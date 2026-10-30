# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Control flow structuring: turn a CFG of basic blocks into structured
JavaScript statements (if/else, loops, switch, try/catch, break/continue).

If a function's CFG cannot be expressed with these constructs, the function
is emitted as an equivalent `for (;;) switch (_pc)` dispatch loop, which is
always correct.
"""

import copy
import os
import sys

from .dataflow import compute_edges
from .jsast import (
    Assign,
    Branch,
    Break,
    Comment,
    Continue,
    ExprStmt,
    FuncExpr,
    If,
    Jump,
    Labeled,
    Lit,
    Logical,
    Loop,
    Name,
    Reg,
    Return,
    Seq,
    SetReg,
    Switch,
    SwitchTerm,
    Throw,
    Try,
    Unreachable,
    VarDecl,
    map_stmt_exprs,
    negate,
    stmt_exprs,
    transform,
    walk_expr,
    walk_stmts,
)
from .lifter import CaughtValue


class Unstructurable(Exception):
    pass


# ---------------------------------------------------------------------------
# Graph utilities
# ---------------------------------------------------------------------------


def all_succs(b):
    return list(b.succs) + [h for h in b.handlers if h not in b.succs]


def reverse_postorder(blocks, entry, succ_fn):
    seen = set()
    order = []
    stack = [(entry, iter(succ_fn(blocks[entry])))]
    seen.add(entry)
    while stack:
        n, it = stack[-1]
        for s in it:
            if s not in seen:
                seen.add(s)
                stack.append((s, iter(succ_fn(blocks[s]))))
                break
        else:
            stack.pop()
            order.append(n)
    order.reverse()
    return order


def dominators(nodes, entry, preds):
    """Cooper/Harvey/Kennedy. nodes in RPO. Returns idom dict."""
    index = {n: i for i, n in enumerate(nodes)}
    idom = {entry: entry}

    def intersect(a, b):
        while a != b:
            while index[a] > index[b]:
                a = idom[a]
            while index[b] > index[a]:
                b = idom[b]
        return a

    changed = True
    while changed:
        changed = False
        for n in nodes[1:]:
            new = None
            for p in preds(n):
                if p in idom and p in index:
                    new = p if new is None else intersect(p, new)
            if new is not None and idom.get(n) != new:
                idom[n] = new
                changed = True
    return idom


def dominates(idom, a, b):
    """True if a dominates b."""
    while True:
        if a == b:
            return True
        p = idom.get(b)
        if p is None or p == b:
            return False
        b = p


class Graph:
    def __init__(self, blocks):
        self.blocks = blocks
        self.rpo = reverse_postorder(blocks, 0, all_succs)
        self.reach = set(self.rpo)
        self.rpo_index = {n: i for i, n in enumerate(self.rpo)}
        all_preds = {n: [] for n in self.reach}
        for n in self.rpo:
            for s in all_succs(blocks[n]):
                if s in self.reach:
                    all_preds[s].append(n)
        self.all_preds = all_preds
        self.idom = dominators(self.rpo, 0, lambda n: all_preds[n])
        self._postdom()
        self._loops()

    def _postdom(self):
        EXIT = -1
        blocks = self.blocks
        rsucc = {EXIT: []}
        for n in self.reach:
            rsucc.setdefault(n, [])
        for n in self.reach:
            b = blocks[n]
            ss = [s for s in b.succs if s in self.reach]
            if not ss:
                rsucc[EXIT].append(n)
            for s in ss:
                rsucc[s].append(n)
        # RPO of the reverse graph from EXIT.
        seen = {EXIT}
        order = []
        stack = [(EXIT, iter(rsucc[EXIT]))]
        while stack:
            n, it = stack[-1]
            for s in it:
                if s not in seen:
                    seen.add(s)
                    stack.append((s, iter(rsucc[s])))
                    break
            else:
                stack.pop()
                order.append(n)
        order.reverse()
        rpreds = {n: [] for n in seen}
        for n in seen:
            for s in rsucc[n]:
                if s in seen:
                    rpreds[s].append(n)

        # In the reverse graph, preds of n are the successors of n.
        def preds(n):
            if n == EXIT:
                return []
            b = blocks[n]
            ss = [s for s in b.succs if s in seen]
            if not [s for s in b.succs if s in self.reach]:
                return [EXIT]
            return ss

        self.ipdom = dominators(order, EXIT, preds)
        self.EXIT = EXIT

    def _loops(self):
        self.loops = {}
        blocks = self.blocks
        for n in self.rpo:
            for s in blocks[n].succs:
                if s not in self.reach:
                    continue
                if self.rpo_index[s] <= self.rpo_index[n]:
                    if not dominates(self.idom, s, n):
                        raise Unstructurable("irreducible control flow")
                    body = self.loops.setdefault(s, {s})
                    stack = [n]
                    while stack:
                        x = stack.pop()
                        if x in body:
                            continue
                        body.add(x)
                        stack.extend(p for p in self.all_preds[x])

    def post_dominator(self, n):
        p = self.ipdom.get(n)
        if p is None or p == self.EXIT:
            return None
        return p


# ---------------------------------------------------------------------------
# Short-circuit condition merging
# ---------------------------------------------------------------------------


def _truthiness(e):
    """Static truthiness of a branch condition, or None if unknown."""
    from .jsast import EMPTY, UNDEFINED, BigIntValue, Unary

    if isinstance(e, Unary) and e.op == "!":
        t = _truthiness(e.e)
        return None if t is None else not t
    if not isinstance(e, Lit):
        return None
    v = e.v
    if v is None or v is UNDEFINED or v is EMPTY:
        return False
    if isinstance(v, bool):
        return v
    if isinstance(v, str):
        return v != ""
    if isinstance(v, BigIntValue):
        return v.v != 0
    if isinstance(v, (int, float)):
        return not (v == 0 or v != v)
    return None


def fold_constant_branches(blocks):
    changed = False
    for b in blocks:
        t = b.term
        if isinstance(t, Branch):
            tv = _truthiness(t.cond)
            if tv is not None:
                b.term = Jump(t.t if tv else t.f)
                changed = True
            elif t.t == t.f:
                if t.cond.pure:
                    b.term = Jump(t.t)
                else:
                    b.stmts.append(ExprStmt(t.cond))
                    b.term = Jump(t.t)
                changed = True
    compute_edges(blocks)
    reach = set(reverse_postorder(blocks, 0, all_succs)) if blocks else set()
    for b in blocks:
        if b.id not in reach and (b.stmts or not isinstance(b.term, Unreachable)):
            b.stmts = []
            b.term = Unreachable()
            b.handlers = []
            changed = True
    if changed:
        compute_edges(blocks)
    return changed


def merge_conditions(blocks):
    """Merge `if (a) goto B else Y; B: if (b) ...` chains into a single
    branch on `a && b` / `a || b` when B is otherwise empty."""
    compute_edges(blocks)
    changed = True
    while changed:
        changed = False
        for a in blocks:
            t = a.term
            if not isinstance(t, Branch) or t.t == t.f:
                continue
            for which in ("t", "f"):
                bid = getattr(t, which)
                other = t.f if which == "t" else t.t
                if bid == a.id:
                    continue
                b = blocks[bid]
                if b.stmts or len(b.preds) != 1 or b.handlers != a.handlers:
                    continue
                bt = b.term
                if not isinstance(bt, Branch) or bid in (bt.t, bt.f):
                    continue
                if bt.t == other:
                    # a ? b : other ; b ? other : q
                    cb, q = bt.cond, bt.f
                    if which == "t":
                        # if (a && !b) q else other  ==  if (!a || b) other else q
                        newc = Logical("||", negate(t.cond), cb)
                        a.term = Branch(newc, other, q)
                    else:
                        # if (!a && b) other else q  -> if (a || b)?
                        # a false -> b ; b true -> other ; a true -> other
                        newc = Logical("||", t.cond, cb)
                        a.term = Branch(newc, other, q)
                elif bt.f == other:
                    cb, p = bt.cond, bt.t
                    if which == "t":
                        newc = Logical("&&", t.cond, cb)
                        a.term = Branch(newc, p, other)
                    else:
                        # a true -> other ; a false -> b ; b true -> p ; b false -> other
                        newc = Logical("&&", negate(t.cond), cb)
                        a.term = Branch(newc, p, other)
                else:
                    continue
                b.term = Unreachable()
                b.stmts = []
                compute_edges(blocks)
                changed = True
                break


# ---------------------------------------------------------------------------
# Structurer
# ---------------------------------------------------------------------------


class Ctx:
    __slots__ = ("region", "follow", "breakables", "open", "fallthrough", "active_loops")

    def __init__(self, region, follow, breakables, open_, fallthrough, active_loops):
        self.region = region
        self.follow = follow
        self.breakables = breakables
        self.open = open_
        self.fallthrough = fallthrough
        self.active_loops = active_loops

    def but(self, **kw):
        c = Ctx(
            self.region,
            self.follow,
            self.breakables,
            self.open,
            self.fallthrough,
            self.active_loops,
        )
        for k, v in kw.items():
            setattr(c, k, v)
        return c


class Breakable:
    __slots__ = ("kind", "brk", "cont", "node")

    def __init__(self, kind, brk, cont, node):
        self.kind = kind
        self.brk = brk
        self.cont = cont
        self.node = node


class Structurer:
    def __init__(self, blocks, label_prefix="L"):
        self.blocks = blocks
        self.g = Graph(blocks)
        self.emitted = set()
        self.dup_budget = 32
        self.retry_budget = 64
        self.copying = frozenset()
        self.label_counter = 0
        self.regions = {}
        for b in blocks:
            for h in b.handlers:
                self.regions.setdefault(h, set()).add(b.id)

    def new_label(self):
        self.label_counter += 1
        return "loop%d" % self.label_counter

    def run(self):
        ctx = Ctx(set(self.g.reach), None, [], [], None, frozenset())
        return self.seq(0, ctx)

    # ---- helpers ---------------------------------------------------------
    def resolve_jump(self, n, ctx):
        if n == ctx.fallthrough:
            return "fall"
        innermost_loop = True
        innermost = True
        for br in reversed(ctx.breakables):
            if br.kind == "block":
                if n == br.brk:
                    br.node.used_label = True
                    return Break(br.node.label)
                continue
            if br.kind == "loop" and n == br.cont:
                if not innermost_loop:
                    br.node.used_label = True
                    return Continue(br.node.label)
                return Continue(None)
            if n == br.brk:
                if not innermost:
                    br.node.used_label = True
                    return Break(br.node.label)
                return Break(None)
            if br.kind == "loop":
                innermost_loop = False
            innermost = False
        return None

    def dupable(self, n, ctx):
        b = self.blocks[n]
        if not isinstance(b.term, (Return, Throw)):
            return False
        if len(b.stmts) > 4:
            return False
        for s in b.stmts + [b.term]:
            if isinstance(s, VarDecl):
                return False
            for e in stmt_exprs(s):
                if any(isinstance(x, CaughtValue) for x in walk_expr(e)):
                    return False
        if b.handlers != ctx.open:
            # Only copy code into a different try nesting if it cannot throw.
            if not isinstance(b.term, Return):
                return False
            for s in b.stmts:
                if not (isinstance(s, SetReg) and s.value.pure):
                    return False
            if b.term.e is not None and not b.term.e.pure:
                return False
        return True

    def terminal_subgraph(self, n, ctx):
        """If every path from n reaches a return/throw within a small acyclic
        sub-graph with the same try nesting, return its node set."""
        blocks = self.blocks
        nodes = set()
        order = []
        stmts = 0
        state = {}

        def visit(x):
            nonlocal stmts
            if state.get(x) == 1:
                return False  # cycle
            if state.get(x) == 2:
                return True
            b = blocks[x]
            if x in self.g.loops:
                return False
            if b.handlers != ctx.open:
                # Copying into a different try nesting is only safe for code
                # that cannot throw.
                if not all(isinstance(st, SetReg) and st.value.pure for st in b.stmts):
                    return False
                t = b.term
                if not (
                    (isinstance(t, Return) and (t.e is None or t.e.pure))
                    or isinstance(t, Jump)
                ):
                    return False
            if isinstance(b.term, (Unreachable, SwitchTerm)):
                return False
            for st in b.stmts:
                if isinstance(st, VarDecl):
                    return False
                for e in stmt_exprs(st):
                    if any(isinstance(y, (CaughtValue, FuncExpr)) for y in walk_expr(e)):
                        return False
            state[x] = 1
            nodes.add(x)
            stmts += len(b.stmts) + 1
            if len(nodes) > 8 or stmts > 12:
                return False
            for sx in b.succs:
                if not visit(sx):
                    return False
            state[x] = 2
            order.append(x)
            return True

        if not visit(n):
            return None
        return nodes

    def emit_copy(self, n, nodes, ctx):
        saved = self.emitted
        saved_copying = self.copying
        self.emitted = set(saved) - nodes
        self.copying = saved_copying | {x for x in nodes if self.blocks[x].handlers != ctx.open}
        try:
            out = self.seq(n, ctx.but(region=ctx.region | nodes, follow=None, fallthrough=None))
        finally:
            self.emitted = saved
            self.copying = saved_copying
        return _clone(out)

    def tail_dupable(self, n, ctx):
        """Small straight-line blocks may be duplicated on each path that
        reaches them (e.g. switch fall-through lowered to if-chains)."""
        b = self.blocks[n]
        if not isinstance(b.term, Jump) or len(b.stmts) > 3:
            return False
        if b.handlers != ctx.open or n in self.g.loops:
            return False
        if self.dup_budget <= 0:
            return False
        for st in b.stmts:
            if not isinstance(st, (SetReg, ExprStmt)):
                return False
            for e in stmt_exprs(st):
                if any(isinstance(x, (CaughtValue, FuncExpr)) for x in walk_expr(e)):
                    return False
        self.dup_budget -= 1
        return True

    def dup(self, n):
        b = self.blocks[n]
        return [copy.copy(s) for s in b.stmts] + [copy.copy(b.term)]

    # ---- sequences -------------------------------------------------------
    def seq(self, n, ctx, first=False, entry=False):
        """Emit code starting at block n. `first` marks n as the header of the
        loop being emitted; `entry` skips jump resolution for n."""
        out = []
        blocks = self.blocks
        while n is not None:
            if not first and not entry:
                if n == ctx.follow:
                    break
                j = self.resolve_jump(n, ctx)
                if j == "fall":
                    break
                if j is not None:
                    out.append(j)
                    break
            if n not in ctx.region:
                if self.dupable(n, ctx):
                    out.extend(self.dup(n))
                    break
                sub = self.terminal_subgraph(n, ctx) if self.dup_budget > 0 else None
                if sub is not None:
                    self.dup_budget -= 1
                    out.extend(self.emit_copy(n, sub, ctx))
                    break
                raise Unstructurable("jump out of region to B%d@%d" % (n, self.blocks[n].start))
            entry = False
            b = blocks[n]
            want_try = len(b.handlers) > len(ctx.open)
            want_loop = not first and n in self.g.loops and n not in ctx.active_loops
            if want_try and want_loop:
                h = b.handlers[len(ctx.open)]
                if not self.g.loops[n] <= self.regions.get(h, set()):
                    want_try = False
            if want_try:
                if b.handlers[: len(ctx.open)] != ctx.open:
                    raise Unstructurable("mismatched try nesting")
                h = b.handlers[len(ctx.open)]
                stmt, n = self.emit_try(n, h, ctx)
                out.append(stmt)
                continue
            if want_loop:
                stmt, n = self.emit_loop(n, ctx)
                out.append(stmt)
                continue
            if n not in self.copying and (
                b.handlers[: len(ctx.open)] != ctx.open[: len(b.handlers)]
                or len(b.handlers) < len(ctx.open)
            ):
                raise Unstructurable("block outside of open try")
            first = False
            if n in self.emitted:
                if self.dupable(n, ctx):
                    out.extend(self.dup(n))
                    break
                if self.tail_dupable(n, ctx):
                    out.extend(copy.copy(st) for st in b.stmts)
                    n = b.term.target
                    continue
                sub = self.terminal_subgraph(n, ctx) if self.dup_budget > 0 else None
                if sub is not None:
                    self.dup_budget -= 1
                    out.extend(self.emit_copy(n, sub, ctx))
                    break
                raise Unstructurable("block B%d emitted twice" % n)
            self.emitted.add(n)
            out.extend(b.stmts)
            t = b.term
            if isinstance(t, (Return, Throw)):
                out.append(t)
                break
            if isinstance(t, Unreachable):
                break
            if isinstance(t, Jump):
                n = t.target
                continue
            if isinstance(t, Branch):
                stmt, n = self.emit_if(n, t, ctx)
                out.append(stmt)
                continue
            if isinstance(t, SwitchTerm):
                stmt, n = self.emit_switch(n, t, ctx)
                out.append(stmt)
                continue
            raise Unstructurable("unknown terminator")
        return out

    def clip_follow(self, f, ctx):
        if f is None:
            return None
        if f == ctx.follow:
            return f
        if f not in ctx.region:
            return None
        return f

    def emit_if(self, n, t, ctx):
        if self.retry_budget <= 0:
            return self.emit_plain_if(n, t, ctx)
        snap = (set(self.emitted), self.dup_budget, self.label_counter)
        try:
            return self.emit_plain_if(n, t, ctx)
        except Unstructurable:
            if self.retry_budget <= 0:
                raise
            self.retry_budget -= 1
            self.emitted, self.dup_budget, self.label_counter = snap[0], snap[1], snap[2]
            res = self.emit_join_if(n, t, ctx)
            if res is None:
                raise
            return res

    def _reach(self, start, n, stop, ctx):
        """Nodes reachable from start (dominated by n) without passing stop
        or enclosing jump targets."""
        targets = {stop, n}
        for br in ctx.breakables:
            targets.add(br.brk)
            if br.cont is not None:
                targets.add(br.cont)
        seen = set()
        stack = [start]
        while stack:
            x = stack.pop()
            if x in seen or x in targets or x not in ctx.region:
                continue
            if not dominates(self.g.idom, n, x):
                continue
            seen.add(x)
            stack.extend(self.blocks[x].succs)
        return seen

    def emit_join_if(self, n, t, ctx):
        """if/else whose branches re-join at a node X other than the
        post-dominator F:  F: { if (c) {...} else {... break F; ...} X... }"""
        follow = self.clip_follow(self.g.post_dominator(n), ctx)
        ra = self._reach(t.t, n, follow, ctx)
        rb = self._reach(t.f, n, follow, ctx)
        joins = (ra & rb) - set(self.g.loops)
        if not joins:
            return None
        x = min(joins, key=lambda k: self.g.rpo_index.get(k, 0))
        if self.blocks[t.f].start < self.blocks[t.t].start:
            cond, a, b = negate(t.cond), t.f, t.t
        else:
            cond, a, b = t.cond, t.t, t.f
        brs = ctx.breakables
        node = None
        if follow is not None:
            node = Labeled(self.new_label().replace("loop", "blk"), [])
            brs = brs + [Breakable("block", follow, None, node)]
        inner = ctx.but(follow=x, breakables=brs)
        then = self.seq(a, inner) if a != x else []
        els = self.seq(b, inner) if b != x else []
        stmt = If(cond, then, els)
        if node is None:
            return stmt, x
        rest = self.seq(x, ctx.but(follow=follow, breakables=brs))
        node.body = [stmt] + rest
        return node, follow

    def emit_plain_if(self, n, t, ctx):
        follow = self.clip_follow(self.g.post_dominator(n), ctx)
        # Put the fall-through (lexically next) block in the `then` branch, as
        # source `if` statements usually jump over the then-block.
        if t.t == follow:
            cond, a, b = negate(t.cond), t.f, t.t
        elif t.f == follow:
            cond, a, b = t.cond, t.t, t.f
        elif self.blocks[t.f].start < self.blocks[t.t].start:
            cond, a, b = negate(t.cond), t.f, t.t
        else:
            cond, a, b = t.cond, t.t, t.f
        inner = ctx.but(follow=follow if follow is not None else ctx.follow)
        then = self.seq(a, inner) if a != follow else []
        els = self.seq(b, inner) if b != follow else []
        return If(cond, then, els), follow

    def latch_block(self, h, body, ctx):
        """A single latch block (other than the header) reached from several
        places is the target of `continue`; return it if its code can be
        expressed as a for-loop update / do-while condition."""
        blocks = self.blocks
        latches = [p for p in self.g.all_preds[h] if p in body and h in blocks[p].succs]
        if len(latches) != 1 or latches[0] == h:
            return None
        L = latches[0]
        bl = blocks[L]
        if len(bl.preds) < 2 or bl.handlers != ctx.open:
            return None
        for st in bl.stmts:
            if not isinstance(st, (SetReg, ExprStmt)):
                return None
        t = bl.term
        if isinstance(t, Jump):
            return L
        if isinstance(t, Branch) and h in (t.t, t.f) and t.t != t.f:
            return L
        return None

    def loop_region(self, h, body, follow, ctx):
        """The loop body plus exit paths that only the loop can reach (e.g.
        a `return` inside the loop), which are emitted inside the loop."""
        blocks = self.blocks
        after = set()
        if follow is not None:
            stack = [follow]
            while stack:
                x = stack.pop()
                if x in after:
                    continue
                after.add(x)
                if x in ctx.region and x != h:
                    stack.extend(all_succs(blocks[x]))
        ext = set()
        stack = [s for x in body for s in all_succs(blocks[x]) if s not in body]
        while stack:
            x = stack.pop()
            if x in ext or x in body or x in after or x not in self.g.reach:
                continue
            if not dominates(self.g.idom, h, x):
                continue
            ext.add(x)
            stack.extend(all_succs(blocks[x]))
        return body | ext

    def emit_loop(self, h, ctx):
        body = self.g.loops[h] & ctx.region
        follow = self.loop_follow(h, body, ctx)
        body = self.loop_region(h, body, follow, ctx) & ctx.region
        node = Loop([], self.new_label())
        latch = self.latch_block(h, body, ctx)
        if latch is not None:
            lt = self.blocks[latch].term
            if isinstance(lt, Branch):
                other = lt.f if lt.t == h else lt.t
                if other != follow:
                    latch = None
        if latch is not None:
            # Prefer plain structuring; fall back to treating the latch as
            # the `continue` target when that fails.
            snap = (set(self.emitted), self.dup_budget, self.label_counter)
            try:
                return self.emit_plain_loop(h, body, follow, node, ctx)
            except Unstructurable:
                self.emitted, self.dup_budget, self.label_counter = (
                    snap[0],
                    snap[1],
                    snap[2],
                )
                node = Loop([], self.new_label())
                return self.emit_latch_loop(h, body, follow, latch, node, ctx)
        return self.emit_plain_loop(h, body, follow, node, ctx)

    def emit_plain_loop(self, h, body, follow, node, ctx):
        br = Breakable("loop", follow, h, node)
        inner = ctx.but(
            region=body,
            follow=None,
            breakables=ctx.breakables + [br],
            fallthrough=None,
            active_loops=ctx.active_loops | {h},
        )
        node.body = self.seq(h, inner, first=True)
        if follow is not None and follow not in ctx.region and follow != ctx.follow:
            # The exit is outside our region; let the caller resolve it.
            pass
        return node, follow

    def emit_latch_loop(self, h, body, follow, latch, node, ctx):
        bl = self.blocks[latch]
        self.emitted.add(latch)
        br = Breakable("loop", follow, latch, node)
        inner = ctx.but(
            region=body - {latch},
            follow=None,
            breakables=ctx.breakables + [br],
            fallthrough=None,
            active_loops=ctx.active_loops | {h},
        )
        node.body = self.seq(h, inner, first=True)
        exprs = []
        for st in bl.stmts:
            if isinstance(st, SetReg):
                exprs.append(Assign(Reg(st.reg), st.value))
            else:
                exprs.append(st.e)
        t = bl.term
        if isinstance(t, Jump):
            node.kind = "for"
            node.update = (exprs[0] if len(exprs) == 1 else Seq(exprs)) if exprs else None
        else:
            c = t.cond if t.t == h else negate(t.cond)
            node.kind = "dowhile"
            node.cond = Seq(exprs + [c]) if exprs else c
        return node, follow

    def loop_follow(self, h, body, ctx):
        blocks = self.blocks
        exits = []
        for x in sorted(body, key=lambda k: self.g.rpo_index.get(k, 0)):
            for s in blocks[x].succs:
                if s not in body and s not in exits:
                    exits.append(s)
        if not exits:
            return None
        if len(exits) == 1:
            return exits[0]
        jump_targets = set()
        for br in ctx.breakables:
            jump_targets.add(br.brk)
            if br.cont is not None:
                jump_targets.add(br.cont)
        if ctx.follow in exits:
            return ctx.follow
        local = [e for e in exits if e not in jump_targets]
        if len(local) == 1:
            return local[0]
        if not local:
            for br in reversed(ctx.breakables):
                if br.brk in exits:
                    return br.brk
            return exits[0]
        ht = blocks[h].term
        if isinstance(ht, Branch):
            outs = [s for s in (ht.t, ht.f) if s not in body and s in local]
            if len(outs) == 1:
                return outs[0]
        # The exit of a latch (back edge source) condition, as in do-while.
        for p in self.g.all_preds[h]:
            if p in body and h in blocks[p].succs:
                pt = blocks[p].term
                if isinstance(pt, Branch):
                    outs = [s for s in (pt.t, pt.f) if s not in body and s in local]
                    if len(outs) == 1:
                        return outs[0]
        # Prefer an exit that is not a small terminal block.
        cand = [e for e in local if not self.dupable(e, ctx)]
        if cand:
            return max(cand, key=lambda k: self.g.rpo_index.get(k, 0))
        return local[0]

    def emit_try(self, n, h, ctx):
        blocks = self.blocks
        region = self.regions.get(h, set()) & ctx.region
        exits = set()
        for x in region:
            for s in blocks[x].succs:
                if s not in region:
                    exits.add(s)
        hcover = blocks[h].handlers
        hregion = {
            x
            for x in self.g.reach
            if x not in region
            and blocks[x].handlers[: len(hcover)] == hcover
            and dominates(self.g.idom, h, x)
        }
        hexits = set()
        for x in hregion:
            for s in blocks[x].succs:
                if s not in hregion:
                    hexits.add(s)
        cands = (exits | hexits) - region - hregion - {h}
        jump_targets = set()
        for br in ctx.breakables:
            jump_targets.add(br.brk)
            if br.cont is not None:
                jump_targets.add(br.cont)
        if ctx.follow in cands:
            follow = ctx.follow
        else:
            c = [x for x in cands if x not in jump_targets]
            nondup = [x for x in c if not self.dupable(x, ctx)]
            if nondup:
                c = nondup
            if len(c) == 1:
                follow = c[0]
            elif not c:
                follow = None
            else:
                both = [x for x in c if x in exits and x in hexits]
                pick = both or [x for x in c if x in exits] or c
                follow = min(pick, key=lambda k: self.g.rpo_index.get(k, 0))
        others = []
        if follow is not None and follow != ctx.follow:
            inner_open = ctx.but(open=ctx.open + [h])
            others = [
                x
                for x in cands
                if x != follow
                and x not in jump_targets
                and x != ctx.follow
                and not self.dupable(x, inner_open)
            ]
            others.sort(key=lambda k: self.g.rpo_index.get(k, 0))
        if not others:
            body = self.seq(
                n,
                ctx.but(region=region, follow=follow, open=ctx.open + [h], fallthrough=None),
                entry=True,
            )
            handler = self.seq(
                h, ctx.but(region=ctx.region | hregion, follow=follow, fallthrough=None)
            )
            return Try(body, "ex", handler), follow
        # Several exits: nest labeled blocks so that each exit is a forward
        # `break label`.
        #   F: { Xk: { ... X1: { try {...} catch {...} } X1-code ... } Xk-code }
        node_f = Labeled(self.new_label().replace("loop", "blk"), [])
        br_f = Breakable("block", follow, None, node_f)
        nodes = []
        brs = []
        for x in others:
            nd = Labeled(self.new_label().replace("loop", "blk"), [])
            nodes.append(nd)
            brs.append(Breakable("block", x, None, nd))
        # Innermost breakable is X1 (others[0]).
        inner_brs = ctx.breakables + [br_f] + list(reversed(brs))
        body = self.seq(
            n,
            ctx.but(
                region=region,
                follow=None,
                open=ctx.open + [h],
                fallthrough=None,
                breakables=inner_brs,
            ),
            entry=True,
        )
        handler = self.seq(
            h,
            ctx.but(
                region=ctx.region | hregion,
                follow=None,
                fallthrough=None,
                breakables=inner_brs,
            ),
        )
        cur = [Try(body, "ex", handler)]
        for i, x in enumerate(others):
            nodes[i].body = cur
            outer_brs = ctx.breakables + [br_f] + list(reversed(brs[i + 1 :]))
            code = self.seq(
                x,
                ctx.but(follow=None, fallthrough=None, breakables=outer_brs),
            )
            cur = [nodes[i]] + code
        node_f.body = cur
        return node_f, follow

    def emit_switch(self, n, t, ctx):
        blocks = self.blocks
        follow = self.clip_follow(self.g.post_dominator(n), ctx)
        targets = []
        for _, tgt in t.cases:
            if tgt not in targets:
                targets.append(tgt)
        if t.default not in targets:
            targets.append(t.default)
        targets.sort(key=lambda k: blocks[k].start)
        if follow in targets and follow != t.default:
            follow = None
        node = Switch(t.disc, [], self.new_label().replace("loop", "sw"))
        br = Breakable("switch", follow, None, node)
        cases = []
        bodies_targets = [x for x in targets if x != follow]
        for i, tgt in enumerate(bodies_targets):
            labels = [c for c, x in t.cases if x == tgt]
            if tgt == t.default:
                labels.append(None)
            nxt = bodies_targets[i + 1] if i + 1 < len(bodies_targets) else None
            inner = ctx.but(follow=None, breakables=ctx.breakables + [br], fallthrough=nxt)
            body = self.seq(tgt, inner)
            cases.append((labels, body))
        node.cases = cases
        return node, follow


# ---------------------------------------------------------------------------
# Dispatcher fallback
# ---------------------------------------------------------------------------


def dispatcher(blocks):
    """Emit the function as a `_pc` driven state machine."""
    g_reach = reverse_postorder(blocks, 0, all_succs)
    reach = set(g_reach)
    pc = Name("_pc", "local")
    caught = Name("_ex", "local")
    has_handlers = any(b.handlers for b in blocks if b.id in reach)

    def goto(t):
        return [ExprStmt(Assign(pc, Lit(t))), Continue(None)]

    cases = []
    for bid in sorted(reach):
        b = blocks[bid]
        body = []
        body.extend(b.stmts)
        t = b.term
        if isinstance(t, (Return, Throw)):
            body.append(t)
        elif isinstance(t, Jump):
            body.extend(goto(t.target))
        elif isinstance(t, Branch):
            body.append(If(t.cond, goto(t.t), []))
            body.extend(goto(t.f))
        elif isinstance(t, SwitchTerm):
            sw_cases = []
            for c, tgt in t.cases:
                sw_cases.append(([c], goto(tgt)))
            sw_cases.append(([None], goto(t.default)))
            body.append(Switch(t.disc, sw_cases, None))
        elif isinstance(t, Unreachable):
            body.append(Throw(_new_error("unreachable")))
        cases.append(([Lit(bid)], body))
    sw = Switch(pc, cases, None)
    loop_body = [sw]
    if has_handlers:
        hcases = {}
        for bid in sorted(reach):
            h = blocks[bid].handler
            if h is not None:
                hcases.setdefault(h, []).append(bid)
        hsw = []
        for h, bids in sorted(hcases.items()):
            hsw.append(
                (
                    [Lit(x) for x in bids],
                    [ExprStmt(Assign(caught, Name("ex", "catch")))] + goto(h),
                )
            )
        handler = [Switch(pc, hsw, None), Throw(Name("ex", "catch"))]
        loop_body = [Try([sw], "ex", handler)]
    decl = VarDecl("let", ["_pc = 0"] + (["_ex"] if has_handlers else []))
    loop = Loop(loop_body, None)
    _replace_caught(cases_bodies(cases), "_ex")
    return [Comment("control flow could not be structured; using a dispatch loop"), decl, loop]


def cases_bodies(cases):
    out = []
    for _, b in cases:
        out.extend(b)
    return out


def _new_error(msg):
    from .jsast import New

    return New(Name("Error", "builtin"), [Lit(msg)])


def _clone(stmts):
    out = []
    for st in stmts:
        st = copy.copy(st)
        if isinstance(st, If):
            st.then, st.els = _clone(st.then), _clone(st.els)
        elif isinstance(st, (Loop, Labeled)):
            st.body = _clone(st.body)
        elif isinstance(st, Switch):
            st.cases = [(l, _clone(b)) for l, b in st.cases]
        elif isinstance(st, Try):
            st.body, st.handler = _clone(st.body), _clone(st.handler)
        out.append(st)
    return out


def _replace_caught(stmts, name):
    def fn(x):
        return Name(name, "catch") if isinstance(x, CaughtValue) else x

    for s in walk_stmts(stmts):
        map_stmt_exprs(s, lambda e: transform(e, fn))
        if isinstance(s, Switch):
            s.cases = [([transform(c, fn) if c is not None else None for c in l], b) for l, b in s.cases]


def structure(blocks):
    if not blocks:
        return [], False
    fold_constant_branches(blocks)
    merge_conditions(blocks)
    try:
        s = Structurer(blocks)
        body = s.run()
        _replace_caught(body, "ex")
        return body, False
    except Unstructurable as e:
        if os.environ.get("HBC_DEBUG_STRUCT"):
            sys.stderr.write("unstructurable: %s\n" % e)
        return dispatcher(blocks), True
    except RecursionError:
        return dispatcher(blocks), True
