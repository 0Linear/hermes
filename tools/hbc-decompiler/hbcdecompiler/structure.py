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
    If,
    Jump,
    Lit,
    Logical,
    Loop,
    Name,
    Return,
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

    def dup(self, n):
        b = self.blocks[n]
        return [copy.copy(s) for s in b.stmts] + [copy.copy(b.term)]

    # ---- sequences -------------------------------------------------------
    def seq(self, n, ctx, first=False):
        out = []
        blocks = self.blocks
        while n is not None:
            if not first:
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
                raise Unstructurable("jump out of region to B%d@%d" % (n, self.blocks[n].start))
            b = blocks[n]
            if not first and len(b.handlers) > len(ctx.open):
                if b.handlers[: len(ctx.open)] != ctx.open:
                    raise Unstructurable("mismatched try nesting")
                h = b.handlers[len(ctx.open)]
                stmt, n = self.emit_try(n, h, ctx)
                out.append(stmt)
                continue
            if b.handlers[: len(ctx.open)] != ctx.open[: len(b.handlers)] or len(
                b.handlers
            ) < len(ctx.open):
                raise Unstructurable("block outside of open try")
            if not first and n in self.g.loops and n not in ctx.active_loops:
                stmt, n = self.emit_loop(n, ctx)
                out.append(stmt)
                continue
            first = False
            if n in self.emitted:
                if self.dupable(n, ctx):
                    out.extend(self.dup(n))
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
        inner = ctx.but(follow=follow)
        then = self.seq(a, inner) if a != follow else []
        els = self.seq(b, inner) if b != follow else []
        return If(cond, then, els), follow

    def emit_loop(self, h, ctx):
        body = self.g.loops[h] & ctx.region
        follow = self.loop_follow(h, body, ctx)
        node = Loop([], self.new_label())
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
        ht = blocks[h].term
        if isinstance(ht, Branch):
            outs = [s for s in (ht.t, ht.f) if s not in body]
            if len(outs) == 1:
                return outs[0]
        # Prefer an exit that is not a small terminal block.
        cand = [e for e in exits if not self.dupable(e, ctx) or e == ctx.follow]
        if ctx.follow in exits:
            return ctx.follow
        for br in reversed(ctx.breakables):
            if br.brk in exits:
                return br.brk
        if cand:
            return max(cand, key=lambda k: self.g.rpo_index.get(k, 0))
        return exits[0]

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
        body = self.seq(
            n, ctx.but(region=region, follow=follow, open=ctx.open + [h], fallthrough=None)
        )
        hb = blocks[h]
        handler = self.seq(
            h, ctx.but(region=ctx.region | hregion, follow=follow, fallthrough=None)
        )
        return Try(body, "ex", handler), follow

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


def _replace_caught(stmts, name):
    def fn(x):
        return Name(name, "catch") if isinstance(x, CaughtValue) else x

    for s in walk_stmts(stmts):
        map_stmt_exprs(s, lambda e: transform(e, fn))
        if isinstance(s, Switch):
            s.cases = [([transform(c, fn) if c is not None else None for c in l], b) for l, b in s.cases]


def structure(blocks):
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
