# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Register dataflow and expression reconstruction on the flat IR.

The passes here turn the one-instruction-per-statement register IR into
expression trees: copy propagation, constant propagation, single-use
temporary inlining (respecting evaluation order and side effects), object and
array literal reconstruction, and dead code elimination.
"""

from .jsast import (
    UNDEFINED,
    ArrayLit,
    Assign,
    Binary,
    Branch,
    Call,
    Comment,
    Cond,
    Logical,
    Seq,
    ExprStmt,
    FuncExpr,
    Lit,
    Member,
    Name,
    New,
    ObjectLit,
    Reg,
    SetReg,
    Spread,
    SwitchTerm,
    Unary,
    VarDecl,
    stmt_exprs,
)
from .lifter import (
    CallT,
    CaughtValue,
    CoerceThis,
    ConstructT,
    CreateThis,
    DefineAccessor,
    DefineProp,
    SelectObj,
)

# ---------------------------------------------------------------------------
# Def/use helpers
# ---------------------------------------------------------------------------


def expr_regs(e, out):
    """Append registers read by e, in evaluation order."""
    if isinstance(e, Reg):
        out.append(e.n)
        return out
    for c in e.children():
        expr_regs(c, out)
    return out


def stmt_uses(s):
    out = []
    for e in stmt_exprs(s):
        expr_regs(e, out)
    return out


def stmt_def(s):
    return s.reg if isinstance(s, SetReg) else None


def stmt_is_pure(s):
    if isinstance(s, SetReg):
        return s.value.pure
    return isinstance(s, (VarDecl, Comment))


def block_succs(b):
    t = b.term
    if isinstance(t, Branch):
        return [x for x in (t.t, t.f) if x is not None]
    if isinstance(t, SwitchTerm):
        return [x for _, x in t.cases] + [t.default]
    if hasattr(t, "target"):
        return [t.target]
    return []


def compute_edges(blocks):
    for b in blocks:
        b.succs = []
        b.preds = []
    for b in blocks:
        seen = set()
        for s in block_succs(b):
            if s not in seen:
                seen.add(s)
                b.succs.append(s)
                blocks[s].preds.append(b.id)


# ---------------------------------------------------------------------------
# Liveness
# ---------------------------------------------------------------------------


def liveness(blocks):
    """Return (live_in, live_out) as lists of sets indexed by block id. The
    live-in set of a block's exception handler is part of its live-out."""
    n = len(blocks)
    use = [set() for _ in range(n)]
    dfn = [set() for _ in range(n)]
    for b in blocks:
        u, d = use[b.id], dfn[b.id]
        for s in b.stmts + [b.term]:
            for r in stmt_uses(s):
                if r not in d:
                    u.add(r)
            r = stmt_def(s)
            if r is not None:
                d.add(r)
    live_in = [set() for _ in range(n)]
    live_out = [set() for _ in range(n)]
    changed = True
    order = list(reversed(range(n)))
    while changed:
        changed = False
        for i in order:
            b = blocks[i]
            out = set()
            for s in b.succs:
                out |= live_in[s]
            for h in b.handlers:
                out |= live_in[h]
            inn = use[i] | (out - dfn[i])
            # A use in a protected block is also live across the whole block.
            for h in b.handlers:
                inn |= live_in[h]
            if out != live_out[i] or inn != live_in[i]:
                live_out[i] = out
                live_in[i] = inn
                changed = True
    return live_in, live_out


def stmt_live_out(b, block_live_out, handler_live):
    """Per-statement live-out sets for block b (stmts + terminator)."""
    stmts = b.stmts + [b.term]
    res = [None] * len(stmts)
    live = set(block_live_out)
    for i in range(len(stmts) - 1, -1, -1):
        res[i] = live | handler_live
        s = stmts[i]
        r = stmt_def(s)
        if r is not None:
            live.discard(r)
        live.update(stmt_uses(s))
    return res


# ---------------------------------------------------------------------------
# Copy propagation (block local)
# ---------------------------------------------------------------------------


def subst_regs(e, mapping):
    """Replace Reg(n) by mapping[n] (an Expr)."""
    if isinstance(e, Reg):
        return mapping.get(e.n, e)
    return e.replace_children(lambda c: subst_regs(c, mapping))


def _map_stmt(s, fn):
    from .jsast import map_stmt_exprs

    map_stmt_exprs(s, fn)
    if isinstance(s, SwitchTerm):
        s.cases = [(fn(c), t) for c, t in s.cases]


def copy_propagate(blocks):
    """Global copy propagation using available-copies dataflow."""
    n = len(blocks)
    if not n:
        return
    # Facts are (dst, src) pairs.
    gen = [None] * n
    killregs = [None] * n
    all_facts = set()
    for b in blocks:
        avail = {}
        kr = set()
        for s in b.stmts:
            r = stmt_def(s)
            if r is None:
                continue
            kr.add(r)
            for k in [k for k, v in avail.items() if k == r or v == r]:
                del avail[k]
            if isinstance(s.value, Reg) and s.value.n != r:
                avail[r] = s.value.n
        gen[b.id] = set(avail.items())
        killregs[b.id] = kr
        all_facts |= gen[b.id]
    preds = [[] for _ in range(n)]
    for b in blocks:
        for s in b.succs:
            preds[s].append(b.id)
    is_handler = set()
    for b in blocks:
        is_handler.update(b.handlers)
    inn = [set() if i == 0 or i in is_handler else set(all_facts) for i in range(n)]
    out = [None] * n

    def transfer(i, x):
        kr = killregs[i]
        return {(d, s) for d, s in x if d not in kr and s not in kr} | gen[i]

    for i in range(n):
        out[i] = transfer(i, inn[i])
    changed = True
    while changed:
        changed = False
        for b in blocks:
            i = b.id
            if i == 0 or i in is_handler or not preds[i]:
                x = set()
            else:
                x = None
                for p in preds[i]:
                    x = set(out[p]) if x is None else (x & out[p])
            if x != inn[i]:
                inn[i] = x
                o = transfer(i, x)
                if o != out[i]:
                    out[i] = o
                changed = True
    for b in blocks:
        copies = dict(inn[b.id])
        new = []
        for s in b.stmts + [b.term]:
            if copies:
                m = {k: Reg(v) for k, v in copies.items()}
                _map_stmt(s, lambda e: subst_regs(e, m))
            r = stmt_def(s)
            if r is not None:
                for k in [k for k, v in copies.items() if k == r or v == r]:
                    del copies[k]
                if isinstance(s.value, Reg):
                    if s.value.n == r:
                        continue
                    copies[r] = s.value.n
            new.append(s)
        b.term = new.pop()
        b.stmts = new


# ---------------------------------------------------------------------------
# Constant propagation (global, reaching definitions)
# ---------------------------------------------------------------------------


def _propagatable(e):
    if isinstance(e, Lit):
        return not (isinstance(e.v, str) and len(e.v) > 64)
    if isinstance(e, Name):
        return e.kind in ("param", "this", "builtin", "globalobj", "helper")
    return False


def constant_propagate(blocks):
    # Only registers with at least one propagatable definition matter.
    interesting = set()
    for b in blocks:
        for s in b.stmts:
            if isinstance(s, SetReg) and _propagatable(s.value):
                interesting.add(s.reg)
    if not interesting:
        return False
    defs = []  # (block id, stmt)
    reg_defs = {}  # reg -> bitmask of def ids
    for b in blocks:
        for s in b.stmts:
            if isinstance(s, SetReg) and s.reg in interesting:
                idx = len(defs)
                defs.append(s)
                reg_defs[s.reg] = reg_defs.get(s.reg, 0) | (1 << idx)
    if not defs:
        return False
    # Entry pseudo definitions.
    entry_bit = {}
    for r in reg_defs:
        idx = len(defs)
        defs.append(None)
        entry_bit[r] = 1 << idx
        reg_defs[r] |= 1 << idx
    n = len(blocks)
    gen = [0] * n
    kill = [0] * n
    alldefs = [0] * n
    di = 0
    for b in blocks:
        g = 0
        k = 0
        a = 0
        for s in b.stmts:
            if isinstance(s, SetReg) and s.reg in interesting:
                bit = 1 << di
                di += 1
                g = (g & ~reg_defs[s.reg]) | bit
                k |= reg_defs[s.reg]
                a |= bit
        gen[b.id], kill[b.id], alldefs[b.id] = g, k, a
    inn = [0] * n
    out = [0] * n
    for r, bit in entry_bit.items():
        inn[0] |= bit
    handler_extra = [0] * n
    order = _rpo_blocks(blocks)
    changed = True
    while changed:
        changed = False
        for b in order:
            i = b.id
            x = inn[i] if i else inn[0]
            for p in b.preds:
                x |= out[p]
            x |= handler_extra[i]
            if i == 0:
                for bit in entry_bit.values():
                    x |= bit
            o = gen[i] | (x & ~kill[i])
            if x != inn[i] or o != out[i]:
                inn[i], out[i] = x, o
                changed = True
            for h in b.handlers:
                v = handler_extra[h] | x | alldefs[i]
                if v != handler_extra[h]:
                    handler_extra[h] = v
                    changed = True
    did = False
    di = 0
    for b in blocks:
        cur = inn[b.id]
        for s in b.stmts + [b.term]:
            uses = set(stmt_uses(s))
            repl = {}
            for r in uses:
                if r not in reg_defs:
                    continue
                reach = cur & reg_defs[r]
                if reach and reach & (reach - 1) == 0:
                    d = defs[reach.bit_length() - 1]
                    if d is not None and _propagatable(d.value):
                        repl[r] = d.value
            if repl:
                _map_stmt(s, lambda e: subst_regs(e, repl))
                did = True
            if isinstance(s, SetReg) and s.reg in reg_defs:
                bit = 1 << di
                di += 1
                cur = (cur & ~reg_defs[s.reg]) | bit
    return did


def _rpo_blocks(blocks):
    seen = set()
    post = []
    for root in [0] + [b.id for b in blocks]:
        if root in seen or root >= len(blocks):
            continue
        seen.add(root)
        stack = [(root, iter(blocks[root].succs + blocks[root].handlers))]
        while stack:
            x, it = stack[-1]
            for y in it:
                if y not in seen:
                    seen.add(y)
                    stack.append((y, iter(blocks[y].succs + blocks[y].handlers)))
                    break
            else:
                stack.pop()
                post.append(blocks[x])
    post.reverse()
    return post


# ---------------------------------------------------------------------------
# Dead code elimination
# ---------------------------------------------------------------------------


def dce(blocks):
    changed_any = False
    while True:
        live_in, live_out = liveness(blocks)
        changed = False
        for b in blocks:
            hl = set()
            for h in b.handlers:
                hl |= live_in[h]
            lo = stmt_live_out(b, live_out[b.id], hl)
            new = []
            for s, l in zip(b.stmts, lo):
                if isinstance(s, SetReg) and s.reg not in l:
                    changed = True
                    if s.value.pure or isinstance(s.value, CaughtValue):
                        continue
                    s = ExprStmt(s.value)
                if isinstance(s, ExprStmt) and s.e.pure:
                    changed = True
                    continue
                new.append(s)
            b.stmts = new
        if not changed:
            return changed_any
        changed_any = True


# ---------------------------------------------------------------------------
# Expression folding (block local)
# ---------------------------------------------------------------------------


def _reg_count(e, n):
    if isinstance(e, Reg):
        return 1 if e.n == n else 0
    return sum(_reg_count(c, n) for c in e.children())


def _replace_one_reg(e, n, repl):
    """Replace the single occurrence of Reg(n) in e by repl."""
    if isinstance(e, Reg):
        return repl if e.n == n else e
    return e.replace_children(lambda c: _replace_one_reg(c, n, repl))


def _defines_any(s, regs):
    r = stmt_def(s)
    return r is not None and r in regs


def _reads(s, n):
    return n in stmt_uses(s)


def fold_blocks(blocks, ctx):
    live_in, live_out = liveness(blocks)
    for b in blocks:
        hl = set()
        for h in b.handlers:
            hl |= live_in[h]
        lo = stmt_live_out(b, live_out[b.id], hl)
        stmts = b.stmts + [b.term]
        out = []
        for s, l in zip(stmts, lo):
            s = _fold_stmt(s, l, hl, out, ctx)
            if s is not None:
                out.append(s)
        b.term = out.pop()
        b.stmts = out


def _fold_stmt(s, live, handler_live, out, ctx):
    """Fold definitions from `out` into statement s. Returns the (possibly
    replaced) statement or None if it was absorbed.

    Every folded expression with side effects is tagged with its original
    position, and a fold is only accepted if the evaluation order of all side
    effects in the resulting statement matches the original order."""
    stamp = {id(st): i for i, st in enumerate(out)}
    origin = {}
    progress = True
    while progress:
        progress = False
        s = _simplify_stmt(s, out, live, ctx)
        if s is None:
            return None
        regs = stmt_uses(s)
        if not regs:
            break
        sdef = stmt_def(s)
        counts = {}
        for n in regs:
            counts[n] = counts.get(n, 0) + 1
        seen = set()
        for n in reversed(regs):
            if n in seen:
                continue
            seen.add(n)
            if counts[n] != 1:
                continue
            if n in handler_live:
                continue
            if n in live and sdef != n:
                continue
            # Find the latest definition of n in out.
            pos = None
            for j in range(len(out) - 1, -1, -1):
                st = out[j]
                if stmt_def(st) == n:
                    pos = j
                    break
                if _reads(st, n):
                    break
            if pos is None:
                continue
            d = out[pos]
            val = d.value
            p = stamp.get(id(d), -1)
            if not val.pure:
                if any(not stmt_is_pure(out[j]) for j in range(pos + 1, len(out))):
                    continue
                if not _order_ok(s, n, p, origin):
                    continue
            vregs = set(expr_regs(val, []))
            if any(_defines_any(out[j], vregs) for j in range(pos + 1, len(out))):
                continue
            # Fold.
            del out[pos]
            if not val.pure:
                origin[id(val)] = p
            _map_into(s, n, val)
            progress = True
            break
    return s


_INF = float("inf")


def _self_effect(e):
    if e.pure:
        return False
    return not isinstance(e, (Logical, Cond, Seq, ObjectLit, ArrayLit))


def _order_ok(s, n, p, origin):
    """Would evaluating a side effect from original position p at the slot of
    Reg(n) in s keep all side effects in their original order?"""
    events = []
    found = [False]

    def walk(e, tag):
        tag = origin.get(id(e), tag)
        if isinstance(e, Reg):
            if e.n == n:
                found[0] = True
                events.append(None)
            return
        for c in e.children():
            walk(c, tag)
        if _self_effect(e):
            events.append(tag)

    for e in stmt_exprs(s):
        walk(e, _INF)
    if not found[0]:
        return False
    before = True
    for ev in events:
        if ev is None:
            before = False
        elif before:
            if not ev < p:
                return False
        elif not ev > p:
            return False
    return True


def _map_into(s, n, val):
    _map_stmt(s, lambda e: _replace_one_reg(e, n, val))


# ---------------------------------------------------------------------------
# Peephole simplifications applied during folding
# ---------------------------------------------------------------------------


def _same(a, b):
    if isinstance(a, Reg) and isinstance(b, Reg):
        return a.n == b.n
    if isinstance(a, Name) and isinstance(b, Name):
        return a.name == b.name and a.pure
    return False


def simplify_expr(e):
    def fn(x):
        if isinstance(x, CallT):
            if isinstance(x.this, Lit) and x.this.v is UNDEFINED:
                return Call(x.callee, x.args)
            if isinstance(x.callee, Member) and _same(x.callee.obj, x.this):
                return Call(x.callee, x.args)
        if isinstance(x, SelectObj) and isinstance(x.ret, ConstructT):
            c = x.ret
            if _same(c.this, x.this):
                if isinstance(c.this, CreateThis) or isinstance(c.this, Reg):
                    return x
        if isinstance(x, SelectObj) and isinstance(x.ret, New):
            return x.ret
        if _is_helper_call(x, "apply") and len(x.args) in (2, 3) and isinstance(x.args[1], ArrayLit):
            elems = x.args[1].elems
            if all(el is not None for el in elems):
                if len(x.args) == 3:
                    return CallT(x.args[0], x.args[2], list(elems))
                return New(x.args[0], list(elems))
        return x

    return _transform(e, fn)


def _transform(e, fn):
    e = e.replace_children(lambda c: _transform(c, fn))
    return fn(e)


def _simplify_stmt(s, out, live, ctx):
    _map_stmt(s, simplify_expr)
    # new F(args): SelectObj(T, ConstructT(F, T, args)) with T = CreateThis(F).
    if isinstance(s, SetReg) and isinstance(s.value, SelectObj):
        so = s.value
        if (
            isinstance(so.ret, ConstructT)
            and isinstance(so.this, Reg)
            and isinstance(so.ret.this, Reg)
            and so.this.n == so.ret.this.n
        ):
            t = so.this.n
            if t not in live or s.reg == t:
                for j in range(len(out) - 1, -1, -1):
                    st = out[j]
                    if stmt_def(st) == t:
                        if isinstance(st.value, CreateThis) and _same_callee(
                            st.value.callee, so.ret.callee
                        ):
                            del out[j]
                            s.value = New(so.ret.callee, so.ret.args)
                        break
                    if _reads(st, t):
                        break
    # Object / array literal construction.
    if isinstance(s, ExprStmt):
        e = s.e
        if isinstance(e, DefineProp) and isinstance(e.obj, Reg):
            return _fold_define(s, e, out)
        if isinstance(e, DefineAccessor) and isinstance(e.obj, Reg) and e.enumerable:
            return _fold_accessor(s, e, out)
        if _is_helper_call(e, "putSlot") and isinstance(e.args[0], Reg):
            return _fold_put_slot(s, e, out)
        if _is_helper_call(e, "arraySpread") and len(e.args) == 3 and isinstance(e.args[0], Reg):
            return _fold_spread(s, e, out, None, live)
    if isinstance(s, SetReg):
        e = s.value
        if _is_helper_call(e, "arraySpread") and len(e.args) == 3 and isinstance(e.args[0], Reg):
            return _fold_spread(s, e, out, s.reg, live)
    return s


def _is_helper_call(e, name):
    return (
        isinstance(e, Call)
        and isinstance(e.callee, Member)
        and isinstance(e.callee.obj, Name)
        and e.callee.obj.name == "$hbc"
        and isinstance(e.callee.key, Lit)
        and e.callee.key.v == name
    )


def _fold_spread(s, e, out, result_reg, live):
    """[...elems] + arraySpread(R, X, n) -> R = [...elems, ...X]. If the next
    index is used, it is re-expressed as R.length."""
    n = e.args[0].n
    idx = e.args[2]
    skip = None
    if isinstance(idx, Reg):
        # Index produced by an earlier spread into the same array.
        for j in range(len(out) - 1, -1, -1):
            st = out[j]
            if stmt_def(st) == idx.n:
                v = st.value
                if (
                    isinstance(v, Member)
                    and isinstance(v.obj, Reg)
                    and v.obj.n == n
                    and isinstance(v.key, Lit)
                    and v.key.v == "length"
                ):
                    skip = j
                break
        if skip is None or idx.n in live or idx.n == result_reg:
            return s
        if any(_reads(out[k], idx.n) for k in range(skip + 1, len(out))):
            return s
    j = _find_literal_def(out, n, skip)
    if j is None or not isinstance(out[j].value, ArrayLit):
        return s
    lit = out[j].value
    if skip is None:
        if not (isinstance(idx, Lit) and idx.v == len(lit.elems)):
            return s
        if any(isinstance(x, Spread) for x in lit.elems):
            return s
    if any(x is None for x in lit.elems):
        return s
    if _reg_count(e.args[1], n):
        return s
    if not _can_move_to_end(out, j):
        return s
    if skip is not None:
        del out[skip]
    del out[j]
    new = SetReg(n, ArrayLit(lit.elems + [Spread(e.args[1])]))
    if result_reg is None or result_reg == n:
        return new
    out.append(new)
    return SetReg(result_reg, Member(Reg(n), Lit("length")))


def _same_callee(a, b):
    return _same(a, b) or (isinstance(a, Reg) and isinstance(b, Reg) and a.n == b.n)


def _find_literal_def(out, n, skip=None):
    for j in range(len(out) - 1, -1, -1):
        if j == skip:
            continue
        st = out[j]
        if stmt_def(st) == n:
            if isinstance(st.value, (ObjectLit, ArrayLit)):
                return j
            return None
        if _reads(st, n):
            return None
    return None


def _can_move_to_end(out, j):
    lit = out[j].value
    if lit.pure:
        return True
    return all(stmt_is_pure(out[k]) for k in range(j + 1, len(out)))


def _fold_define(s, e, out):
    n = e.obj.n
    j = _find_literal_def(out, n)
    if j is None or not _can_move_to_end(out, j):
        return s
    lit = out[j].value
    if _reg_count(e.value, n) or _reg_count(e.key, n):
        return s
    if isinstance(lit, ObjectLit):
        if isinstance(e.key, Lit) and isinstance(e.key.v, (str, int, float)) and not isinstance(e.key.v, bool):
            if not e.enumerable:
                return s
            key = e.key.v
            if key == "__proto__":
                return s
            if any(k in ("init", "get", "set") and kk == key for k, kk, _ in lit.props):
                # Redefinition of an existing key: keep the order semantics.
                return s
            new = ObjectLit(lit.props + [("init", key, e.value)])
        else:
            if not e.enumerable:
                return s
            new = ObjectLit(lit.props + [("computed", e.key, e.value)])
    else:
        if not (isinstance(e.key, Lit) and isinstance(e.key.v, int) and not isinstance(e.key.v, bool)):
            return s
        idx = e.key.v
        elems = list(lit.elems)
        if idx == len(elems):
            elems.append(e.value)
        elif (
            idx < len(elems)
            and elems[idx] is None
            and all(x is None or isinstance(x, Lit) for x in elems[idx + 1 :])
        ):
            elems[idx] = e.value
        else:
            return s
        new = ArrayLit(elems)
    del out[j]
    return SetReg(n, new)


def _fold_accessor(s, e, out):
    n = e.obj.n
    j = _find_literal_def(out, n)
    if j is None or not _can_move_to_end(out, j):
        return s
    lit = out[j].value
    if not isinstance(lit, ObjectLit):
        return s
    if not (isinstance(e.key, Lit) and isinstance(e.key.v, (str, int, float))):
        return s
    key = e.key.v
    if key == "__proto__" or any(kk == key for _, kk, _ in lit.props):
        return s
    props = list(lit.props)
    for kind, fn_ in (("get", e.getter), ("set", e.setter)):
        if isinstance(fn_, Lit) and fn_.v is UNDEFINED:
            continue
        if not isinstance(fn_, FuncExpr):
            return s
        props.append((kind, key, fn_))
    del out[j]
    return SetReg(n, ObjectLit(props))


def _fold_put_slot(s, e, out):
    n = e.args[0].n
    j = _find_literal_def(out, n)
    if j is None or not _can_move_to_end(out, j):
        return s
    lit = out[j].value
    if not isinstance(lit, ObjectLit) or not isinstance(e.args[1], Lit):
        return s
    idx = e.args[1].v
    own = [i for i, (k, _, _) in enumerate(lit.props) if k == "init"]
    if any(k not in ("init", "proto") for k, _, _ in lit.props) or idx >= len(own):
        return s
    if _reg_count(e.args[2], n):
        return s
    props = list(lit.props)
    # The new value is evaluated at its position in the literal; that must not
    # move it before side effects of later entries.
    if any(not isinstance(v, Lit) for _, _, v in props[own[idx] + 1 :]):
        return s
    k, key, _ = props[own[idx]]
    props[own[idx]] = (k, key, e.args[2])
    del out[j]
    return SetReg(n, ObjectLit(props))


# ---------------------------------------------------------------------------
# Final cleanups
# ---------------------------------------------------------------------------


def finalize_expr(e, declared_globals):
    from .lifter import TryMember

    def fn(x):
        if isinstance(x, CallT):
            if isinstance(x.this, Lit) and x.this.v is UNDEFINED:
                return Call(x.callee, x.args)
            if isinstance(x.callee, Member) and _same(x.callee.obj, x.this):
                return Call(x.callee, x.args)
            return Call(Member(x.callee, Lit("call")), [x.this] + x.args)
        if isinstance(x, ConstructT):
            return Call(
                Member(Name("$hbc", "helper"), Lit("construct")),
                [x.callee, x.this, ArrayLit(x.args)],
            )
        if isinstance(x, CreateThis):
            return Call(Member(Name("$hbc", "helper"), Lit("createThis")), [x.callee])
        if isinstance(x, SelectObj):
            return Call(Member(Name("$hbc", "helper"), Lit("selectObject")), [x.this, x.ret])
        if isinstance(x, Member) and _is_global_obj(x.obj) and isinstance(x.key, Lit):
            k = x.key.v
            from .jsast import is_identifier

            if isinstance(k, str) and is_identifier(k):
                if isinstance(x, TryMember) or k in declared_globals:
                    return Name(k, "global")
            if isinstance(x, TryMember):
                return Member(x.obj, x.key)
        if isinstance(x, TryMember):
            return Member(x.obj, x.key)
        if isinstance(x, CoerceThis):
            if isinstance(x.e, Name) and x.e.kind == "this":
                return x.e
            return Call(Member(Name("$hbc", "helper"), Lit("coerceThis")), [x.e])
        if isinstance(x, Assign) and isinstance(x.target, Member):
            t = x.target
            if _is_global_obj(t.obj) and isinstance(t.key, Lit):
                from .jsast import is_identifier

                k = t.key.v
                if isinstance(k, str) and is_identifier(k) and (
                    isinstance(t, TryMember) or k in declared_globals
                ):
                    return Assign(Name(k, "global"), x.value)
            if isinstance(t, TryMember):
                return Assign(Member(t.obj, t.key), x.value)
        if isinstance(x, Binary) and x.op in ("===", "!==", "==", "!="):
            if isinstance(x.l, Lit) and not isinstance(x.r, Lit):
                return Binary(x.op, x.r, x.l)
        if isinstance(x, Unary) and x.op == "!" and isinstance(x.e, Binary):
            inv = {"===": "!==", "!==": "===", "==": "!=", "!=": "=="}.get(x.e.op)
            if inv:
                return Binary(inv, x.e.l, x.e.r)
        if isinstance(x, DefineProp):
            return _define_prop_call(x)
        from .lifter import DefineAccessor

        if isinstance(x, DefineAccessor):
            props = []
            for nm, fn_ in (("get", x.getter), ("set", x.setter)):
                if not (isinstance(fn_, Lit) and fn_.v is UNDEFINED):
                    props.append(("init", nm, fn_))
            props.append(("init", "enumerable", Lit(x.enumerable)))
            props.append(("init", "configurable", Lit(True)))
            desc = ObjectLit(props)
            return Call(
                Member(Name("Object", "builtin"), Lit("defineProperty")), [x.obj, x.key, desc]
            )
        return x

    return _transform(e, fn)


def _is_global_obj(e):
    return isinstance(e, Name) and e.kind == "globalobj"


def _define_prop_call(x):
    desc = ObjectLit(
        [
            ("init", "value", x.value),
            ("init", "writable", Lit(True)),
            ("init", "enumerable", Lit(bool(x.enumerable))),
            ("init", "configurable", Lit(True)),
        ]
    )
    return Call(Member(Name("Object", "builtin"), Lit("defineProperty")), [x.obj, x.key, desc])


def finalize_blocks(blocks, declared_globals):
    for b in blocks:
        for s in b.stmts + [b.term]:
            _map_stmt(s, lambda e: finalize_expr(e, declared_globals))


def run_passes(blocks, ctx):
    compute_edges(blocks)
    copy_propagate(blocks)
    constant_propagate(blocks)
    dce(blocks)
    for _ in range(3):
        fold_blocks(blocks, ctx)
        copy_propagate(blocks)
        if not dce(blocks):
            break
    finalize_blocks(blocks, ctx.declared_globals)
