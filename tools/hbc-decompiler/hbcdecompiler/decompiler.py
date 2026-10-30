# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Whole-file decompilation driver: lifts, optimizes and structures every
function, nests closures at their creation sites and prints JavaScript."""

import os
import traceback

from . import disasm
from .dataflow import run_passes
from .jsast import (
    UNDEFINED,
    ArrayLit,
    Assign,
    Binary,
    Break,
    Call,
    Comment,
    Cond,
    Continue,
    Expr,
    ExprStmt,
    ForIn,
    FuncExpr,
    If,
    Labeled,
    Lit,
    Logical,
    Loop,
    Member,
    Name,
    Printer,
    Reg,
    Return,
    SetReg,
    Switch,
    TemplateLit,
    Throw,
    Try,
    Unary,
    VarDecl,
    child_blocks,
    is_identifier,
    negate,
    quote_string,
    simplify_bool,
    stmt_exprs,
    walk_expr,
    walk_stmts,
)
from .lifter import FunctionLifter
from .structure import structure

PRELUDE_PATH = os.path.join(os.path.dirname(__file__), "prelude.js")


class DecompiledFunction:
    def __init__(self, fid):
        self.fid = fid
        self.name = ""
        self.body = []
        self.params = []
        self.strict = False
        self.kind = 0
        self.fallback = False
        self.error = None
        self.hoisted = []
        self.regs = []
        self.parent = None


class Decompiler:
    def __init__(self, hbc, options=None):
        self.hbc = hbc
        self.options = options or {}
        self.env_counter = 0
        self.declared_globals = set()
        self.closure_env = {}
        self.env_slots = {}
        self.env_container = {}
        self.parent = {}
        self.funcs = {}
        self.stats = {"functions": 0, "fallback": 0, "errors": 0}

    def new_env_id(self):
        self.env_counter += 1
        return self.env_counter - 1

    # ---- per function ----------------------------------------------------
    def process(self, fid):
        f = self.hbc.functions[fid]
        df = DecompiledFunction(fid)
        df.strict = f.strictMode
        df.kind = f.kind
        df.parent = self.parent.get(fid)
        nm = self.hbc.function_name(f)
        df.name = nm if is_identifier(nm) else ""
        df.params = ["a%d" % i for i in range(max(0, f.paramCount - 1))]
        self.stats["functions"] += 1
        try:
            fl = FunctionLifter(self, f)
            blocks = fl.lift(self.closure_env.get(fid))
            for child, env in fl.children.items():
                if self.closure_env.get(child) is None:
                    self.closure_env[child] = env
                self.parent.setdefault(child, fid)
            df.params = ["a%d" % i for i in range(max(0, fl.max_param))]
            run_passes(blocks, self)
            body, fell_back = structure(blocks)
            df.fallback = fell_back
            if fell_back:
                self.stats["fallback"] += 1
            body = cleanup(body, loop_depth=0)
            body = final_rewrites(body)
            body = cleanup(body, loop_depth=0)
            body = strip_tail_return(body)
            df.body = body
            df.envs = fl.envs_created
        except Exception as e:  # pragma: no cover - defensive
            self.stats["errors"] += 1
            df.error = "%s: %s" % (type(e).__name__, e)
            if self.options.get("debug"):
                traceback.print_exc()
            df.body = [
                Comment("decompilation failed: %s" % df.error),
                Throw(Call(Name("Error", "builtin"), [Lit("decompilation failed")])),
            ]
            df.envs = []
        self.funcs[fid] = df
        return df

    def run(self):
        g = self.hbc.header["globalCodeIndex"]
        queue = [g]
        seen = {g}
        i = 0
        while i < len(queue):
            fid = queue[i]
            i += 1
            self.process(fid)
            for child in sorted(self.children_of(fid)):
                if child not in seen and child < len(self.hbc.functions):
                    seen.add(child)
                    queue.append(child)
        self.orphans = []
        for fid in range(len(self.hbc.functions)):
            if fid not in seen:
                seen.add(fid)
                self.orphans.append(fid)
                queue2 = [fid]
                while queue2:
                    x = queue2.pop()
                    self.process(x)
                    for child in self.children_of(x):
                        if child not in seen:
                            seen.add(child)
                            queue2.append(child)
        for df in self.funcs.values():
            for s in walk_stmts(df.body):
                for e in stmt_exprs(s):
                    for x in walk_expr(e):
                        if isinstance(x, FuncExpr):
                            x.func = self.funcs.get(x.fid)
        extra = {}
        for df in self.funcs.values():
            scope_envs(df, self.env_container, extra)
        for fid, names in extra.items():
            df = self.funcs.get(fid)
            if df is not None:
                df.hoisted.extend(n for n in names if n not in df.hoisted)

    def children_of(self, fid):
        out = []
        df = self.funcs.get(fid)
        if df is None:
            return out
        for s in walk_stmts(df.body):
            for e in stmt_exprs(s):
                for x in walk_expr(e):
                    if isinstance(x, FuncExpr):
                        out.append(x.fid)
            if isinstance(s, (Assign,)):
                pass
        return out

    # ---- printing ----------------------------------------------------------
    def render(self):
        printer = Printer(func_printer=self.render_func)
        out = []
        g = self.hbc.header["globalCodeIndex"]
        gdf = self.funcs[g]
        body = global_body(gdf.body)
        if gdf.strict:
            out.append('"use strict";')
        decl = self.declarations(gdf)
        if decl:
            out.append("let %s;" % ", ".join(decl))
        printer.stmts(body, 0, out)
        for fid in self.orphans:
            out.append("")
            out.append("// Function #%d is not created by any reachable code." % fid)
            out.append("var $function%d = %s;" % (fid, self.render_func(FuncExpr(fid), 0)))
        text = "\n".join(out) + "\n"
        header = self.header_comment()
        if "$hbc." in text:
            with open(PRELUDE_PATH) as f:
                text = f.read() + "\n" + text
        return header + text

    def header_comment(self):
        h = self.hbc.header
        lines = [
            "// Decompiled from Hermes bytecode version %d." % self.hbc.version,
            "// Functions: %d (%d structured with a dispatch loop, %d failed)."
            % (self.stats["functions"], self.stats["fallback"], self.stats["errors"]),
        ]
        if self.hbc.cjsModules:
            lines.append("// CommonJS modules:")
            for a, b in self.hbc.cjsModules:
                name = a if self.hbc.cjsModulesStaticallyResolved else self.hbc.string(a)
                lines.append("//   %s -> function #%d" % (name, b))
        return "\n".join(lines) + "\n"

    def declarations(self, df):
        regs = set()
        for s in walk_stmts(df.body):
            if isinstance(s, SetReg):
                regs.add(s.reg)
            for e in stmt_exprs(s):
                for x in walk_expr(e):
                    if isinstance(x, Reg):
                        regs.add(x.n)
        names = ["r%d" % r for r in sorted(regs)]
        return names + df.hoisted

    def render_func(self, fe, indent, method=None):
        printer = Printer(func_printer=self.render_func)
        df = self.funcs.get(fe.fid)
        if df is None:
            self.process(fe.fid)
            df = self.funcs[fe.fid]
        pad = printer.unit * (indent + 1)
        lines = []
        name = df.name
        if name and _references_name(df.body, name):
            name = ""
        if self.options.get("annotate", True):
            fn = self.hbc.functions[fe.fid]
            info = "#%d" % fe.fid
            nm = self.hbc.function_name(fn)
            if nm and nm != name:
                info += " " + nm
            if df.kind == 1:
                info += " (generator)"
            elif df.kind == 2:
                info += " (async)"
            if df.fallback:
                info += " (unstructured)"
            lines.append(pad + "// " + info)
        parent = self.funcs.get(df.parent) if df.parent is not None else None
        if df.strict and not (parent and parent.strict):
            lines.append(pad + '"use strict";')
        decl = self.declarations(df)
        if decl:
            lines.append(pad + "let %s;" % ", ".join(decl))
        printer.stmts(df.body, indent + 1, lines)
        if method:
            head = "%s(%s) {" % (method, ", ".join(df.params))
        else:
            head = "function %s(%s) {" % (name, ", ".join(df.params))
        return "\n".join([head] + lines + [printer.unit * indent + "}"])


def _references_name(body, name):
    for s in walk_stmts(body):
        for e in stmt_exprs(s):
            for x in walk_expr(e):
                if isinstance(x, Name) and x.name == name:
                    return True
                if isinstance(x, Assign) and isinstance(x.target, Name) and x.target.name == name:
                    return True
    return False


# ---------------------------------------------------------------------------
# Structured AST cleanups
# ---------------------------------------------------------------------------

JUMPS = (Break, Continue, Return, Throw)


def ends_with_jump(stmts):
    if not stmts:
        return False
    s = stmts[-1]
    if isinstance(s, JUMPS):
        return True
    if isinstance(s, If):
        return ends_with_jump(s.then) and ends_with_jump(s.els)
    if isinstance(s, Try):
        return ends_with_jump(s.body) and ends_with_jump(s.handler)
    return False


def _contains_continue_to(stmts, loop):
    """True if stmts contain a continue that targets `loop`."""
    for s in stmts:
        if isinstance(s, Continue):
            if s.label is None or s.label == loop.label:
                return True
        elif isinstance(s, (Loop, ForIn)):
            # Unlabeled continues inside refer to the inner loop.
            if _contains_labeled_continue(s.body, loop.label):
                return True
        else:
            for b in child_blocks(s):
                if _contains_continue_to(b, loop):
                    return True
    return False


def _contains_labeled_continue(stmts, label):
    for s in walk_stmts(stmts):
        if isinstance(s, Continue) and s.label == label:
            return True
    return False


def _strip_trailing_continue(stmts, loop):
    """Remove continues that are in tail position of a loop body."""
    if not stmts:
        return stmts
    last = stmts[-1]
    if isinstance(last, Continue) and (last.label is None or last.label == loop.label):
        return stmts[:-1]
    if isinstance(last, If):
        last.then = _strip_trailing_continue(last.then, loop)
        last.els = _strip_trailing_continue(last.els, loop)
    if isinstance(last, Try):
        last.body = _strip_trailing_continue(last.body, loop)
        last.handler = _strip_trailing_continue(last.handler, loop)
    return stmts


def cleanup(stmts, loop_depth):
    out = []
    for s in stmts:
        if isinstance(s, If):
            s.cond = simplify_bool(s.cond)
            s.then = cleanup(s.then, loop_depth)
            s.els = cleanup(s.els, loop_depth)
            if not s.then and not s.els:
                if not s.cond.pure:
                    out.append(ExprStmt(s.cond))
                continue
            if not s.then:
                s.cond, s.then, s.els = simplify_bool(negate(s.cond)), s.els, []
            # Ternary: if (c) r = a; else r = b;
            t = _ternary(s)
            if t is not None:
                out.append(t)
                continue
            if (
                s.els
                and ends_with_jump(s.els)
                and _size(s.els) < _size(s.then)
            ):
                s.cond, s.then, s.els = simplify_bool(negate(s.cond)), s.els, s.then
            if s.els and ends_with_jump(s.then):
                els = s.els
                s.els = []
                out.append(s)
                out.extend(cleanup(els, loop_depth))
                continue
            if s.els and ends_with_jump(s.els) and not ends_with_jump(s.then) and _size(s.els) < _size(s.then):
                then = s.then
                s.cond, s.then, s.els = simplify_bool(negate(s.cond)), s.els, []
                out.append(s)
                out.extend(cleanup(then, loop_depth))
                continue
            # Logical: r = a; if (r) r = b;  ->  r = a && b
            if out and _logical_assign(out, s):
                continue
            out.append(s)
        elif isinstance(s, Loop):
            s.body = cleanup(s.body, loop_depth + 1)
            s.body = _strip_trailing_continue(s.body, s)
            _loop_form(s)
            out.append(s)
        elif isinstance(s, ForIn):
            s.body = cleanup(s.body, loop_depth + 1)
            out.append(s)
        elif isinstance(s, Switch):
            for i, (labels, body) in enumerate(s.cases):
                body = cleanup(body, loop_depth)
                if i == len(s.cases) - 1 and body and isinstance(body[-1], Break) and body[-1].label is None:
                    body = body[:-1]
                s.cases[i] = (labels, body)
            out.append(s)
        elif isinstance(s, Try):
            s.body = cleanup(s.body, loop_depth)
            s.handler = cleanup(s.handler, loop_depth)
            out.append(s)
        elif isinstance(s, Labeled):
            s.body = cleanup(s.body, loop_depth)
            out.append(s)
        else:
            out.append(s)
        if ends_with_jump(out):
            break
    return out


def _size(stmts):
    return sum(1 for _ in walk_stmts(stmts))


def _ternary(s):
    if (
        len(s.then) == 1
        and len(s.els) == 1
        and isinstance(s.then[0], SetReg)
        and isinstance(s.els[0], SetReg)
        and s.then[0].reg == s.els[0].reg
    ):
        return SetReg(s.then[0].reg, Cond(s.cond, s.then[0].value, s.els[0].value))
    return None


def _logical_assign(out, s):
    prev = out[-1]
    if not (isinstance(prev, SetReg) and not s.els and len(s.then) == 1):
        return False
    inner = s.then[0]
    if not (isinstance(inner, SetReg) and inner.reg == prev.reg):
        return False
    c = s.cond
    r = prev.reg
    if isinstance(c, Reg) and c.n == r:
        op = "&&"
    elif isinstance(c, Unary) and c.op == "!" and isinstance(c.e, Reg) and c.e.n == r:
        op = "||"
    elif (
        isinstance(c, Binary)
        and c.op in ("==", "!=")
        and isinstance(c.l, Reg)
        and c.l.n == r
        and isinstance(c.r, Lit)
        and c.r.v is None
    ):
        # r = a; if (r == null) r = b;  ->  r = a ?? b
        if c.op == "!=":
            return False
        op = "??"
    else:
        return False
    out[-1] = SetReg(r, Logical(op, prev.value, inner.value))
    return True


def _loop_form(loop):
    body = loop.body
    if loop.kind != "for":
        return
    # while (c): leading `if (!c) break;`
    if body and isinstance(body[0], If) and not body[0].els:
        first = body[0]
        if len(first.then) == 1 and isinstance(first.then[0], Break) and first.then[0].label is None:
            loop.kind = "while"
            loop.cond = simplify_bool(negate(first.cond))
            loop.body = body[1:]
            return
    # do { ... } while (c): trailing `if (c) continue; break;`
    if (
        len(body) >= 2
        and isinstance(body[-1], Break)
        and body[-1].label is None
        and isinstance(body[-2], If)
        and not body[-2].els
        and len(body[-2].then) == 1
        and isinstance(body[-2].then[0], Continue)
        and body[-2].then[0].label in (None, loop.label)
    ):
        rest = body[:-2]
        if not _contains_continue_to(rest, loop) and not _breaks_inside_to(rest):
            loop.kind = "dowhile"
            loop.cond = body[-2].cond
            loop.body = rest
            return
    # Trailing `if (c) break;` -> do-while(!c)
    if (
        body
        and isinstance(body[-1], If)
        and not body[-1].els
        and len(body[-1].then) == 1
        and isinstance(body[-1].then[0], Break)
        and body[-1].then[0].label is None
    ):
        rest = body[:-1]
        if not _contains_continue_to(rest, loop):
            loop.kind = "dowhile"
            loop.cond = simplify_bool(negate(body[-1].cond))
            loop.body = rest


def _breaks_inside_to(stmts):
    return False


# ---------------------------------------------------------------------------
# Final expression rewrites (template literals etc.)
# ---------------------------------------------------------------------------


def _rewrite_expr(e):
    from .jsast import transform

    def fn(x):
        if (
            isinstance(x, Call)
            and isinstance(x.callee, Member)
            and isinstance(x.callee.obj, Name)
            and x.callee.obj.name == "HermesInternal"
            and isinstance(x.callee.key, Lit)
            and x.callee.key.v == "concat"
            and x.args
        ):
            parts = []
            for a in x.args:
                if isinstance(a, Lit) and isinstance(a.v, str):
                    parts.append(a.v)
                else:
                    parts.append(a)
            return TemplateLit(parts)
        return x

    return transform(e, fn)


def final_rewrites(stmts):
    from .jsast import map_stmt_exprs

    for s in walk_stmts(stmts):
        map_stmt_exprs(s, _rewrite_expr)
    return stmts


def strip_tail_return(body):
    if body and isinstance(body[-1], Return):
        e = body[-1].e
        if e is None or (isinstance(e, Lit) and e.v is UNDEFINED):
            return body[:-1]
    return body


def global_body(body):
    """Make the global function's statements valid at script top level."""
    body = list(body)
    if body and isinstance(body[-1], Return):
        e = body.pop().e
        if e is not None and not e.pure:
            body.append(ExprStmt(e))
    has_return = any(isinstance(s, Return) for s in walk_stmts(body))
    if not has_return:
        return body

    def conv(stmts):
        out = []
        for s in stmts:
            if isinstance(s, Return):
                if s.e is not None and not s.e.pure:
                    out.append(ExprStmt(s.e))
                out.append(Break("$global"))
                continue
            if isinstance(s, If):
                s.then, s.els = conv(s.then), conv(s.els)
            elif isinstance(s, (Loop, Labeled, ForIn)):
                s.body = conv(s.body)
            elif isinstance(s, Switch):
                s.cases = [(l, conv(b)) for l, b in s.cases]
            elif isinstance(s, Try):
                s.body, s.handler = conv(s.body), conv(s.handler)
            out.append(s)
        return out

    lab = Labeled("$global", conv(body))
    lab.used_label = True
    return [lab]


# ---------------------------------------------------------------------------
# Environment variable scoping
# ---------------------------------------------------------------------------


def scope_envs(df, containers, extra):
    """Hoist env variable declarations to the function top, except
    block-scoped environments created inside loops whose variables are only
    referenced after the declaration in the same block (these keep their
    per-iteration `let` semantics)."""
    hoisted = []

    def visit(stmts, in_loop):
        i = 0
        while i < len(stmts):
            s = stmts[i]
            if isinstance(s, VarDecl) and s.kind == "let" and s.env is not None:
                env = s.env
                if env.eid in containers:
                    # This environment is stored inside another one (generator
                    # state); its variables must outlive this function call.
                    root = env
                    while root.eid in containers:
                        root = containers[root.eid]
                    lst = extra.setdefault(root.owner, [])
                    lst.extend(n for n in s.names if n not in lst)
                    del stmts[i]
                    continue
                keep = (
                    in_loop
                    and env.kind == "scope"
                    and not _refs_outside(df.body, stmts, i, set(s.names))
                    and not df.fallback
                )
                if not keep:
                    hoisted.extend(n for n in s.names if n not in hoisted)
                    del stmts[i]
                    continue
            for b in child_blocks(s):
                visit(b, in_loop or isinstance(s, (Loop, ForIn)))
            i += 1

    visit(df.body, False)
    df.hoisted = hoisted


def _refs_outside(body, container, idx, names):
    """True if any of `names` is referenced in `body` outside
    container[idx+1:] (searching nested functions too)."""
    allowed = set(id(s) for s in container[idx + 1 :])

    def scan(stmts, inside):
        for s in stmts:
            ins = inside or id(s) in allowed
            if not ins and _stmt_refs(s, names):
                return True
            for b in child_blocks(s):
                if scan(b, ins):
                    return True
        return False

    return scan(body, False)


def _stmt_refs(s, names):
    for e in stmt_exprs(s):
        for x in walk_expr(e):
            if isinstance(x, Name) and x.name in names:
                return True
            if isinstance(x, FuncExpr) and x.func is not None:
                if _body_refs(x.func.body, names):
                    return True
    return False


def _body_refs(body, names):
    for s in walk_stmts(body):
        if _stmt_refs(s, names):
            return True
    return False
