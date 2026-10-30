# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""A small JavaScript AST used as the decompiler's IR, plus a printer.

Expressions are immutable-ish trees. Statements are either "flat" (produced by
the lifter, carrying register defs/uses) or structured (produced by the
control-flow structurer).
"""

import json
import math
import re

# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------

# Operator precedence (higher binds tighter), roughly following the ECMAScript
# grammar.
PREC_SEQ = 1
PREC_ASSIGN = 2
PREC_COND = 3
PREC_NULLISH = 4
PREC_OR = 4
PREC_AND = 5
PREC_BITOR = 6
PREC_BITXOR = 7
PREC_BITAND = 8
PREC_EQ = 9
PREC_REL = 10
PREC_SHIFT = 11
PREC_ADD = 12
PREC_MUL = 13
PREC_EXP = 14
PREC_UNARY = 15
PREC_POSTFIX = 16
PREC_NEW = 17
PREC_CALL = 18
PREC_MEMBER = 19
PREC_PRIMARY = 20

BINARY_PREC = {
    "||": PREC_OR,
    "&&": PREC_AND,
    "??": PREC_NULLISH,
    "|": PREC_BITOR,
    "^": PREC_BITXOR,
    "&": PREC_BITAND,
    "==": PREC_EQ,
    "!=": PREC_EQ,
    "===": PREC_EQ,
    "!==": PREC_EQ,
    "<": PREC_REL,
    ">": PREC_REL,
    "<=": PREC_REL,
    ">=": PREC_REL,
    "instanceof": PREC_REL,
    "in": PREC_REL,
    "<<": PREC_SHIFT,
    ">>": PREC_SHIFT,
    ">>>": PREC_SHIFT,
    "+": PREC_ADD,
    "-": PREC_ADD,
    "*": PREC_MUL,
    "/": PREC_MUL,
    "%": PREC_MUL,
    "**": PREC_EXP,
}

RESERVED = set(
    """break case catch class const continue debugger default delete do else
    enum export extends false finally for function if import in instanceof new
    null return super switch this throw true try typeof var void while with
    yield let static implements interface package private protected public
    await""".split()
)

_IDENT_RE = re.compile(r"^[A-Za-z_$][A-Za-z0-9_$]*$")


def is_identifier(s):
    if not isinstance(s, str) or not s or s in RESERVED:
        return False
    if _IDENT_RE.match(s):
        return True
    # Non-ASCII identifiers: Python's rules (XID_Start/XID_Continue) are a
    # close match for ECMAScript's ID_Start/ID_Continue.
    return s.replace("$", "_").isidentifier()


class Expr:
    __slots__ = ()
    # Whether evaluating the expression can have side effects or observe
    # mutable state. Overridden by subclasses.
    pure = False

    def children(self):
        """Sub-expressions in evaluation order."""
        return ()

    def replace_children(self, fn):
        """Return a copy with each child c replaced by fn(c)."""
        return self


class Reg(Expr):
    __slots__ = ("n",)
    pure = True

    def __init__(self, n):
        self.n = n

    def __eq__(self, other):
        return isinstance(other, Reg) and other.n == self.n

    def __hash__(self):
        return hash(("reg", self.n))

    def __repr__(self):
        return "r%d" % self.n


class Undefined:
    def __repr__(self):
        return "undefined"


UNDEFINED = Undefined()


class Empty:
    """The TDZ 'empty' value."""

    def __repr__(self):
        return "empty"


EMPTY = Empty()


class BigIntValue:
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = v


class Lit(Expr):
    __slots__ = ("v",)
    pure = True

    def __init__(self, v):
        self.v = v

    def __eq__(self, other):
        return (
            isinstance(other, Lit)
            and type(other.v) is type(self.v)
            and (
                other.v == self.v
                or (isinstance(self.v, float) and math.isnan(self.v) and math.isnan(other.v))
            )
        )

    def __hash__(self):
        return hash(("lit", repr(self.v)))

    def __repr__(self):
        return "Lit(%r)" % (self.v,)


class Name(Expr):
    """An identifier. kind is one of: global, env, param, this, arguments,
    builtin, local, catch, helper, newtarget."""

    __slots__ = ("name", "kind")

    def __init__(self, name, kind="local"):
        self.name = name
        self.kind = kind

    @property
    def pure(self):
        return self.kind in (
            "param",
            "this",
            "arguments",
            "builtin",
            "catch",
            "helper",
            "newtarget",
            "globalobj",
        )

    def __eq__(self, other):
        return isinstance(other, Name) and other.name == self.name

    def __hash__(self):
        return hash(("name", self.name))

    def __repr__(self):
        return self.name


class Member(Expr):
    __slots__ = ("obj", "key")

    def __init__(self, obj, key):
        self.obj = obj
        self.key = key  # Expr

    @property
    def pure(self):
        # Runtime helper lookups ($hbc.name) have no side effects.
        return isinstance(self.obj, Name) and self.obj.kind == "helper"

    def children(self):
        return (self.obj, self.key)

    def replace_children(self, fn):
        return Member(fn(self.obj), fn(self.key))


class Call(Expr):
    __slots__ = ("callee", "args")

    def __init__(self, callee, args):
        self.callee = callee
        self.args = list(args)

    def children(self):
        return (self.callee,) + tuple(self.args)

    def replace_children(self, fn):
        return Call(fn(self.callee), [fn(a) for a in self.args])


class New(Expr):
    __slots__ = ("callee", "args")

    def __init__(self, callee, args):
        self.callee = callee
        self.args = list(args)

    def children(self):
        return (self.callee,) + tuple(self.args)

    def replace_children(self, fn):
        return New(fn(self.callee), [fn(a) for a in self.args])


class Unary(Expr):
    __slots__ = ("op", "e")

    def __init__(self, op, e):
        self.op = op
        self.e = e

    @property
    def pure(self):
        return self.op in ("typeof", "!", "void") and self.e.pure

    def children(self):
        return (self.e,)

    def replace_children(self, fn):
        return Unary(self.op, fn(self.e))


class Binary(Expr):
    __slots__ = ("op", "l", "r")

    def __init__(self, op, l, r):
        self.op = op
        self.l = l
        self.r = r

    @property
    def pure(self):
        return self.op in ("===", "!==") and self.l.pure and self.r.pure

    def children(self):
        return (self.l, self.r)

    def replace_children(self, fn):
        return Binary(self.op, fn(self.l), fn(self.r))


class Logical(Expr):
    """Short circuit && / || / ??."""

    __slots__ = ("op", "l", "r")

    def __init__(self, op, l, r):
        self.op = op
        self.l = l
        self.r = r

    @property
    def pure(self):
        return self.l.pure and self.r.pure

    def children(self):
        return (self.l, self.r)

    def replace_children(self, fn):
        return Logical(self.op, fn(self.l), fn(self.r))


class Cond(Expr):
    __slots__ = ("c", "a", "b")

    def __init__(self, c, a, b):
        self.c = c
        self.a = a
        self.b = b

    @property
    def pure(self):
        return self.c.pure and self.a.pure and self.b.pure

    def children(self):
        return (self.c, self.a, self.b)

    def replace_children(self, fn):
        return Cond(fn(self.c), fn(self.a), fn(self.b))


class Assign(Expr):
    __slots__ = ("target", "value")

    def __init__(self, target, value):
        self.target = target
        self.value = value

    def children(self):
        if isinstance(self.target, Member):
            return (self.target.obj, self.target.key, self.value)
        return (self.value,)

    def replace_children(self, fn):
        if isinstance(self.target, Member):
            return Assign(
                Member(fn(self.target.obj), fn(self.target.key)), fn(self.value)
            )
        return Assign(self.target, fn(self.value))


class Spread(Expr):
    """`...e` in an array literal or argument list."""

    __slots__ = ("e",)

    def __init__(self, e):
        self.e = e

    def children(self):
        return (self.e,)

    def replace_children(self, fn):
        return Spread(fn(self.e))


class Seq(Expr):
    """Comma expression."""

    __slots__ = ("exprs",)

    def __init__(self, exprs):
        self.exprs = list(exprs)

    @property
    def pure(self):
        return all(e.pure for e in self.exprs)

    def children(self):
        return tuple(self.exprs)

    def replace_children(self, fn):
        return Seq([fn(e) for e in self.exprs])


class ObjectLit(Expr):
    """props: list of (kind, key, value): kind is 'init' (key is a str or
    number), 'computed' (key is an Expr), 'proto' (value is the prototype) or
    'spread'."""

    __slots__ = ("props",)

    def __init__(self, props):
        self.props = list(props)

    @property
    def pure(self):
        return all(
            v.pure and (k != "computed" or key.pure) and k != "spread"
            for k, key, v in self.props
        )

    def children(self):
        out = []
        for k, key, v in self.props:
            if k == "computed":
                out.append(key)
            out.append(v)
        return tuple(out)

    def replace_children(self, fn):
        props = []
        for k, key, v in self.props:
            if k == "computed":
                key = fn(key)
            props.append((k, key, fn(v)))
        return ObjectLit(props)


class ArrayLit(Expr):
    """elems: list of Expr, None for holes, or ('spread', Expr)."""

    __slots__ = ("elems",)

    def __init__(self, elems):
        self.elems = list(elems)

    @property
    def pure(self):
        return all(e is None or (isinstance(e, Expr) and e.pure) for e in self.elems)

    def children(self):
        out = []
        for e in self.elems:
            if isinstance(e, tuple):
                out.append(e[1])
            elif e is not None:
                out.append(e)
        return tuple(out)

    def replace_children(self, fn):
        elems = []
        for e in self.elems:
            if isinstance(e, tuple):
                elems.append((e[0], fn(e[1])))
            elif e is None:
                elems.append(None)
            else:
                elems.append(fn(e))
        return ArrayLit(elems)


class RegExpLit(Expr):
    __slots__ = ("pattern", "flags")
    pure = True

    def __init__(self, pattern, flags):
        self.pattern = pattern
        self.flags = flags


class FuncExpr(Expr):
    """A closure. `func` is a decompiled function object (see decompiler)."""

    __slots__ = ("fid", "func")
    pure = True

    def __init__(self, fid, func=None):
        self.fid = fid
        self.func = func


class TemplateLit(Expr):
    """A template literal; parts are str (cooked text) or Expr."""

    __slots__ = ("parts",)

    def __init__(self, parts):
        self.parts = parts

    def children(self):
        return tuple(p for p in self.parts if not isinstance(p, str))

    def replace_children(self, fn):
        return TemplateLit([p if isinstance(p, str) else fn(p) for p in self.parts])


class EnvRef(Expr):
    """A register holding a lexical environment (never printed)."""

    __slots__ = ("env",)
    pure = True

    def __init__(self, env):
        self.env = env


class Raw(Expr):
    """Verbatim text (used for things like `new.target`)."""

    __slots__ = ("text", "prec")
    pure = True

    def __init__(self, text, prec=PREC_PRIMARY):
        self.text = text
        self.prec = prec


def helper(name):
    return Member(Name("$hbc", "helper"), Lit(name))


def hcall(name, *args):
    return Call(helper(name), list(args))


# ---------------------------------------------------------------------------
# Statements
# ---------------------------------------------------------------------------


class Stmt:
    __slots__ = ()


class SetReg(Stmt):
    """reg = value (flat IR)."""

    __slots__ = ("reg", "value")

    def __init__(self, reg, value):
        self.reg = reg
        self.value = value

    def __repr__(self):
        return "SetReg(r%d, %r)" % (self.reg, self.value)


class ExprStmt(Stmt):
    __slots__ = ("e",)

    def __init__(self, e):
        self.e = e


class Return(Stmt):
    __slots__ = ("e",)

    def __init__(self, e):
        self.e = e


class Throw(Stmt):
    __slots__ = ("e",)

    def __init__(self, e):
        self.e = e


class Comment(Stmt):
    __slots__ = ("text",)

    def __init__(self, text):
        self.text = text


class Debugger(Stmt):
    __slots__ = ()


class VarDecl(Stmt):
    """`kind names;` kind is var/let."""

    __slots__ = ("kind", "names", "env")

    def __init__(self, kind, names, env=None):
        self.kind = kind
        self.names = list(names)
        self.env = env


# Terminators (flat IR).
class Jump(Stmt):
    __slots__ = ("target",)

    def __init__(self, target):
        self.target = target


class Branch(Stmt):
    """if (cond) goto t else goto f."""

    __slots__ = ("cond", "t", "f")

    def __init__(self, cond, t, f):
        self.cond = cond
        self.t = t
        self.f = f


class SwitchTerm(Stmt):
    __slots__ = ("disc", "cases", "default")

    def __init__(self, disc, cases, default):
        self.disc = disc
        self.cases = cases  # [(Expr, target)]
        self.default = default


class Unreachable(Stmt):
    __slots__ = ()


# Structured statements.
class If(Stmt):
    __slots__ = ("cond", "then", "els")

    def __init__(self, cond, then, els):
        self.cond = cond
        self.then = then
        self.els = els


class Loop(Stmt):
    """kind: 'for' (infinite), 'while', 'dowhile'. label: str or None."""

    __slots__ = ("kind", "cond", "body", "label", "used_label", "update")

    def __init__(self, body, label):
        self.kind = "for"
        self.cond = None
        self.body = body
        self.label = label
        self.used_label = False
        self.update = None


class Break(Stmt):
    __slots__ = ("label", "target")

    def __init__(self, label, target=None):
        self.label = label
        self.target = target


class Continue(Stmt):
    __slots__ = ("label", "target")

    def __init__(self, label, target=None):
        self.label = label
        self.target = target


class Switch(Stmt):
    """cases: list of ([case Exprs or None for default], body)."""

    __slots__ = ("disc", "cases", "label", "used_label")

    def __init__(self, disc, cases, label):
        self.disc = disc
        self.cases = cases
        self.label = label
        self.used_label = False


class Try(Stmt):
    __slots__ = ("body", "param", "handler")

    def __init__(self, body, param, handler):
        self.body = body
        self.param = param
        self.handler = handler


class Labeled(Stmt):
    __slots__ = ("label", "body", "used_label")

    def __init__(self, label, body):
        self.label = label
        self.body = body
        self.used_label = False


class ForIn(Stmt):
    __slots__ = ("kind", "target", "obj", "body", "label", "used_label")

    def __init__(self, kind, target, obj, body, label):
        self.kind = kind  # 'in' / 'of'
        self.target = target
        self.obj = obj
        self.body = body
        self.label = label
        self.used_label = False


# ---------------------------------------------------------------------------
# Generic traversal helpers
# ---------------------------------------------------------------------------


def walk_expr(e):
    """Yield e and all sub-expressions (pre-order), not entering functions."""
    stack = [e]
    while stack:
        x = stack.pop()
        yield x
        ch = x.children()
        if isinstance(x, Assign) and not isinstance(x.target, Member):
            yield x.target
        stack.extend(reversed(ch))


def stmt_exprs(s):
    """Top-level expressions of a statement."""
    if isinstance(s, SetReg):
        return [s.value]
    if isinstance(s, (ExprStmt, Return, Throw)):
        return [s.e] if s.e is not None else []
    if isinstance(s, Branch):
        return [s.cond]
    if isinstance(s, SwitchTerm):
        return [s.disc] + [c for c, _ in s.cases]
    if isinstance(s, If):
        return [s.cond]
    if isinstance(s, Loop):
        return [x for x in (s.cond, s.update) if x is not None]
    if isinstance(s, Switch):
        out = [s.disc]
        for exprs, _ in s.cases:
            out.extend(e for e in exprs if e is not None)
        return out
    if isinstance(s, ForIn):
        return [s.target, s.obj]
    return []


def child_blocks(s):
    if isinstance(s, If):
        return [s.then, s.els]
    if isinstance(s, (Loop, Labeled, ForIn)):
        return [s.body]
    if isinstance(s, Switch):
        return [b for _, b in s.cases]
    if isinstance(s, Try):
        return [s.body, s.handler]
    return []


def walk_stmts(stmts):
    """Yield all statements recursively (pre-order), not entering functions."""
    for s in stmts:
        yield s
        for b in child_blocks(s):
            yield from walk_stmts(b)


def map_stmt_exprs(s, fn):
    """Replace the top-level expressions of statement s in place."""
    if isinstance(s, SetReg):
        s.value = fn(s.value)
    elif isinstance(s, (ExprStmt, Return, Throw)):
        if s.e is not None:
            s.e = fn(s.e)
    elif isinstance(s, Branch):
        s.cond = fn(s.cond)
    elif isinstance(s, SwitchTerm):
        s.disc = fn(s.disc)
    elif isinstance(s, If):
        s.cond = fn(s.cond)
    elif isinstance(s, Loop):
        if s.cond is not None:
            s.cond = fn(s.cond)
        if s.update is not None:
            s.update = fn(s.update)
    elif isinstance(s, Switch):
        s.disc = fn(s.disc)
    elif isinstance(s, ForIn):
        s.obj = fn(s.obj)


def transform(e, fn):
    """Bottom-up rewrite of expression e with fn."""
    e = e.replace_children(lambda c: transform(c, fn))
    return fn(e)


def negate(e):
    """Logical negation in a boolean context."""
    if isinstance(e, Unary) and e.op == "!":
        return e.e
    if isinstance(e, Binary):
        inv = {"===": "!==", "!==": "===", "==": "!=", "!=": "=="}.get(e.op)
        if inv:
            return Binary(inv, e.l, e.r)
    if isinstance(e, Logical) and e.op in ("&&", "||"):
        return Logical("||" if e.op == "&&" else "&&", negate(e.l), negate(e.r))
    if isinstance(e, Lit) and isinstance(e.v, bool):
        return Lit(not e.v)
    return Unary("!", e)


def simplify_bool(e):
    """Simplify an expression used as a branch condition."""
    while isinstance(e, Unary) and e.op == "!" and isinstance(e.e, Unary) and e.e.op == "!":
        e = e.e.e
    return e


# ---------------------------------------------------------------------------
# Printer
# ---------------------------------------------------------------------------


def format_number(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if math.isnan(v):
        return "NaN"
    if math.isinf(v):
        return "Infinity" if v > 0 else "-Infinity"
    if v == 0 and math.copysign(1, v) < 0:
        return "-0"
    if v == int(v) and abs(v) < 1e21:
        return str(int(v))
    r = repr(v)
    if "e" in r:
        mant, exp = r.split("e")
        r = "%se%s" % (mant, exp.lstrip("+") if not exp.startswith("-") else exp)
        if "e" in r and not r.split("e")[1].startswith("-"):
            r = r.replace("e", "e+")
    return r


def quote_string(s):
    out = json.dumps(s, ensure_ascii=False)
    # JSON allows U+2028/2029 raw; escape them for older JS engines.
    out = out.replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    # Lone surrogates survive json.dumps as escapes only with ensure_ascii.
    try:
        out.encode("utf-8")
    except UnicodeEncodeError:
        out = json.dumps(s, ensure_ascii=True)
    return out


class Printer:
    def __init__(self, func_printer=None, indent_unit="  "):
        # func_printer(FuncExpr, indent) -> str
        self.func_printer = func_printer
        self.unit = indent_unit

    # ---- expressions ----------------------------------------------------
    def expr(self, e, indent=0, min_prec=0):
        s, p = self._expr(e, indent)
        if p < min_prec:
            return "(" + s + ")"
        return s

    def _expr(self, e, ind):
        if isinstance(e, Reg):
            return "r%d" % e.n, PREC_PRIMARY
        if isinstance(e, Name):
            return e.name, PREC_PRIMARY
        if isinstance(e, Lit):
            return self._lit(e.v)
        if isinstance(e, Raw):
            return e.text, e.prec
        if isinstance(e, Member):
            obj = self.expr(e.obj, ind, PREC_NEW)
            if isinstance(e.obj, Lit) and isinstance(e.obj.v, (int, float)) and not isinstance(e.obj.v, bool):
                obj = "(" + obj + ")"
            if isinstance(e.obj, (New,)) and not e.obj.args:
                obj = "(" + obj + ")"
            if isinstance(e.key, Lit) and is_identifier(e.key.v):
                return obj + "." + e.key.v, PREC_MEMBER
            return obj + "[" + self.expr(e.key, ind) + "]", PREC_MEMBER
        if isinstance(e, Call):
            callee = self.expr(e.callee, ind, PREC_NEW)
            if isinstance(e.callee, FuncExpr):
                callee = "(" + callee + ")"
            return callee + "(" + self._args(e.args, ind) + ")", PREC_CALL
        if isinstance(e, New):
            callee = self.expr(e.callee, ind, PREC_MEMBER)
            if isinstance(e.callee, Call) or _contains_call_head(e.callee):
                callee = "(" + callee + ")"
            return "new " + callee + "(" + self._args(e.args, ind) + ")", PREC_NEW
        if isinstance(e, Unary):
            inner = self.expr(e.e, ind, PREC_UNARY)
            if e.op[-1].isalpha():
                return e.op + " " + inner, PREC_UNARY
            if (e.op in ("-", "+") and inner.startswith(e.op)) or (
                e.op == "-" and inner.startswith("--")
            ):
                inner = "(" + inner + ")"
            return e.op + inner, PREC_UNARY
        if isinstance(e, Binary):
            p = BINARY_PREC[e.op]
            if e.op == "**":
                l = self.expr(e.l, ind, PREC_POSTFIX)
                r = self.expr(e.r, ind, p)
            else:
                l = self.expr(e.l, ind, p)
                r = self.expr(e.r, ind, p + 1)
            return "%s %s %s" % (l, e.op, r), p
        if isinstance(e, Logical):
            p = BINARY_PREC[e.op]
            l = self.expr(e.l, ind, p)
            r = self.expr(e.r, ind, p + 1)
            # ?? cannot be mixed with && / || without parentheses.
            if e.op == "??" or (isinstance(e.l, Logical) and (e.l.op == "??") != (e.op == "??")):
                if isinstance(e.l, Logical) and e.l.op != e.op:
                    l = "(" + l + ")"
            if isinstance(e.r, Logical) and (e.r.op == "??") != (e.op == "??"):
                if not r.startswith("("):
                    r = "(" + r + ")"
            return "%s %s %s" % (l, e.op, r), p
        if isinstance(e, Cond):
            c = self.expr(e.c, ind, PREC_NULLISH)
            a = self.expr(e.a, ind, PREC_ASSIGN)
            b = self.expr(e.b, ind, PREC_ASSIGN)
            return "%s ? %s : %s" % (c, a, b), PREC_COND
        if isinstance(e, Seq):
            return ", ".join(self.expr(x, ind, PREC_ASSIGN) for x in e.exprs), PREC_SEQ
        if isinstance(e, Assign):
            t = self.expr(e.target, ind, PREC_POSTFIX)
            v = self.expr(e.value, ind, PREC_ASSIGN)
            return "%s = %s" % (t, v), PREC_ASSIGN
        if isinstance(e, ObjectLit):
            return self._object(e, ind), PREC_PRIMARY
        if isinstance(e, ArrayLit):
            parts = []
            for el in e.elems:
                if el is None:
                    parts.append("")
                elif isinstance(el, Spread):
                    parts.append("..." + self.expr(el.e, ind, PREC_ASSIGN))
                else:
                    parts.append(self.expr(el, ind, PREC_ASSIGN))
            s = ", ".join(parts)
            if e.elems and e.elems[-1] is None:
                s += ","
            return "[" + s + "]", PREC_PRIMARY
        if isinstance(e, RegExpLit):
            pat = e.pattern if e.pattern else "(?:)"
            pat = _escape_regexp_source(pat)
            return "/" + pat + "/" + e.flags, PREC_PRIMARY
        if isinstance(e, FuncExpr):
            if self.func_printer:
                return self.func_printer(e, ind), PREC_ASSIGN
            return "function#%d" % e.fid, PREC_PRIMARY
        if isinstance(e, EnvRef):
            return "/*env*/undefined", PREC_PRIMARY
        if isinstance(e, TemplateLit):
            out = ["`"]
            for p in e.parts:
                if isinstance(p, str):
                    out.append(_template_escape(p))
                else:
                    out.append("${" + self.expr(p, ind) + "}")
            out.append("`")
            return "".join(out), PREC_PRIMARY
        return "/*?%s*/" % type(e).__name__, PREC_PRIMARY

    def _lit(self, v):
        if isinstance(v, str):
            return quote_string(v), PREC_PRIMARY
        if v is None:
            return "null", PREC_PRIMARY
        if v is UNDEFINED or v is EMPTY:
            return "undefined", PREC_PRIMARY
        if isinstance(v, bool):
            return ("true" if v else "false"), PREC_PRIMARY
        if isinstance(v, BigIntValue):
            if v.v < 0:
                return "-%dn" % -v.v, PREC_UNARY
            return "%dn" % v.v, PREC_PRIMARY
        s = format_number(v)
        if s.startswith("-"):
            return s, PREC_UNARY
        return s, PREC_PRIMARY

    def _args(self, args, ind):
        parts = []
        for a in args:
            if isinstance(a, Spread):
                parts.append("..." + self.expr(a.e, ind, PREC_ASSIGN))
            else:
                parts.append(self.expr(a, ind, PREC_ASSIGN))
        return ", ".join(parts)

    def _key(self, key):
        if isinstance(key, str):
            if is_identifier(key) or key in RESERVED and _IDENT_RE.match(key):
                return key
            return quote_string(key)
        if isinstance(key, (int, float)) and not isinstance(key, bool):
            s = format_number(key)
            if s.startswith("-") or s in ("NaN", "Infinity"):
                return "[" + s + "]"
            return s
        return quote_string(str(key))

    def _object(self, e, ind):
        if not e.props:
            return "{}"
        parts = []
        for kind, key, v in e.props:
            if kind == "init":
                k = self._key(key)
                if k == "__proto__":
                    k = '["__proto__"]'
                parts.append("%s: %s" % (k, self.expr(v, ind + 1, PREC_ASSIGN)))
            elif kind == "computed":
                parts.append(
                    "[%s]: %s"
                    % (self.expr(key, ind + 1, PREC_ASSIGN), self.expr(v, ind + 1, PREC_ASSIGN))
                )
            elif kind in ("get", "set") and isinstance(v, FuncExpr) and self.func_printer:
                text = self.func_printer(v, ind + 1, method=kind + " " + self._key(key))
                parts.append(text)
            elif kind == "proto":
                parts.append("__proto__: %s" % self.expr(v, ind + 1, PREC_ASSIGN))
            elif kind == "spread":
                parts.append("...%s" % self.expr(v, ind + 1, PREC_ASSIGN))
        one = "{" + ", ".join(parts) + "}"
        if len(one) <= 80 and "\n" not in one:
            return one
        pad = self.unit * (ind + 1)
        return "{\n" + ",\n".join(pad + p for p in parts) + "\n" + self.unit * ind + "}"

    # ---- statements -----------------------------------------------------
    def stmts(self, stmts, ind, out):
        for s in stmts:
            self.stmt(s, ind, out)

    def stmt(self, s, ind, out):
        pad = self.unit * ind
        if isinstance(s, SetReg):
            out.append(pad + "r%d = %s;" % (s.reg, self.expr(s.value, ind, PREC_ASSIGN)))
        elif isinstance(s, ExprStmt):
            text = self.expr(s.e, ind)
            if text.startswith(("{", "function", "class", "let [")):
                text = "(" + text + ")"
            out.append(pad + text + ";")
        elif isinstance(s, Return):
            if s.e is None:
                out.append(pad + "return;")
            else:
                out.append(pad + "return " + self.expr(s.e, ind) + ";")
        elif isinstance(s, Throw):
            out.append(pad + "throw " + self.expr(s.e, ind) + ";")
        elif isinstance(s, Comment):
            for line in s.text.split("\n"):
                out.append(pad + "// " + line)
        elif isinstance(s, Debugger):
            out.append(pad + "debugger;")
        elif isinstance(s, VarDecl):
            if s.names:
                out.append(pad + "%s %s;" % (s.kind, ", ".join(s.names)))
        elif isinstance(s, If):
            self._if(s, ind, out, pad)
        elif isinstance(s, Loop):
            label = (s.label + ": ") if s.used_label else ""
            if s.kind == "while":
                out.append(pad + label + "while (%s) {" % self.expr(s.cond, ind))
                self.stmts(s.body, ind + 1, out)
                out.append(pad + "}")
            elif s.kind == "dowhile":
                out.append(pad + label + "do {")
                self.stmts(s.body, ind + 1, out)
                out.append(pad + "} while (%s);" % self.expr(s.cond, ind))
            else:
                cond = self.expr(s.cond, ind) if s.cond is not None else ""
                upd = (" " + self.expr(s.update, ind)) if s.update is not None else ""
                if s.cond is None and s.update is None:
                    out.append(pad + label + "for (;;) {")
                else:
                    out.append(pad + label + "for (; %s;%s) {" % (cond, upd))
                self.stmts(s.body, ind + 1, out)
                out.append(pad + "}")
        elif isinstance(s, ForIn):
            label = (s.label + ": ") if s.used_label else ""
            out.append(
                pad
                + label
                + "for (%s %s %s) {"
                % (self.expr(s.target, ind), s.kind, self.expr(s.obj, ind, PREC_ASSIGN))
            )
            self.stmts(s.body, ind + 1, out)
            out.append(pad + "}")
        elif isinstance(s, Break):
            out.append(pad + ("break %s;" % s.label if s.label else "break;"))
        elif isinstance(s, Continue):
            out.append(pad + ("continue %s;" % s.label if s.label else "continue;"))
        elif isinstance(s, Switch):
            label = (s.label + ": ") if s.used_label else ""
            out.append(pad + label + "switch (%s) {" % self.expr(s.disc, ind))
            for exprs, body in s.cases:
                for c in exprs:
                    if c is None:
                        out.append(pad + self.unit + "default:")
                    else:
                        out.append(pad + self.unit + "case %s:" % self.expr(c, ind + 1))
                self.stmts(body, ind + 2, out)
            out.append(pad + "}")
        elif isinstance(s, Try):
            out.append(pad + "try {")
            self.stmts(s.body, ind + 1, out)
            out.append(pad + "} catch (%s) {" % s.param)
            self.stmts(s.handler, ind + 1, out)
            out.append(pad + "}")
        elif isinstance(s, Labeled):
            if s.used_label:
                out.append(pad + s.label + ": {")
                self.stmts(s.body, ind + 1, out)
                out.append(pad + "}")
            else:
                self.stmts(s.body, ind, out)
        elif isinstance(s, Jump):
            out.append(pad + "/* goto L%s */" % s.target)
        elif isinstance(s, Branch):
            out.append(
                pad + "/* if (%s) goto L%s else L%s */" % (self.expr(s.cond, ind), s.t, s.f)
            )
        elif isinstance(s, Unreachable):
            out.append(pad + "/* unreachable */")
        else:
            out.append(pad + "/* ? %s */" % type(s).__name__)

    def _if(self, s, ind, out, pad, prefix=""):
        out.append(pad + prefix + "if (%s) {" % self.expr(s.cond, ind))
        self.stmts(s.then, ind + 1, out)
        if s.els:
            if len(s.els) == 1 and isinstance(s.els[0], If):
                tmp = []
                self._if(s.els[0], ind, tmp, pad, prefix="} else ")
                out.extend(tmp)
                return
            out.append(pad + "} else {")
            self.stmts(s.els, ind + 1, out)
        out.append(pad + "}")


def _template_escape(s):
    q = quote_string(s)[1:-1]
    q = q.replace('\\"', '"')
    return q.replace("`", "\\`").replace("${", "\\${")


def _contains_call_head(e):
    """True if printing `new <e>(...)` would mis-associate a call in e."""
    while isinstance(e, Member):
        e = e.obj
    return isinstance(e, Call)


def _escape_regexp_source(p):
    # Escape forward slashes not already escaped and outside classes, and
    # line terminators.
    out = []
    in_class = False
    i = 0
    while i < len(p):
        c = p[i]
        if c == "\\" and i + 1 < len(p):
            out.append(p[i : i + 2])
            i += 2
            continue
        if c == "[":
            in_class = True
        elif c == "]":
            in_class = False
        elif c == "/" and not in_class:
            out.append("\\/")
            i += 1
            continue
        elif c == "\n":
            out.append("\\n")
            i += 1
            continue
        elif c == "\r":
            out.append("\\r")
            i += 1
            continue
        elif c == "\u2028":
            out.append("\\u2028")
            i += 1
            continue
        elif c == "\u2029":
            out.append("\\u2029")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)
