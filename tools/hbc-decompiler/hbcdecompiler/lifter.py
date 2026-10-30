# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Lift decoded HBC instructions into the flat register IR (jsast)."""

from . import disasm
from .disasm import StrRef
from .jsast import (
    EMPTY,
    UNDEFINED,
    ArrayLit,
    Assign,
    BigIntValue,
    Binary,
    Branch,
    Call,
    Comment,
    Debugger,
    EnvRef,
    Expr,
    ExprStmt,
    FuncExpr,
    Jump,
    Lit,
    Logical,
    Member,
    Name,
    ObjectLit,
    Raw,
    Reg,
    RegExpLit,
    Return,
    SetReg,
    SwitchTerm,
    Throw,
    Unary,
    Unreachable,
    VarDecl,
    hcall,
)

FRAME_EXTRA = 7  # StackFrameLayout::CallerExtraRegistersAtEnd

# ---------------------------------------------------------------------------
# Extra expression kinds used by the lifter
# ---------------------------------------------------------------------------


class CallT(Expr):
    """A call with an explicit `this` value. Simplified to a plain call or a
    method call when possible, otherwise printed as callee.call(this, ...)."""

    __slots__ = ("callee", "this", "args")

    def __init__(self, callee, this, args):
        self.callee = callee
        self.this = this
        self.args = list(args)

    def children(self):
        return (self.callee, self.this) + tuple(self.args)

    def replace_children(self, fn):
        return CallT(fn(self.callee), fn(self.this), [fn(a) for a in self.args])


class TryMember(Member):
    """Global variable read/write that throws ReferenceError if missing."""

    __slots__ = ()

    def replace_children(self, fn):
        return TryMember(fn(self.obj), fn(self.key))


class DefineProp(Expr):
    """Define an own data property (object literal semantics)."""

    __slots__ = ("obj", "key", "value", "enumerable")

    def __init__(self, obj, key, value, enumerable=True):
        self.obj = obj
        self.key = key
        self.value = value
        self.enumerable = enumerable

    def children(self):
        return (self.obj, self.key, self.value)

    def replace_children(self, fn):
        return DefineProp(fn(self.obj), fn(self.key), fn(self.value), self.enumerable)


class DefineAccessor(Expr):
    __slots__ = ("obj", "key", "getter", "setter", "enumerable")

    def __init__(self, obj, key, getter, setter, enumerable):
        self.obj = obj
        self.key = key
        self.getter = getter
        self.setter = setter
        self.enumerable = enumerable

    def children(self):
        return (self.obj, self.key, self.getter, self.setter)

    def replace_children(self, fn):
        return DefineAccessor(
            fn(self.obj), fn(self.key), fn(self.getter), fn(self.setter), self.enumerable
        )


class CoerceThis(Expr):
    """Sloppy-mode `this` coercion of a value."""

    __slots__ = ("e",)

    def __init__(self, e):
        self.e = e

    @property
    def pure(self):
        return self.e.pure

    def children(self):
        return (self.e,)

    def replace_children(self, fn):
        return CoerceThis(fn(self.e))


class CaughtValue(Expr):
    """The exception value at the start of a catch handler."""

    __slots__ = ()
    pure = True


class CreateThis(Expr):
    """`this` object created for a `new` call (CreateThisForNew)."""

    __slots__ = ("callee",)
    pure = True

    def __init__(self, callee):
        self.callee = callee

    def children(self):
        return (self.callee,)

    def replace_children(self, fn):
        return CreateThis(fn(self.callee))


class ConstructT(Expr):
    """Construct call with an explicit `this` (from CreateThisForNew)."""

    __slots__ = ("callee", "this", "args")

    def __init__(self, callee, this, args):
        self.callee = callee
        self.this = this
        self.args = list(args)

    def children(self):
        return (self.callee, self.this) + tuple(self.args)

    def replace_children(self, fn):
        return ConstructT(fn(self.callee), fn(self.this), [fn(a) for a in self.args])


class SelectObj(Expr):
    __slots__ = ("this", "ret")

    def __init__(self, this, ret):
        self.this = this
        self.ret = ret

    def children(self):
        return (self.this, self.ret)

    def replace_children(self, fn):
        return SelectObj(fn(self.this), fn(self.ret))


# ---------------------------------------------------------------------------
# Environments
# ---------------------------------------------------------------------------


class EnvName(Name):
    """A variable in a lexical environment; its name is resolved lazily so
    that environments can still be unified after lifting."""

    __slots__ = ("env", "slot")

    def __init__(self, env, slot):
        self.env = env
        self.slot = slot
        self.kind = "env"

    @property
    def name(self):
        return self.env.slot_name(self.slot)

    def __eq__(self, other):
        return isinstance(other, Name) and other.name == self.name

    def __hash__(self):
        return hash(("name", self.name))


class Env:
    """A lexical environment created by some function."""

    def __init__(self, eid, owner, parent, size, kind):
        self.eid = eid
        self.owner = owner  # function index
        self.parent = parent  # Env or None
        self.size = size
        self.kind = kind  # 'function', 'scope', 'toplevel'
        self.hoist = True
        # Union-find representative: environments of the same function body
        # created at several sites (e.g. after inlining) share variable names.
        self.rep = self

    def find(self):
        e = self
        while e.rep is not e:
            e = e.rep
        return e

    def slot_name(self, k):
        return "e%d_%d" % (self.find().eid, k)

    def __repr__(self):
        return "Env(%d)" % self.eid


class ClosureVal:
    __slots__ = ("fid",)

    def __init__(self, fid):
        self.fid = fid


# ---------------------------------------------------------------------------
# Basic blocks
# ---------------------------------------------------------------------------


class Block:
    def __init__(self, bid, start):
        self.id = bid
        self.start = start
        self.end = start
        self.insns = []
        self.stmts = []
        self.term = None
        self.succs = []
        self.preds = []
        # Exception handler block ids covering this block, outermost first.
        self.handlers = []

    @property
    def handler(self):
        return self.handlers[-1] if self.handlers else None

    def __repr__(self):
        return "B%d@%d" % (self.id, self.start)


def build_blocks(func, insns):
    if not insns:
        return [], {}
    size = insns[-1].next
    leaders = {0}
    by_off = {i.offset: i for i in insns}
    for ins in insns:
        if ins.targets:
            leaders.update(ins.targets)
            leaders.add(ins.next)
        elif not ins.falls_through():
            leaders.add(ins.next)
    for s, e, t in func.exceptionHandlers:
        leaders.update((s, e, t))
    leaders = sorted(l for l in leaders if l in by_off)
    blocks = []
    off2block = {}
    for i, l in enumerate(leaders):
        b = Block(i, l)
        blocks.append(b)
        off2block[l] = b
    bi = -1
    for ins in insns:
        if ins.offset in off2block:
            bi = off2block[ins.offset].id
        blocks[bi].insns.append(ins)
        blocks[bi].end = ins.next
    # Exception handler coverage: the table lists inner handlers first.
    for b in blocks:
        cover = []
        for s, e, t in func.exceptionHandlers:
            if s <= b.start < e and t in off2block:
                cover.append(off2block[t].id)
        b.handlers = list(reversed(cover))
    del size
    return blocks, off2block


# ---------------------------------------------------------------------------
# The lifter
# ---------------------------------------------------------------------------

BINOPS = {
    "Eq": "==",
    "StrictEq": "===",
    "Neq": "!=",
    "StrictNeq": "!==",
    "Less": "<",
    "LessEq": "<=",
    "Greater": ">",
    "GreaterEq": ">=",
    "Add": "+",
    "AddN": "+",
    "AddS": "+",
    "Mul": "*",
    "MulN": "*",
    "Div": "/",
    "DivN": "/",
    "Mod": "%",
    "Sub": "-",
    "SubN": "-",
    "LShift": "<<",
    "RShift": ">>",
    "URshift": ">>>",
    "BitAnd": "&",
    "BitXor": "^",
    "BitOr": "|",
    "IsIn": "in",
}

# Conditional jumps: name -> (operator, negated)
CMP_JUMPS = {
    "JLess": ("<", False),
    "JNotLess": ("<", True),
    "JLessN": ("<", False),
    "JNotLessN": ("<", True),
    "JLessEqual": ("<=", False),
    "JNotLessEqual": ("<=", True),
    "JLessEqualN": ("<=", False),
    "JNotLessEqualN": ("<=", True),
    "JGreater": (">", False),
    "JNotGreater": (">", True),
    "JGreaterEqual": (">=", False),
    "JNotGreaterEqual": (">=", True),
    "JEqual": ("==", False),
    "JNotEqual": ("==", True),
    "JStrictEqual": ("===", False),
    "JStrictNotEqual": ("===", True),
}
for _k in list(CMP_JUMPS):
    CMP_JUMPS[_k + "Long"] = CMP_JUMPS[_k]

BUILTIN_EXPR = {}


def builtin_expr(idx):
    name = disasm.builtin_name(idx)
    obj, _, meth = name.partition(".")
    if obj == "globalThis":
        return Name(meth, "builtin")
    if obj == "HermesBuiltin":
        return Member(Name("$hbc", "helper"), Lit(meth))
    return Member(Name(obj, "builtin"), Lit(meth))


def typeof_is_expr(e, mask):
    names = disasm.typeof_is_names(mask)
    conds = []
    has_obj = "object" in names
    has_null = "null" in names
    for n in names:
        if n == "null":
            if not has_obj:
                conds.append(Binary("===", e, Lit(None)))
            continue
        if n == "object" and not has_null:
            conds.append(
                Logical(
                    "&&",
                    Binary("===", Unary("typeof", e), Lit("object")),
                    Binary("!==", e, Lit(None)),
                )
            )
            continue
        conds.append(Binary("===", Unary("typeof", e), Lit(n)))
    if not conds:
        return Lit(False)
    out = conds[0]
    for c in conds[1:]:
        out = Logical("||", out, c)
    return out


class FunctionLifter:
    """Lifts one function. `dec` is the decompiler (shared state)."""

    def __init__(self, dec, func):
        self.dec = dec
        self.hbc = dec.hbc
        self.func = func
        self.fid = func.index
        self.frame = func.frameSize
        self.insns = disasm.decode_function(self.hbc, func)
        self.blocks, self.off2block = build_blocks(func, self.insns)
        self.uses_arguments = False
        self.max_param = func.paramCount - 1
        self.envs_created = []
        # Environments are keyed by creation site and shared across
        # re-processing of the same function.
        self.created_envs = dec.created_envs.setdefault(func.index, {})
        self.unknown_env = False
        # Child functions created here: fid -> Env or None.
        self.children = {}

    # ---- helpers -------------------------------------------------------
    def s(self, sid):
        return self.hbc.string(sid)

    def arg_reg(self, i):
        """Register holding outgoing call argument i (0 is `this`)."""
        return self.frame - FRAME_EXTRA - 1 - i

    def call_args(self, n):
        """(this, [args]) for an outgoing call with n arguments incl. this."""
        this = Reg(self.arg_reg(0))
        return this, [Reg(self.arg_reg(i)) for i in range(1, n)]

    def param(self, i):
        if i == 0:
            return Name("this", "this")
        if i < self.func.paramCount or self.fid in self.dec.generator_inner:
            self.max_param = max(self.max_param, i)
            return Name("a%d" % (i - 1), "param")
        # Not a declared parameter (e.g. one with a default value): declaring
        # it would change the function's `length`.
        self.uses_arguments = True
        return Member(Name("arguments", "arguments"), Lit(i - 1))

    def key(self, sid):
        return Lit(self.s(sid))

    def block_target(self, off):
        b = self.off2block.get(off)
        if b is None:
            raise ValueError("function %d: jump to invalid offset %d" % (self.fid, off))
        return b.id

    # ---- environment analysis ------------------------------------------
    def analyze_envs(self, closure_env):
        for _ in range(4):
            self.env_slots_changed = False
            res = self._analyze_envs(closure_env)
            if not self.env_slots_changed:
                break
        return res

    def _analyze_envs(self, closure_env):
        """Forward dataflow computing env/closure values held by registers
        before each instruction. Returns {insn offset: {reg: value}}."""
        blocks = self.blocks
        if not blocks:
            return {}
        succ = {b.id: set() for b in blocks}
        for b in blocks:
            last = b.insns[-1]
            for t in last.targets:
                if t in self.off2block:
                    succ[b.id].add(self.off2block[t].id)
            if last.falls_through() and b.id + 1 < len(blocks):
                succ[b.id].add(b.id + 1)
            for h in b.handlers:
                succ[b.id].add(h)
        created = self.created_envs  # insn offset -> Env

        def make_env(ins, parent, size, kind):
            env = created.get(ins.offset)
            if env is None:
                env = Env(self.dec.new_env_id(), self.fid, parent, size, kind)
                created[ins.offset] = env
            else:
                env.parent = parent
            if env not in self.envs_created:
                self.envs_created.append(env)
            return env

        def walk(env, n):
            while env is not None and n > 0:
                env = env.parent
                n -= 1
            return env

        env_slots = self.dec.env_slots
        in_state = {0: {}}
        before = {}
        work = [0]
        visits = {}
        while work:
            bid = work.pop()
            visits[bid] = visits.get(bid, 0) + 1
            if visits[bid] > 50:
                continue
            state = dict(in_state[bid])
            b = blocks[bid]
            for ins in b.insns:
                before[ins.offset] = dict(state)
                op, a = ins.op, ins.args
                val = None
                defines = _defined_regs(ins)
                if op == "CreateFunctionEnvironment":
                    val = make_env(ins, closure_env, a[1], "function")
                elif op == "CreateTopLevelEnvironment":
                    val = make_env(ins, None, a[1], "toplevel")
                elif op == "CreateEnvironment":
                    p = state.get(a[1])
                    val = make_env(ins, p if isinstance(p, Env) else None, a[2], "scope")
                elif op == "GetParentEnvironment":
                    val = walk(closure_env, a[1])
                elif op == "GetEnvironment":
                    p = state.get(a[1])
                    val = walk(p, a[2]) if isinstance(p, Env) else None
                elif op == "GetClosureEnvironment":
                    c = state.get(a[1])
                    if isinstance(c, ClosureVal):
                        val = self.children.get(c.fid) or self.dec.closure_env.get(c.fid)
                elif op in ("Mov", "MovLong"):
                    val = state.get(a[1])
                elif op in ("LoadFromEnvironment", "LoadFromEnvironmentL"):
                    e = state.get(a[1])
                    if isinstance(e, Env):
                        val = env_slots.get((e.eid, a[2]))
                        if val is None:
                            val = self.dec.closure_slots.get((e.eid, a[2])) or None
                elif op in (
                    "StoreToEnvironment",
                    "StoreToEnvironmentL",
                    "StoreNPToEnvironment",
                    "StoreNPToEnvironmentL",
                ):
                    e = state.get(a[0])
                    v = state.get(a[2])
                    if isinstance(e, Env) and isinstance(v, Env):
                        if env_slots.get((e.eid, a[1])) is not v:
                            env_slots[(e.eid, a[1])] = v
                            self.dec.env_container[v.eid] = e
                            self.env_slots_changed = True
                    elif isinstance(e, Env) and isinstance(v, ClosureVal):
                        old = self.dec.closure_slots.get((e.eid, a[1]))
                        if old is None:
                            self.dec.closure_slots[(e.eid, a[1])] = v
                            self.env_slots_changed = True
                        elif old is not False and old.fid != v.fid:
                            self.dec.closure_slots[(e.eid, a[1])] = False
                elif op in (
                    "CreateClosure",
                    "CreateClosureLongIndex",
                    "CreateGenerator",
                    "CreateGeneratorLongIndex",
                ):
                    p = state.get(a[1])
                    env = p if isinstance(p, Env) else None
                    if a[2] not in self.children or self.children[a[2]] is None:
                        self.children[a[2]] = env
                    val = ClosureVal(a[2])
                elif op in ("CreateBaseClass", "CreateBaseClassLongIndex"):
                    p = state.get(a[2])
                    env = p if isinstance(p, Env) else None
                    if a[3] not in self.children or self.children[a[3]] is None:
                        self.children[a[3]] = env
                    val = ClosureVal(a[3])
                elif op in ("CreateDerivedClass", "CreateDerivedClassLongIndex"):
                    p = state.get(a[2])
                    env = p if isinstance(p, Env) else None
                    if a[4] not in self.children or self.children[a[4]] is None:
                        self.children[a[4]] = env
                    val = ClosureVal(a[4])
                for r in defines:
                    state.pop(r, None)
                if val is not None and defines:
                    state[defines[0]] = val
            for s in succ[bid]:
                old = in_state.get(s)
                if old is None:
                    in_state[s] = dict(state)
                    work.append(s)
                else:
                    merged = {
                        k: v
                        for k, v in old.items()
                        if k in state and (state[k] is v or _same_val(state[k], v))
                    }
                    if len(merged) != len(old):
                        in_state[s] = merged
                        work.append(s)
        self.env_at = before
        return before

    def env_of(self, ins, reg):
        v = self.env_at.get(ins.offset, {}).get(reg)
        return v if isinstance(v, Env) else None

    def env_var(self, ins, reg, slot):
        env = self.env_of(ins, reg)
        if env is None:
            self.unknown_env = True
            return Name("$unknownEnv_r%d_%d" % (reg, slot), "env")
        return EnvName(env, slot)

    # ---- main lifting --------------------------------------------------
    def lift(self, closure_env):
        self.closure_env = closure_env
        self.analyze_envs(closure_env)
        for b in self.blocks:
            out = []
            for ins in b.insns:
                stmts = self.lift_insn(ins, b)
                out.extend(stmts)
            # Split off the terminator.
            term = None
            if out and isinstance(
                out[-1], (Jump, Branch, SwitchTerm, Return, Throw, Unreachable)
            ):
                term = out.pop()
            if term is None:
                nxt = b.id + 1
                term = Jump(nxt) if nxt < len(self.blocks) else Unreachable()
            b.stmts = out
            b.term = term
        return self.blocks

    def lift_insn(self, ins, b):
        op = ins.op
        a = ins.args
        R = Reg
        nxt = None
        if ins.next in self.off2block:
            nxt = self.off2block[ins.next].id

        def set_(r, e):
            return [SetReg(r, e)]

        def br(cond, target_off):
            return [Branch(cond, self.block_target(target_off), nxt)]

        # ---- objects/arrays -------------------------------------------
        if op in ("NewObjectWithBuffer", "NewObjectWithBufferLong"):
            return set_(a[0], self.object_literal(a[1], a[2]))
        if op == "NewObjectWithBufferAndParent":
            lit = self.object_literal(a[2], a[3])
            lit.props.insert(0, ("proto", None, R(a[1])))
            return set_(a[0], lit)
        if op == "NewObject":
            return set_(a[0], ObjectLit([]))
        if op == "NewObjectWithParent":
            return set_(a[0], ObjectLit([("proto", None, R(a[1]))]))
        if op in ("NewArrayWithBuffer", "NewArrayWithBufferLong"):
            vals = disasm.array_literal(self.hbc, a[2], a[3])
            return set_(a[0], ArrayLit([self.lit(v) for v in vals]))
        if op == "NewArray":
            return set_(a[0], ArrayLit([None] * a[1]))
        if op == "NewFastArray":
            return set_(a[0], hcall("newFastArray", Lit(a[1])))
        if op == "FastArrayLength":
            return set_(a[0], Member(R(a[1]), Lit("length")))
        if op == "FastArrayLoad":
            return set_(a[0], hcall("fastArrayLoad", R(a[1]), R(a[2])))
        if op == "FastArrayStore":
            return [ExprStmt(hcall("fastArrayStore", R(a[0]), R(a[1]), R(a[2])))]
        if op == "FastArrayPush":
            return [ExprStmt(Call(Member(R(a[0]), Lit("push")), [R(a[1])]))]
        if op == "FastArrayAppend":
            return [ExprStmt(hcall("fastArrayAppend", R(a[0]), R(a[1])))]
        # ---- moves & arithmetic ---------------------------------------
        if op in ("Mov", "MovLong"):
            return set_(a[0], R(a[1]))
        if op == "Negate":
            return set_(a[0], Unary("-", R(a[1])))
        if op == "Not":
            return set_(a[0], Unary("!", R(a[1])))
        if op == "BitNot":
            return set_(a[0], Unary("~", R(a[1])))
        if op == "TypeOf":
            return set_(a[0], Unary("typeof", R(a[1])))
        if op in BINOPS:
            return set_(a[0], Binary(BINOPS[op], R(a[1]), R(a[2])))
        if op == "Inc":
            return set_(a[0], Binary("+", R(a[1]), Lit(1)))
        if op == "Dec":
            return set_(a[0], Binary("-", R(a[1]), Lit(1)))
        if op == "InstanceOf":
            return set_(a[0], Binary("instanceof", R(a[1]), R(a[2])))
        if op == "PrivateIsIn":
            return set_(a[0], hcall("privateIsIn", R(a[1]), R(a[2])))
        if op == "TypeOfIs":
            return set_(a[0], typeof_is_expr(R(a[1]), a[2]))
        # ---- environments ---------------------------------------------
        if op in (
            "GetParentEnvironment",
            "GetEnvironment",
            "GetClosureEnvironment",
        ):
            nxt_state = self.env_at.get(ins.next, None)
            env = None
            if nxt_state is not None:
                env = nxt_state.get(a[0])
            if env is None:
                env = self._env_after(ins)
            return set_(a[0], EnvRef(env if isinstance(env, Env) else None))
        if op in (
            "CreateFunctionEnvironment",
            "CreateTopLevelEnvironment",
            "CreateEnvironment",
        ):
            env = self.created_envs.get(ins.offset)
            names = [env.slot_name(k) for k in range(env.size)] if env else []
            return [VarDecl("let", names, env), SetReg(a[0], EnvRef(env))]
        if op in ("StoreToEnvironment", "StoreToEnvironmentL", "StoreNPToEnvironment", "StoreNPToEnvironmentL"):
            if self.env_of(ins, a[2]) is not None:
                # Storing an environment object; tracked statically.
                return []
            return [ExprStmt(Assign(self.env_var(ins, a[0], a[1]), R(a[2])))]
        if op in ("LoadFromEnvironment", "LoadFromEnvironmentL"):
            e = self.env_of(ins, a[1])
            if e is not None and isinstance(self.dec.env_slots.get((e.eid, a[2])), Env):
                return set_(a[0], EnvRef(self.dec.env_slots[(e.eid, a[2])]))
            return set_(a[0], self.env_var(ins, a[1], a[2]))
        # ---- globals --------------------------------------------------
        if op == "GetGlobalObject":
            return set_(a[0], Name("globalThis", "globalobj"))
        if op == "GetNewTarget":
            if self.fid == self.hbc.header["globalCodeIndex"]:
                return set_(a[0], Lit(UNDEFINED))
            return set_(a[0], Raw("new.target", 19))
        if op == "LoadParentNoTraps":
            return set_(a[0], Call(Member(Name("Object", "builtin"), Lit("getPrototypeOf")), [R(a[1])]))
        if op == "TypedLoadParent":
            return set_(a[0], Call(Member(Name("Object", "builtin"), Lit("getPrototypeOf")), [R(a[1])]))
        if op == "DeclareGlobalVar":
            self.dec.declared_globals.add(self.s(a[0]))
            return [VarDecl("var", [self.s(a[0])])] if _ident_ok(self.s(a[0])) else []
        # ---- property access ------------------------------------------
        if op in ("GetByIdShort", "GetById", "GetByIdLong"):
            return set_(a[0], Member(R(a[1]), self.key(a[3])))
        if op in ("TryGetById", "TryGetByIdLong"):
            return set_(a[0], TryMember(R(a[1]), self.key(a[3])))
        if op == "GetByIdWithReceiverLong":
            return set_(
                a[0],
                Call(
                    Member(Name("Reflect", "builtin"), Lit("get")),
                    [R(a[1]), self.key(a[4]), R(a[3])],
                ),
            )
        if op in ("PutByIdLoose", "PutByIdStrict", "PutByIdLooseLong", "PutByIdStrictLong"):
            return [ExprStmt(Assign(Member(R(a[0]), self.key(a[3])), R(a[1])))]
        if op in ("TryPutByIdLoose", "TryPutByIdStrict", "TryPutByIdLooseLong", "TryPutByIdStrictLong"):
            return [ExprStmt(Assign(TryMember(R(a[0]), self.key(a[3])), R(a[1])))]
        if op in ("PutOwnBySlotIdx", "PutOwnBySlotIdxLong"):
            return [ExprStmt(hcall("putSlot", R(a[0]), Lit(a[2]), R(a[1])))]
        if op in ("GetOwnBySlotIdx", "GetOwnBySlotIdxLong"):
            return set_(a[0], hcall("getSlot", R(a[1]), Lit(a[2])))
        if op in ("DefineOwnById", "DefineOwnByIdLong"):
            return [ExprStmt(DefineProp(R(a[0]), self.key(a[3]), R(a[1])))]
        if op in ("DefineOwnByIndex", "DefineOwnByIndexL", "DefineOwnInDenseArray", "DefineOwnInDenseArrayL"):
            return [ExprStmt(DefineProp(R(a[0]), Lit(a[2]), R(a[1])))]
        if op == "DefineOwnByVal":
            return [ExprStmt(DefineProp(R(a[0]), R(a[2]), R(a[1]), bool(a[3])))]
        if op == "GetByVal":
            return set_(a[0], Member(R(a[1]), R(a[2])))
        if op == "GetByIndex":
            return set_(a[0], Member(R(a[1]), Lit(a[2])))
        if op == "GetByValWithReceiver":
            return set_(
                a[0],
                Call(Member(Name("Reflect", "builtin"), Lit("get")), [R(a[1]), R(a[2]), R(a[3])]),
            )
        if op in ("PutByValLoose", "PutByValStrict"):
            return [ExprStmt(Assign(Member(R(a[0]), R(a[1])), R(a[2])))]
        if op == "PutByValWithReceiver":
            return [
                ExprStmt(
                    hcall(
                        "putWithReceiver" if not a[4] else "putWithReceiverStrict",
                        R(a[0]),
                        R(a[1]),
                        R(a[2]),
                        R(a[3]),
                    )
                )
            ]
        if op == "DelByVal":
            return set_(a[0], Unary("delete", Member(R(a[1]), R(a[2]))))
        if op == "AddOwnPrivateBySym":
            return [ExprStmt(hcall("addPrivate", R(a[0]), R(a[2]), R(a[1])))]
        if op == "GetOwnPrivateBySym":
            return set_(a[0], hcall("getPrivate", R(a[1]), R(a[3])))
        if op == "PutOwnPrivateBySym":
            return [ExprStmt(hcall("putPrivate", R(a[0]), R(a[3]), R(a[1])))]
        if op == "DefineOwnGetterSetterByVal":
            return [ExprStmt(DefineAccessor(R(a[0]), R(a[1]), R(a[2]), R(a[3]), bool(a[4])))]
        if op == "GetPNameList":
            # a0 = iterator state, a1 = object, a2 = index, a3 = size.
            return [
                SetReg(a[0], hcall("forInBegin", R(a[1]))),
                SetReg(a[2], Lit(0)),
                SetReg(a[3], Lit(0)),
            ]
        if op == "GetNextPName":
            return set_(a[0], hcall("forInNext", R(a[1])))
        # ---- calls ------------------------------------------------------
        if op in ("Call", "Construct"):
            this, args = self.call_args(a[2])
            if op == "Construct":
                return set_(a[0], ConstructT(R(a[1]), this, args))
            return set_(a[0], CallT(R(a[1]), this, args))
        if op == "Call1":
            return set_(a[0], CallT(R(a[1]), R(a[2]), []))
        if op == "Call2":
            return set_(a[0], CallT(R(a[1]), R(a[2]), [R(a[3])]))
        if op == "Call3":
            return set_(a[0], CallT(R(a[1]), R(a[2]), [R(a[3]), R(a[4])]))
        if op == "Call4":
            return set_(a[0], CallT(R(a[1]), R(a[2]), [R(a[3]), R(a[4]), R(a[5])]))
        if op == "CallWithNewTarget":
            this, args = self.call_args(a[3])
            return set_(a[0], hcall("callWithNewTarget", R(a[1]), R(a[2]), this, ArrayLit(args)))
        if op == "CallWithNewTargetLong":
            # The argument count is in a register; it is always loaded from a
            # constant just before the call.
            argc = self.const_before(ins, b, a[3])
            if not isinstance(argc, int) or isinstance(argc, bool):
                return [Comment("unsupported: CallWithNewTargetLong with a dynamic argument count")]
            this, args = self.call_args(argc)
            nt = self.const_before(ins, b, a[2])
            if nt is UNDEFINED:
                return set_(a[0], CallT(R(a[1]), this, args))
            return set_(a[0], hcall("callWithNewTarget", R(a[1]), R(a[2]), this, ArrayLit(args)))
        if op == "CallRequire":
            return set_(a[0], Call(R(a[1]), [Lit(a[2])]))
        if op in ("CallBuiltin", "CallBuiltinLong"):
            _, args = self.call_args(a[2])
            return self.builtin_call(a[0], a[1], args)
        if op == "GetBuiltinClosure":
            return set_(a[0], builtin_expr(a[1]))
        if op == "Ret":
            return [Return(R(a[0]))]
        if op == "Catch":
            return set_(a[0], CaughtValue())
        if op == "DirectEval":
            return set_(a[0], Call(Name("eval", "builtin"), [R(a[1])]))
        if op == "Throw":
            return [Throw(R(a[0]))]
        if op == "ThrowIfEmpty":
            return set_(a[0], R(a[1]))
        if op == "ThrowIfUndefined":
            return set_(a[0], hcall("throwIfUndefined", R(a[1])))
        if op == "ThrowIfThisInitialized":
            return [ExprStmt(hcall("throwIfThisInitialized", R(a[0])))]
        if op == "Debugger":
            return [Debugger()]
        if op in ("AsyncBreakCheck", "ProfilePoint"):
            return []
        if op == "Unreachable":
            return [Unreachable()]
        # ---- closures & classes ---------------------------------------
        if op in ("CreateClosure", "CreateClosureLongIndex"):
            return set_(a[0], FuncExpr(a[2]))
        if op in ("CreateGenerator", "CreateGeneratorLongIndex"):
            self.dec.generator_inner.add(a[2])
            return set_(a[0], hcall("createGenerator", FuncExpr(a[2])))
        if op in (
            "CreateBaseClass",
            "CreateBaseClassLongIndex",
            "CreateDerivedClass",
            "CreateDerivedClassLongIndex",
        ):
            if op.startswith("CreateBase"):
                cls = hcall("createClass", FuncExpr(a[3]), Lit(UNDEFINED))
            else:
                cls = hcall("createClass", FuncExpr(a[4]), R(a[3]))
            out = [SetReg(a[0], cls)]
            if a[1] != a[0]:
                out.append(SetReg(a[1], Member(Reg(a[0]), Lit("prototype"))))
            return out
        if op == "CreateThisForNew":
            return set_(a[0], CreateThis(R(a[1])))
        if op == "CreateThisForSuper":
            return set_(a[0], hcall("createThisForSuper", R(a[1]), R(a[2])))
        if op == "SelectObject":
            return set_(a[0], SelectObj(R(a[1]), R(a[2])))
        if op in ("LoadParam", "LoadParamLong"):
            return set_(a[0], self.param(a[1]))
        # ---- constants -------------------------------------------------
        if op == "LoadConstUInt8" or op == "LoadConstInt":
            return set_(a[0], Lit(a[1]))
        if op == "LoadConstDouble":
            v = a[1]
            if v == v and abs(v) < 2**53 and v == int(v) and not (v == 0 and str(v).startswith("-")):
                v = int(v)
            return set_(a[0], Lit(v))
        if op in ("LoadConstBigInt", "LoadConstBigIntLongIndex"):
            return set_(a[0], Lit(BigIntValue(self.hbc.bigints[a[1]])))
        if op in ("LoadConstString", "LoadConstStringLongIndex"):
            return set_(a[0], Lit(self.s(a[1])))
        if op == "LoadConstEmpty":
            return set_(a[0], Lit(EMPTY))
        if op == "LoadConstUndefined":
            return set_(a[0], Lit(UNDEFINED))
        if op == "LoadConstNull":
            return set_(a[0], Lit(None))
        if op == "LoadConstTrue":
            return set_(a[0], Lit(True))
        if op == "LoadConstFalse":
            return set_(a[0], Lit(False))
        if op == "LoadConstZero":
            return set_(a[0], Lit(0))
        if op == "CoerceThisNS":
            return set_(a[0], CoerceThis(R(a[1])))
        if op == "LoadThisNS":
            return set_(a[0], Name("this", "this"))
        if op == "ToNumber":
            return set_(a[0], Unary("+", R(a[1])))
        if op == "ToNumeric":
            return set_(a[0], hcall("toNumeric", R(a[1])))
        if op == "ToInt32":
            return set_(a[0], Binary("|", R(a[1]), Lit(0)))
        if op == "ToUint32":
            return set_(a[0], Binary(">>>", R(a[1]), Lit(0)))
        if op == "AddEmptyString":
            return set_(a[0], Binary("+", Lit(""), R(a[1])))
        if op == "CreatePrivateName":
            return set_(a[0], Call(Name("Symbol", "builtin"), [Lit(self.s(a[1]))]))
        if op in ("GetArgumentsPropByValLoose", "GetArgumentsPropByValStrict"):
            self.uses_arguments = True
            return set_(a[0], Member(Name("arguments", "arguments"), R(a[1])))
        if op == "GetArgumentsLength":
            self.uses_arguments = True
            return set_(a[0], Member(Name("arguments", "arguments"), Lit("length")))
        if op in ("ReifyArgumentsStrict", "ReifyArgumentsLoose"):
            self.uses_arguments = True
            return set_(a[0], Name("arguments", "arguments"))
        if op == "ToPropertyKey":
            return set_(a[0], R(a[1]))
        if op == "CreateRegExp":
            return set_(a[0], RegExpLit(self.s(a[1]), self.s(a[2])))
        if op == "UIntSwitchImm":
            cases = [(Lit(v), self.block_target(t)) for v, t in ins.table]
            return [SwitchTerm(R(a[0]), cases, self.block_target(ins.offset + a[2]))]
        if op == "StringSwitchImm":
            cases = [(Lit(self.s(v)), self.block_target(t)) for v, t in ins.table]
            return [SwitchTerm(R(a[0]), cases, self.block_target(ins.offset + a[3]))]
        if op == "IteratorBegin":
            return set_(a[0], hcall("iterBegin", R(a[1])))
        if op == "IteratorNext":
            return [
                SetReg(a[0], hcall("iterNext", R(a[1]))),
                SetReg(a[1], hcall("iterAlive", R(a[1]))),
            ]
        if op == "IteratorClose":
            return [ExprStmt(hcall("iterClose", R(a[0]), Lit(bool(a[1]))))]
        # ---- jumps -------------------------------------------------------
        if op in ("Jmp", "JmpLong"):
            return [Jump(self.block_target(ins.targets[0]))]
        if op in ("JmpTrue", "JmpTrueLong"):
            return br(R(a[1]), ins.targets[0])
        if op in ("JmpFalse", "JmpFalseLong"):
            return br(Unary("!", R(a[1])), ins.targets[0])
        if op in ("JmpUndefined", "JmpUndefinedLong"):
            return br(Binary("===", R(a[1]), Lit(UNDEFINED)), ins.targets[0])
        if op == "JmpTypeOfIs":
            return br(typeof_is_expr(R(a[1]), a[2]), ins.targets[0])
        if op in CMP_JUMPS:
            o, neg = CMP_JUMPS[op]
            c = Binary(o, R(a[1]), R(a[2]))
            return br(Unary("!", c) if neg else c, ins.targets[0])
        if op in ("JmpBuiltinIs", "JmpBuiltinIsLong"):
            return br(Binary("===", R(a[2]), builtin_expr(a[1])), ins.targets[0])
        if op in ("JmpBuiltinIsNot", "JmpBuiltinIsNotLong"):
            return br(Binary("!==", R(a[2]), builtin_expr(a[1])), ins.targets[0])
        return [Comment("unsupported instruction: " + disasm.format_instruction(self.hbc, ins))]

    def const_before(self, ins, b, reg, depth=0):
        """The constant held by `reg` just before `ins` (in block b), found by
        following moves backwards; None if unknown."""
        idx = b.insns.index(ins)
        for prev in reversed(b.insns[:idx]):
            if reg in _defined_regs(prev):
                v = _const_value(prev)
                if v is not None:
                    return v
                if prev.op in ("Mov", "MovLong") and depth < 16:
                    return self.const_before(prev, b, prev.args[1], depth + 1)
                return None
        # Not defined in this block: accept a register that only ever holds
        # one constant in the whole function.
        vals = set()
        for i in self.insns:
            if reg in _defined_regs(i):
                v = _const_value(i)
                if v is None:
                    return None
                vals.add(v if v is not UNDEFINED else "<undefined>")
        if len(vals) == 1:
            v = vals.pop()
            return UNDEFINED if v == "<undefined>" else v
        return None

    def _env_after(self, ins):
        # Fallback: recompute the value the instruction defines.
        op, a = ins.op, ins.args
        state = self.env_at.get(ins.offset, {})
        if op == "GetParentEnvironment":
            env = self.closure_env
            for _ in range(a[1]):
                env = env.parent if env else None
            return env
        if op == "GetEnvironment":
            env = state.get(a[1])
            for _ in range(a[2]):
                env = env.parent if isinstance(env, Env) else None
            return env
        if op == "GetClosureEnvironment":
            c = state.get(a[1])
            if isinstance(c, ClosureVal):
                return self.children.get(c.fid) or self.dec.closure_env.get(c.fid)
        return None

    def lit(self, v):
        if isinstance(v, StrRef):
            return Lit(self.s(v.sid))
        if v is disasm.UNDEFINED:
            return Lit(UNDEFINED)
        if isinstance(v, float) and v == v and abs(v) < 2**53 and v == int(v) and str(v) != "-0.0":
            v = int(v)
        return Lit(v)

    def object_literal(self, shape, voff):
        props = []
        for k, v in disasm.object_literal(self.hbc, shape, voff):
            key = self.s(k.sid) if isinstance(k, StrRef) else k
            if isinstance(key, float) and key == int(key):
                key = int(key)
            props.append(("init", key, self.lit(v)))
        return ObjectLit(props)

    def builtin_call(self, dst, idx, args):
        name = disasm.builtin_name(idx)
        obj, _, meth = name.partition(".")
        if obj == "HermesBuiltin":
            if meth == "copyRestArgs":
                self.uses_arguments = True
                return [
                    SetReg(
                        dst,
                        Call(
                            Member(
                                Member(Member(Name("Array", "builtin"), Lit("prototype")), Lit("slice")),
                                Lit("call"),
                            ),
                            [Name("arguments", "arguments")] + args,
                        ),
                    )
                ]
            if meth == "applyArguments":
                self.uses_arguments = True
                return [SetReg(dst, hcall("applyArguments", *(args + [Name("arguments", "arguments")])))]
            if meth == "exponentiationOperator" and len(args) == 2:
                return [SetReg(dst, Binary("**", args[0], args[1]))]
        return [SetReg(dst, Call(builtin_expr(idx), args))]


def _const_value(ins):
    op = ins.op
    if op in ("LoadConstUInt8", "LoadConstInt"):
        return ins.args[1]
    if op == "LoadConstDouble" and ins.args[1] == ins.args[1] and ins.args[1] == int(ins.args[1]):
        return int(ins.args[1])
    if op == "LoadConstZero":
        return 0
    if op == "LoadConstUndefined":
        return UNDEFINED
    return None


def _ident_ok(s):
    from .jsast import is_identifier

    return is_identifier(s)


def _same_val(a, b):
    return isinstance(a, ClosureVal) and isinstance(b, ClosureVal) and a.fid == b.fid


_DEF_CACHE = {}


def _defined_regs(ins):
    """Registers written by an instruction."""
    op = ins.op
    a = ins.args
    if op in _NO_DEF:
        return []
    if op == "GetPNameList":
        return [a[0], a[1], a[2], a[3]]
    if op == "GetNextPName":
        return [a[0], a[3]]
    if op == "IteratorBegin":
        return [a[0], a[1]]
    if op == "IteratorNext":
        return [a[0], a[1]]
    if op in ("CreateBaseClass", "CreateBaseClassLongIndex", "CreateDerivedClass", "CreateDerivedClassLongIndex"):
        return [a[0], a[1]]
    if ins.types and ins.types[0] in ("Reg8", "Reg32"):
        return [a[0]]
    return []


_NO_DEF = {
    "UIntSwitchImm",
    "StringSwitchImm",
    "FastArrayStore",
    "FastArrayPush",
    "FastArrayAppend",
    "StoreToEnvironment",
    "StoreToEnvironmentL",
    "StoreNPToEnvironment",
    "StoreNPToEnvironmentL",
    "PutByIdLoose",
    "PutByIdStrict",
    "PutByIdLooseLong",
    "PutByIdStrictLong",
    "TryPutByIdLoose",
    "TryPutByIdStrict",
    "TryPutByIdLooseLong",
    "TryPutByIdStrictLong",
    "PutOwnBySlotIdx",
    "PutOwnBySlotIdxLong",
    "DefineOwnById",
    "DefineOwnByIdLong",
    "DefineOwnByIndex",
    "DefineOwnByIndexL",
    "DefineOwnInDenseArray",
    "DefineOwnInDenseArrayL",
    "DefineOwnByVal",
    "PutByValLoose",
    "PutByValStrict",
    "PutByValWithReceiver",
    "AddOwnPrivateBySym",
    "PutOwnPrivateBySym",
    "DefineOwnGetterSetterByVal",
    "Ret",
    "Throw",
    "ThrowIfThisInitialized",
    "IteratorClose",
    "DeclareGlobalVar",
    "Debugger",
    "AsyncBreakCheck",
    "ProfilePoint",
    "Unreachable",
}
