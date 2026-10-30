# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Instruction decoding and textual disassembly for HBC v98."""

import struct

from . import tables

_FMT = {
    "Reg8": "B",
    "Reg32": "I",
    "UInt8": "B",
    "UInt16": "H",
    "UInt32": "I",
    "Addr8": "b",
    "Addr32": "i",
    "Imm32": "i",
    "Double": "d",
}

OPCODE_BY_NAME = {name: i for i, (name, _) in enumerate(tables.OPCODES)}

# Precomputed per-opcode decode info: (name, operand types, struct fmt, size).
_DECODE = []
for _name, _ops in tables.OPCODES:
    _fmt = "<" + "".join(_FMT[t] for t in _ops)
    _DECODE.append((_name, _ops, _fmt, 1 + struct.calcsize(_fmt)))

# Operand indices (1-based) that are string IDs but are not annotated in the
# .def file.
_EXTRA_STRING_OPERANDS = {"DefineOwnById": [4]}

STRING_OPERANDS = dict(tables.STRING_OPERANDS)
for _k, _v in _EXTRA_STRING_OPERANDS.items():
    STRING_OPERANDS.setdefault(_k, _v)

FUNCTION_OPERANDS = dict(tables.FUNCTION_OPERANDS)
for _k in (
    "CreateBaseClass",
    "CreateBaseClassLongIndex",
):
    FUNCTION_OPERANDS.setdefault(_k, [4])
for _k in ("CreateDerivedClass", "CreateDerivedClassLongIndex"):
    FUNCTION_OPERANDS.setdefault(_k, [5])

TERMINATORS = {"Ret", "Throw", "Unreachable"}


class Instruction:
    __slots__ = ("offset", "op", "types", "args", "size", "targets", "table")

    def __init__(self, offset, op, types, args, size):
        self.offset = offset
        self.op = op
        self.types = types
        self.args = list(args)
        self.size = size
        # Absolute (function-relative) branch targets, for jumps & switches.
        self.targets = []
        # For switch instructions: list of (case value, target).
        self.table = None

    @property
    def next(self):
        return self.offset + self.size

    def is_unconditional_jump(self):
        return self.op in ("Jmp", "JmpLong")

    def is_switch(self):
        return self.op in ("UIntSwitchImm", "StringSwitchImm")

    def falls_through(self):
        return not (
            self.op in TERMINATORS or self.is_unconditional_jump() or self.is_switch()
        )

    def __repr__(self):
        return "<%d: %s %s>" % (self.offset, self.op, self.args)


def _align4(x):
    return (x + 3) & ~3


def decode_function(hbc, func):
    """Decode all instructions of `func. Returns [Instruction]."""
    data = hbc.data
    base = func.offset
    size = func.bytecodeSize
    end = size
    insns = []
    ip = 0
    while ip < end:
        opc = data[base + ip]
        if opc >= len(_DECODE):
            raise ValueError(
                "function %d: invalid opcode %d at offset %d" % (func.index, opc, ip)
            )
        name, types, fmt, isize = _DECODE[opc]
        if ip + isize > size:
            raise ValueError(
                "function %d: truncated instruction at offset %d" % (func.index, ip)
            )
        args = struct.unpack_from(fmt, data, base + ip + 1)
        ins = Instruction(ip, name, types, args, isize)
        if name == "UIntSwitchImm":
            _, tbl_rel, default_rel, lo, hi = args
            tstart = _align4(base + ip + tbl_rel) - base
            ins.table = []
            for k in range(hi - lo + 1):
                (rel,) = struct.unpack_from("<i", data, base + tstart + 4 * k)
                ins.table.append((lo + k, ip + rel))
            ins.targets = [ip + default_rel] + [t for _, t in ins.table]
            end = min(end, tstart)
        elif name == "StringSwitchImm":
            _, _, tbl_rel, default_rel, count = args
            tstart = _align4(base + ip + tbl_rel) - base
            ins.table = []
            for k in range(count):
                sid, rel = struct.unpack_from("<Ii", data, base + tstart + 8 * k)
                ins.table.append((sid, ip + rel))
            ins.targets = [ip + default_rel] + [t for _, t in ins.table]
            end = min(end, tstart)
        else:
            for t, v in zip(types, args):
                if t in ("Addr8", "Addr32"):
                    ins.targets.append(ip + v)
        insns.append(ins)
        ip += isize
    return insns


# ---- literal buffers ---------------------------------------------------------


class Undefined:
    def __repr__(self):
        return "undefined"


UNDEFINED = Undefined()


class StrRef:
    """A string-table reference found in a literal buffer."""

    __slots__ = ("sid",)

    def __init__(self, sid):
        self.sid = sid

    def __repr__(self):
        return "StrRef(%d)" % self.sid


def parse_literals(buf, offset, count):
    """Decode `count values starting at `offset of a serialized literal
    buffer. Values are StrRef, float/int, None (null), UNDEFINED or bool."""
    out = []
    i = offset
    while len(out) < count:
        tag = buf[i]
        i += 1
        if tag & 0x80:
            n = ((tag & 0x0F) << 8) | buf[i]
            i += 1
        else:
            n = tag & 0x0F
        n = min(n, count - len(out))
        kind = tag & 0x70
        if kind == 0x50:  # short string
            for _ in range(n):
                out.append(StrRef(struct.unpack_from("<H", buf, i)[0]))
                i += 2
        elif kind == 0x40:  # long string
            for _ in range(n):
                out.append(StrRef(struct.unpack_from("<I", buf, i)[0]))
                i += 4
        elif kind == 0x30:  # number
            for _ in range(n):
                out.append(struct.unpack_from("<d", buf, i)[0])
                i += 8
        elif kind == 0x70:  # integer
            for _ in range(n):
                out.append(struct.unpack_from("<i", buf, i)[0])
                i += 4
        elif kind == 0x00:
            out.extend([None] * n)
        elif kind == 0x60:
            out.extend([UNDEFINED] * n)
        elif kind == 0x10:
            out.extend([True] * n)
        elif kind == 0x20:
            out.extend([False] * n)
        if n == 0 and kind not in (0x00, 0x10, 0x20, 0x60):
            break
    return out


def object_literal(hbc, shape_idx, val_offset):
    """Return [(key, value)] for NewObjectWithBuffer operands."""
    key_off, nprops = hbc.shapes[shape_idx]
    keys = parse_literals(hbc.objKeyBuffer, key_off, nprops)
    vals = parse_literals(hbc.literalValueBuffer, val_offset, nprops)
    return list(zip(keys, vals))


def array_literal(hbc, count, val_offset):
    return parse_literals(hbc.literalValueBuffer, val_offset, count)


# ---- text disassembly ----------------------------------------------------------


def _fmt_literal(hbc, v):
    if isinstance(v, StrRef):
        return repr(hbc.string(v.sid))
    if v is None:
        return "null"
    if v is UNDEFINED:
        return "undefined"
    if v is True:
        return "true"
    if v is False:
        return "false"
    return repr(v)


def format_instruction(hbc, ins):
    parts = []
    sops = STRING_OPERANDS.get(ins.op, ())
    fops = FUNCTION_OPERANDS.get(ins.op, ())
    bops = tables.BIGINT_OPERANDS.get(ins.op, ())
    for n, (t, v) in enumerate(zip(ins.types, ins.args), start=1):
        if t.startswith("Reg"):
            parts.append("r%d" % v)
        elif t.startswith("Addr"):
            parts.append("L%d" % (ins.offset + v))
        elif n in sops:
            try:
                parts.append("%s" % _quote(hbc.string(v)))
            except Exception:
                parts.append("<string %d>" % v)
        elif n in fops:
            fn = hbc.functions[v] if v < len(hbc.functions) else None
            nm = hbc.function_name(fn) if fn else "?"
            parts.append("Function<%s>#%d" % (nm, v))
        elif n in bops:
            parts.append("%dn" % hbc.bigints[v])
        else:
            parts.append(repr(v))
    text = "%-28s %s" % (ins.op, ", ".join(parts))
    if ins.op in ("CallBuiltin", "CallBuiltinLong", "GetBuiltinClosure"):
        text += "    ; %s" % builtin_name(ins.args[1])
    elif ins.op in ("JmpBuiltinIs", "JmpBuiltinIsLong", "JmpBuiltinIsNot", "JmpBuiltinIsNotLong"):
        text += "    ; %s" % builtin_name(ins.args[1])
    elif ins.op in ("NewObjectWithBuffer", "NewObjectWithBufferLong"):
        props = object_literal(hbc, ins.args[1], ins.args[2])
        text += "    ; {%s}" % ", ".join(
            "%s: %s" % (_fmt_literal(hbc, k), _fmt_literal(hbc, v)) for k, v in props
        )
    elif ins.op == "NewObjectWithBufferAndParent":
        props = object_literal(hbc, ins.args[2], ins.args[3])
        text += "    ; {%s}" % ", ".join(
            "%s: %s" % (_fmt_literal(hbc, k), _fmt_literal(hbc, v)) for k, v in props
        )
    elif ins.op in ("NewArrayWithBuffer", "NewArrayWithBufferLong"):
        vals = array_literal(hbc, ins.args[2], ins.args[3])
        text += "    ; [%s]" % ", ".join(_fmt_literal(hbc, v) for v in vals)
    elif ins.op in ("TypeOfIs", "JmpTypeOfIs"):
        text += "    ; %s" % "|".join(typeof_is_names(ins.args[2]))
    if ins.table is not None:
        for val, tgt in ins.table:
            if ins.op == "StringSwitchImm":
                val = _quote(hbc.string(val))
            text += "\n%38s %s -> L%d" % ("", val, tgt)
    return text


def _quote(s):
    import json

    return json.dumps(s, ensure_ascii=False)


TYPEOF_IS_TYPES = [
    "undefined",
    "object",
    "string",
    "symbol",
    "boolean",
    "number",
    "bigint",
    "function",
    "null",
]


def typeof_is_names(raw):
    return [n for i, n in enumerate(TYPEOF_IS_TYPES) if raw & (1 << i)]


def builtin_name(idx):
    if 0 <= idx < len(tables.BUILTINS):
        return tables.BUILTINS[idx]
    return "<builtin %d>" % idx


def disassemble(hbc, out):
    """Write a full textual disassembly of `hbc to file object `out."""
    h = hbc.header
    out.write("Bytecode File Information:\n")
    out.write("  Bytecode version number: %d\n" % hbc.version)
    out.write("  Source hash: %s\n" % hbc.sourceHash.hex())
    out.write("  Function count: %d\n" % h["functionCount"])
    out.write("  String count: %d\n" % h["stringCount"])
    out.write("  BigInt count: %d\n" % h["bigIntCount"])
    out.write("  RegExp count: %d\n" % h["regExpCount"])
    out.write("  Segment ID: %d\n" % h["segmentID"])
    out.write("  CommonJS module count: %d\n" % h["cjsModuleCount"])
    out.write("  CommonJS modules statically resolved: %s\n" % hbc.cjsModulesStaticallyResolved)
    out.write("  Function source count: %d\n" % h["functionSourceCount"])
    out.write("  Global code index: %d\n\n" % h["globalCodeIndex"])
    if hbc.cjsModules:
        out.write("CommonJS Modules:\n")
        for a, b in hbc.cjsModules:
            name = a if hbc.cjsModulesStaticallyResolved else _quote(hbc.string(a))
            out.write("  %s -> function %d\n" % (name, b))
        out.write("\n")
    for f in hbc.functions:
        disassemble_function(hbc, f, out)


def disassemble_function(hbc, f, out):
    from .reader import FUNC_KIND_NAMES

    out.write(
        "Function<%s>#%d (params: %d, frame: %d, kind: %s%s, offset: 0x%x, size: %d)\n"
        % (
            hbc.function_name(f),
            f.index,
            f.paramCount,
            f.frameSize,
            FUNC_KIND_NAMES.get(f.kind, f.kind),
            ", strict" if f.strictMode else "",
            f.offset,
            f.bytecodeSize,
        )
    )
    try:
        insns = decode_function(hbc, f)
    except ValueError as e:
        out.write("  ; error: %s\n\n" % e)
        return
    labels = set()
    for ins in insns:
        labels.update(ins.targets)
    for s, e, t in f.exceptionHandlers:
        labels.update((s, e, t))
    for ins in insns:
        if ins.offset in labels:
            out.write("L%d:\n" % ins.offset)
        out.write("  %5d  %s\n" % (ins.offset, format_instruction(hbc, ins)))
    if f.exceptionHandlers:
        out.write("  Exception handlers:\n")
        for s, e, t in f.exceptionHandlers:
            out.write("    [L%d, L%d) -> L%d\n" % (s, e, t))
    out.write("\n")
