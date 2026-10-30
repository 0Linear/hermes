# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Parser for Hermes bytecode (HBC) files, bytecode version 98.

The layout mirrors include/hermes/BCGen/HBC/BytecodeFileFormat.h and
lib/BCGen/HBC/BCProvider.cpp as of the last v98 commit.
"""

import struct

from . import tables

MAGIC = 0x1F1903C103BC1FC6
DELTA_MAGIC = (~MAGIC) & 0xFFFFFFFFFFFFFFFF
HEADER_SIZE = 128
SMALL_FUNC_HEADER_SIZE = 12
LARGE_FUNC_HEADER_SIZE = 36

HEADER_FIELDS = [
    "fileLength",
    "globalCodeIndex",
    "functionCount",
    "stringKindCount",
    "identifierCount",
    "stringCount",
    "overflowStringCount",
    "stringStorageSize",
    "bigIntCount",
    "bigIntStorageSize",
    "regExpCount",
    "regExpStorageSize",
    "literalValueBufferSize",
    "objKeyBufferSize",
    "objShapeTableCount",
    "numStringSwitchImms",
    "segmentID",
    "cjsModuleCount",
    "functionSourceCount",
    "debugInfoOffset",
]

FUNC_KIND_NAMES = {0: "normal", 1: "generator", 2: "async"}
PROHIBIT_NAMES = {0: "call", 1: "construct", 2: "none"}


class HBCError(Exception):
    """Raised for malformed or unsupported bytecode files."""


def _align(off, a=4):
    return (off + a - 1) & ~(a - 1)


class FunctionHeader:
    """Decoded (small or large) function header."""

    __slots__ = (
        "index",
        "offset",
        "paramCount",
        "loopDepth",
        "bytecodeSize",
        "functionName",
        "numberRegCount",
        "nonPtrRegCount",
        "frameSize",
        "readCacheSize",
        "writeCacheSize",
        "privateNameCacheSize",
        "prohibitInvoke",
        "strictMode",
        "hasExceptionHandler",
        "hasDebugInfo",
        "overflowed",
        "kind",
        "exceptionHandlers",
        "debugOffset",
    )

    def _set_flags(self, flags):
        self.prohibitInvoke = flags & 3
        self.strictMode = bool(flags & 4)
        self.hasExceptionHandler = bool(flags & 8)
        self.hasDebugInfo = bool(flags & 16)
        self.overflowed = bool(flags & 32)
        self.kind = (flags >> 6) & 3


class DebugLocation:
    __slots__ = ("address", "line", "column", "statement", "filename")

    def __init__(self, address, line, column, statement, filename):
        self.address = address
        self.line = line
        self.column = column
        self.statement = statement
        self.filename = filename


class HBCFile:
    """An in-memory, fully decoded HBC file."""

    def __init__(self, data):
        self.data = bytes(data)
        self._parse()

    # ---- low level helpers -------------------------------------------------
    def u8(self, off):
        return self.data[off]

    def u32(self, off):
        return struct.unpack_from("<I", self.data, off)[0]

    def _check(self, off, size, what):
        if off < 0 or off + size > len(self.data):
            raise HBCError("%s extends past end of file" % what)

    # ---- parsing -------------------------------------------------------------
    def _parse(self):
        d = self.data
        if len(d) < HEADER_SIZE:
            raise HBCError("file is smaller than an HBC header")
        magic, version = struct.unpack_from("<QI", d, 0)
        if magic == DELTA_MAGIC:
            raise HBCError("delta-prepped bytecode is not supported")
        if magic != MAGIC:
            raise HBCError("not a Hermes bytecode file (bad magic)")
        self.version = version
        if version != tables.BYTECODE_VERSION:
            raise HBCError(
                "unsupported bytecode version %d (this decompiler handles %d)"
                % (version, tables.BYTECODE_VERSION)
            )
        self.sourceHash = d[12:32]
        vals = struct.unpack_from("<20I", d, 32)
        self.header = dict(zip(HEADER_FIELDS, vals))
        opts = d[112]
        self.staticBuiltins = bool(opts & 1)
        self.cjsModulesStaticallyResolved = bool(opts & 2)
        h = self.header
        if h["fileLength"] > len(d):
            raise HBCError("file is truncated")

        off = HEADER_SIZE

        def take(count, size, what):
            nonlocal off
            off = _align(off)
            self._check(off, count * size, what)
            start = off
            off += count * size
            return start

        fh_off = take(h["functionCount"], SMALL_FUNC_HEADER_SIZE, "function headers")
        sk_off = take(h["stringKindCount"], 4, "string kinds")
        take(h["identifierCount"], 4, "identifier hashes")
        st_off = take(h["stringCount"], 4, "string table")
        ov_off = take(h["overflowStringCount"], 8, "overflow string table")
        ss_off = take(h["stringStorageSize"], 1, "string storage")
        lv_off = take(h["literalValueBufferSize"], 1, "literal value buffer")
        ok_off = take(h["objKeyBufferSize"], 1, "object key buffer")
        sh_off = take(h["objShapeTableCount"], 8, "object shape table")
        bt_off = take(h["bigIntCount"], 8, "bigint table")
        bs_off = take(h["bigIntStorageSize"], 1, "bigint storage")
        rt_off = take(h["regExpCount"], 8, "regexp table")
        rs_off = take(h["regExpStorageSize"], 1, "regexp storage")
        cj_off = take(h["cjsModuleCount"], 8, "CJS module table")
        fs_off = take(h["functionSourceCount"], 8, "function source table")

        self.literalValueBuffer = d[lv_off : lv_off + h["literalValueBufferSize"]]
        self.objKeyBuffer = d[ok_off : ok_off + h["objKeyBufferSize"]]

        self._parse_strings(sk_off, st_off, ov_off, ss_off)
        self.shapes = [
            struct.unpack_from("<II", d, sh_off + 8 * i)
            for i in range(h["objShapeTableCount"])
        ]
        self.bigints = []
        for i in range(h["bigIntCount"]):
            o, ln = struct.unpack_from("<II", d, bt_off + 8 * i)
            self.bigints.append(
                int.from_bytes(d[bs_off + o : bs_off + o + ln], "little", signed=True)
            )
        self.regexps = [
            struct.unpack_from("<II", d, rt_off + 8 * i) for i in range(h["regExpCount"])
        ]
        self.cjsModules = [
            struct.unpack_from("<II", d, cj_off + 8 * i)
            for i in range(h["cjsModuleCount"])
        ]
        self.functionSources = dict(
            struct.unpack_from("<II", d, fs_off + 8 * i)
            for i in range(h["functionSourceCount"])
        )
        self.functions = [
            self._parse_function_header(i, fh_off + SMALL_FUNC_HEADER_SIZE * i)
            for i in range(h["functionCount"])
        ]
        self._parse_debug_info()

    def _parse_strings(self, sk_off, st_off, ov_off, ss_off):
        d = self.data
        h = self.header
        self.isIdentifier = []
        for i in range(h["stringKindCount"]):
            e = self.u32(sk_off + 4 * i)
            kind = e >> 31
            count = e & 0x7FFFFFFF
            self.isIdentifier.extend([bool(kind)] * count)
        self.strings = []
        for i in range(h["stringCount"]):
            e = self.u32(st_off + 4 * i)
            is_utf16 = e & 1
            offset = (e >> 1) & 0x7FFFFF
            length = e >> 24
            if length == 0xFF:
                offset, length = struct.unpack_from("<II", d, ov_off + 8 * offset)
            start = ss_off + offset
            if is_utf16:
                raw = d[start : start + 2 * length]
                s = raw.decode("utf-16-le", errors="surrogatepass")
            else:
                s = d[start : start + length].decode("latin-1")
            self.strings.append(s)

    def _parse_function_header(self, index, off):
        d = self.data
        w1, w2, b1, b2, b3, flags = struct.unpack_from("<IIBBBB", d, off)
        fh = FunctionHeader()
        fh.index = index
        fh._set_flags(flags)
        fh.exceptionHandlers = []
        fh.debugOffset = None
        if fh.overflowed:
            large = ((w2 >> 14) & 0xFF) << 24 | (w1 & 0x1FFFFFF)
            self._check(large, LARGE_FUNC_HEADER_SIZE, "large function header")
            (
                fh.offset,
                fh.paramCount,
                fh.loopDepth,
                fh.bytecodeSize,
                fh.functionName,
                fh.numberRegCount,
                fh.nonPtrRegCount,
                fh.frameSize,
                fh.readCacheSize,
                fh.writeCacheSize,
                fh.privateNameCacheSize,
                lflags,
            ) = struct.unpack_from("<8I4B", d, large)
            fh._set_flags(lflags)
            p = large + LARGE_FUNC_HEADER_SIZE
            if fh.hasExceptionHandler:
                p = _align(p)
                count = self.u32(p)
                p += 4
                for j in range(count):
                    fh.exceptionHandlers.append(struct.unpack_from("<III", d, p))
                    p += 12
            if fh.hasDebugInfo:
                p = _align(p)
                v = self.u32(p)
                fh.debugOffset = None if v == 0xFFFFFFFF else v
        else:
            fh.offset = w1 & 0x1FFFFFF
            fh.paramCount = (w1 >> 25) & 0x1F
            fh.loopDepth = (w1 >> 30) & 3
            fh.bytecodeSize = w2 & 0x3FFF
            fh.functionName = (w2 >> 14) & 0xFF
            fh.numberRegCount = (w2 >> 22) & 0x1F
            fh.nonPtrRegCount = (w2 >> 27) & 0x1F
            fh.frameSize = b1
            fh.readCacheSize = b2
            fh.writeCacheSize = b3 & 0x7F
            fh.privateNameCacheSize = b3 >> 7
        self._check(fh.offset, fh.bytecodeSize, "function %d bytecode" % index)
        return fh

    # ---- debug info --------------------------------------------------------
    def _parse_debug_info(self):
        self.filenames = []
        self.fileRegions = []
        self.debugData = b""
        off = self.header["debugInfoOffset"]
        d = self.data
        if off == 0 or off + 16 > len(d):
            return
        fcount, fsize, rcount, dsize = struct.unpack_from("<4I", d, off)
        p = off + 16
        entries = [struct.unpack_from("<II", d, p + 8 * i) for i in range(fcount)]
        p += 8 * fcount
        storage = d[p : p + fsize]
        p += fsize
        for o, ln in entries:
            if ln & 0x80000000:
                ln &= 0x7FFFFFFF
                self.filenames.append(
                    storage[o : o + 2 * ln].decode("utf-16-le", errors="replace")
                )
            else:
                self.filenames.append(storage[o : o + ln].decode("latin-1"))
        for i in range(rcount):
            self.fileRegions.append(struct.unpack_from("<III", d, p))
            p += 12
        self.debugData = d[p : p + dsize]

    def _sleb(self, buf, pos):
        result = 0
        shift = 0
        while True:
            b = buf[pos]
            pos += 1
            result |= (b & 0x7F) << shift
            shift += 7
            if not b & 0x80:
                if b & 0x40:
                    result -= 1 << shift
                return result, pos

    def _filename_for_debug_offset(self, off):
        name = None
        for from_addr, fid, _ in self.fileRegions:
            if from_addr <= off:
                name = fid
            else:
                break
        if name is None or name >= len(self.filenames):
            return None
        return self.filenames[name]

    def debug_locations(self, func):
        """Return [DebugLocation] for a function (possibly empty)."""
        if func.debugOffset is None or func.debugOffset >= len(self.debugData):
            return []
        buf = self.debugData
        pos = func.debugOffset
        filename = self._filename_for_debug_offset(pos)
        try:
            _, pos = self._sleb(buf, pos)
            line, pos = self._sleb(buf, pos)
            col, pos = self._sleb(buf, pos)
            _, pos = self._sleb(buf, pos)
            locs = [DebugLocation(0, line, col, 0, filename)]
            addr = 0
            stmt = 0
            while True:
                ad, pos = self._sleb(buf, pos)
                if ad == -1:
                    break
                addr += ad
                ld, pos = self._sleb(buf, pos)
                if not ld & 1:
                    continue
                cd, pos = self._sleb(buf, pos)
                if ld & 2:
                    sd, pos = self._sleb(buf, pos)
                    stmt += sd
                if ld & 4:
                    _, pos = self._sleb(buf, pos)
                line += ld >> 3
                col += cd
                locs.append(DebugLocation(addr, line, col, stmt, filename))
            return locs
        except IndexError:
            return []

    # ---- accessors -----------------------------------------------------------
    def string(self, sid):
        if 0 <= sid < len(self.strings):
            return self.strings[sid]
        raise HBCError("string id %d out of range" % sid)

    def function_name(self, func):
        try:
            return self.string(func.functionName)
        except HBCError:
            return ""

    def bytecode(self, func):
        return self.data[func.offset : func.offset + func.bytecodeSize]

    def regexp_source(self, idx):
        """Regexp table entries only hold compiled regex bytecode; the pattern
        and flags strings are operands of CreateRegExp."""
        return self.regexps[idx] if idx < len(self.regexps) else None
