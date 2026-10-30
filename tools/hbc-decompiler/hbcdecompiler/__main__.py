# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Command line interface: python3 -m hbcdecompiler [options] file.hbc"""

import argparse
import struct
import sys
import threading

from . import disasm, reader
from .decompiler import Decompiler


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="hbc-decompile",
        description="Decompile a Hermes bytecode (HBC v98) file to JavaScript.",
    )
    ap.add_argument("input", help="input .hbc file")
    ap.add_argument("-o", "--output", help="output file (default: stdout)")
    ap.add_argument(
        "-d", "--disassemble", action="store_true", help="print a disassembly instead"
    )
    ap.add_argument(
        "--no-annotate",
        action="store_true",
        help="do not emit '// #N name' comments at the start of functions",
    )
    ap.add_argument(
        "--debug", action="store_true", help="print tracebacks for internal errors"
    )
    args = ap.parse_args(argv)

    try:
        with open(args.input, "rb") as f:
            data = f.read()
    except OSError as e:
        sys.stderr.write("error: %s\n" % e)
        return 1
    try:
        hbc = reader.HBCFile(data)
    except (reader.HBCError, struct.error) as e:
        sys.stderr.write("error: %s\n" % e)
        return 1

    out = open(args.output, "w", encoding="utf-8") if args.output else sys.stdout
    try:
        if args.disassemble:
            disasm.disassemble(hbc, out)
        else:
            dec = Decompiler(hbc, {"annotate": not args.no_annotate, "debug": args.debug})
            dec.run()
            out.write(dec.render())
            st = dec.stats
            if st["errors"]:
                sys.stderr.write(
                    "warning: %d of %d functions failed to decompile\n"
                    % (st["errors"], st["functions"])
                )
    finally:
        if out is not sys.stdout:
            out.close()
    return 0


def run_with_big_stack(fn):
    """Structuring deeply nested code recurses deeply; run on a thread with a
    large stack."""
    sys.setrecursionlimit(200000)
    threading.stack_size(512 * 1024 * 1024)
    result = []
    t = threading.Thread(target=lambda: result.append(fn()))
    t.start()
    t.join()
    return result[0] if result else 1


if __name__ == "__main__":
    sys.exit(run_with_big_stack(main))
