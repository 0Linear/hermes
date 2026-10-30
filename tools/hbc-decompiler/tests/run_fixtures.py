#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Decompile the precompiled v98 bytecode in tests/fixtures/ and run the
output with Node.js, comparing against the output of the original bytecode
(recorded from a v98 hermes VM in the .expected files).

The fixtures are tests/corpus/<name>.js compiled with a v98 hermesc at -O and
-O0. To refresh them after changing the corpus, rebuild them with
run_tests.py's toolchain and re-record the expected output.

Usage: run_fixtures.py [--node /path/to/node] [-k filter] [-v]
"""

import argparse
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.realpath(__file__))
DECOMPILER = os.path.join(os.path.dirname(HERE), "hbc-decompile")
FIXTURES = os.path.join(HERE, "fixtures")

# Runs a decompiled file as a classic script in the global scope, with a
# Hermes-compatible print().
NODE_RUNNER = """
const vm = require("vm");
const fs = require("fs");
globalThis.print = (...a) => console.log(a.map(String).join(" "));
const file = process.argv[1];
vm.runInThisContext(fs.readFileSync(file, "utf8"), { filename: file });
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--node", default=shutil.which("node"), help="path to node")
    ap.add_argument("-k", help="only run fixtures whose name contains this")
    ap.add_argument("-v", action="store_true", help="show diffs for failures")
    args = ap.parse_args()
    if not args.node:
        sys.stderr.write("error: node not found; pass --node\n")
        return 2
    names = sorted(f[:-4] for f in os.listdir(FIXTURES) if f.endswith(".hbc"))
    if args.k:
        names = [n for n in names if args.k in n]
    tmp = tempfile.mkdtemp(prefix="hbcdec-fx-")
    failures = 0
    for name in names:
        hbc = os.path.join(FIXTURES, name + ".hbc")
        with open(os.path.join(FIXTURES, name + ".expected")) as f:
            expected = f.read()
        out_js = os.path.join(tmp, name + ".js")
        p = subprocess.run(
            [sys.executable, DECOMPILER, hbc, "-o", out_js],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if p.returncode:
            print("FAIL", name, "(decompiler error)")
            if args.v:
                print(p.stderr.decode())
            failures += 1
            continue
        p = subprocess.run(
            [args.node, "-e", NODE_RUNNER, out_js],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=60,
        )
        got = p.stdout.decode("utf-8", "replace")
        if got != expected:
            print("FAIL", name)
            if args.v:
                print("--- expected\n%s--- got\n%s" % (expected, got))
            failures += 1
        else:
            print("PASS", name)
    print("\n%d/%d passed" % (len(names) - failures, len(names)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
