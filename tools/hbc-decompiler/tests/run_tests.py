#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Round-trip tests for the HBC v98 decompiler.

Each tests/corpus/*.js program is compiled with a v98 hermesc, decompiled,
and both the original bytecode and the decompiled JavaScript are executed with
a v98 hermes VM. The test passes when the outputs are identical.

Usage:
    run_tests.py --bin /path/to/v98/build/bin [-k filter] [-v]

The bin directory must contain `hermesc` and `hermes` built from a v98
checkout (e.g. commit 639e5d6af).
"""

import argparse
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.realpath(__file__))
DECOMPILER = os.path.join(os.path.dirname(HERE), "hbc-decompile")
OPT_LEVELS = ["-O", "-O0"]


def run(cmd, timeout=60):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    return p.returncode, p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True, help="directory with v98 hermesc and hermes")
    ap.add_argument("-k", help="only run tests whose name contains this")
    ap.add_argument("-v", action="store_true", help="show diffs for failures")
    ap.add_argument("--keep", help="directory to keep decompiled outputs in")
    args = ap.parse_args()
    hermesc = os.path.join(args.bin, "hermesc")
    hermes = os.path.join(args.bin, "hermes")
    tests = sorted(f for f in os.listdir(os.path.join(HERE, "corpus")) if f.endswith(".js"))
    if args.k:
        tests = [t for t in tests if args.k in t]
    failures = []
    fallbacks = 0
    tmp = tempfile.mkdtemp(prefix="hbcdec-")
    for t in tests:
        src = os.path.join(HERE, "corpus", t)
        for opt in OPT_LEVELS:
            name = "%s %s" % (t, opt)
            base = os.path.join(args.keep or tmp, t[:-3] + opt.replace("-", "_"))
            hbc = base + ".hbc"
            out_js = base + ".dec.js"
            rc, _, err = run([hermesc, opt, "-emit-binary", "-out", hbc, src])
            if rc:
                failures.append((name, "hermesc failed:\n" + err))
                continue
            rc1, exp, err1 = run([hermes, hbc])
            rc, _, err = run([sys.executable, DECOMPILER, hbc, "-o", out_js])
            if rc:
                failures.append((name, "decompiler failed:\n" + err))
                continue
            with open(out_js) as f:
                text = f.read()
            fallbacks += text.count("(unstructured)")
            if "decompilation failed" in text:
                failures.append((name, "some functions failed to decompile"))
                continue
            rc2, got, err2 = run([hermes, "-w", out_js])
            if (rc1 == 0) != (rc2 == 0) or exp != got:
                failures.append(
                    (
                        name,
                        "output mismatch (rc %d vs %d)\n--- expected\n%s\n--- got\n%s\n%s"
                        % (rc1, rc2, exp, got, err2[-2000:]),
                    )
                )
                continue
            print("PASS", name)
    for name, msg in failures:
        print("FAIL", name)
        if args.v:
            print(msg)
    total = len(tests) * len(OPT_LEVELS)
    print(
        "\n%d/%d passed, %d unstructured functions"
        % (total - len(failures), total, fallbacks)
    )
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
