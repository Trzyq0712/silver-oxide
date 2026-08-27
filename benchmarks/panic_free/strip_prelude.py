#!/usr/bin/env python3
"""Drop Prusti prelude methods our typechecker cannot lower yet.

`p_{Slice,Array}_{fold,unfold}_index` state their postcondition as a `forall` whose body
contains `old(...)`. Our typechecker lowers quantifier bodies in a pure context that
rejects `old`, so the whole file fails at typecheck with `IllegalOldUsage` — before any
member is verified.

Prusti emits these declarations whenever a program mentions `panic!` or an array, whether
or not anything calls them, and in this corpus nothing does. Stripping them is therefore a
no-op on the meaning of the program and buys back four otherwise-unverifiable files. Once
`old`-under-a-quantifier lowers, delete this script and read `vpr/` directly.

Usage: strip_prelude.py <in.vpr> <out.vpr>
"""

import re
import sys

DROP = re.compile(r"^method (p_(?:Slice|Array)_(?:un)?fold_index)\b")


def strip(text):
    lines = text.split("\n")
    out, dropped, i = [], [], 0
    while i < len(lines):
        m = DROP.match(lines[i])
        if m:
            dropped.append(m.group(1))
            i += 1
            # A declaration's spec lines are indented; blank lines separate declarations.
            while i < len(lines) and (lines[i].startswith("  ") or not lines[i].strip()):
                i += 1
            continue
        out.append(lines[i])
        i += 1
    return "\n".join(out), dropped


def main():
    if len(sys.argv) != 3:
        sys.exit("usage: strip_prelude.py <in.vpr> <out.vpr>")
    src, dst = sys.argv[1], sys.argv[2]
    text = open(src).read()

    stripped, dropped = strip(text)
    for name in dropped:
        # A call would make the strip unsound; the point is that these are dead.
        if re.search(r"\b%s\(" % re.escape(name), stripped):
            sys.exit("[strip_prelude] %s is called in %s; refusing to strip" % (name, src))

    open(dst, "w").write(stripped)
    if dropped:
        print("[strip_prelude] %s: dropped %s" % (src, ", ".join(dropped)))


if __name__ == "__main__":
    main()
