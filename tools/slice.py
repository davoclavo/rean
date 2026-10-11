#!/usr/bin/env python3
"""Cuts a `lean4export` file after one declaration.

Chapters 11 and 12 use this, and the method is the point: **take one failing
declaration, not the class of them.** 676 failures with one guessed cause is
worse than one failure with a measured one.

It works because the export format is **topologically ordered**. Every index a
line mentions is defined on an earlier line, so a prefix of the file is a module
in its own right. Cut after the declaration you want, and you have it and its
dependencies and nothing else.

    python3 tools/slice.py full.ndjson one.ndjson Nat.modCore_eq_mod
    REAN_FUEL=500000000 ./target/release/rean check one.ndjson

Then sweep `REAN_FUEL`. If the declaration passes at a larger budget and spends
it in about a second, the budget is the fault. If it wants twenty **billion**
units, the kernel is. Two plans were retired by that one question.
"""

import json
import sys

# The name table is built as the file is read. Index 0 is the anonymous name.
DECLARATIONS = ("thm", "def", "axiom", "opaq", "inductive", "ctor", "rec", "quot")


def names_and_cut(lines, target):
    """Returns the index of the line that declares `target`, or `None`."""
    names = {0: ""}
    for number, line in enumerate(lines):
        line = line.strip()
        if not line:
            continue
        try:
            entry = json.loads(line)
        except json.JSONDecodeError:
            continue
        if "in" in entry:
            if "str" in entry:
                prefix = names.get(entry["str"]["pre"], "")
                part = entry["str"]["str"]
            elif "num" in entry:
                prefix = names.get(entry["num"]["pre"], "")
                part = str(entry["num"]["i"])
            else:
                continue
            names[entry["in"]] = f"{prefix}.{part}" if prefix else part
        for kind in DECLARATIONS:
            body = entry.get(kind)
            if isinstance(body, dict) and names.get(body.get("name")) == target:
                return number
    return None


def main():
    if len(sys.argv) != 4:
        print("usage: slice.py <in.ndjson> <out.ndjson> <declaration name>")
        return 2
    source, destination, target = sys.argv[1:4]
    lines = open(source).read().splitlines()
    cut = names_and_cut(lines, target)
    if cut is None:
        print(f"{target} is not declared in {source}")
        return 1
    print(f"{target} is at line {cut + 1} of {len(lines)}")
    with open(destination, "w") as out:
        out.write("\n".join(lines[: cut + 1]) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
