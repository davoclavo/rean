#!/usr/bin/env python3
"""Ranks the failures of a `rean check` report by how much they block.

A **blocked** declaration is not wrong. It waits on something that did not
check, and the report says what:

    block def   instAppendString
                  `String.append` did not check

Follow that chain far enough and it ends at one real failure. This script
follows every chain and counts the leaves that each root holds up.

    ./target/release/rean check full.ndjson > report.txt
    python3 tools/roots.py report.txt

The answer is worth the trouble. On the Lean prelude, 115 failures blocked
18,153 declarations, and **one** of them held up 15,272 of those. Work on the
longest row, not on the first failure you read.

Pair it with `tools/slice.py`: take the root, cut its slice, sweep `REAN_FUEL`.
"""

import collections
import re
import sys

LINE = re.compile(r"^  (ok   |FAIL |block) (\S+) +(\S+)$")
WAITS = re.compile(r"^\s*`(.+?)` did not check$")


def read(lines):
    """Returns the verdict for each declaration, and what each one waits on."""
    status, waits = {}, {}
    for number, line in enumerate(lines):
        found = LINE.match(line)
        if not found:
            continue
        verdict, name = found.group(1).strip(), found.group(3)
        status[name] = verdict
        if verdict == "block" and number + 1 < len(lines):
            reason = WAITS.match(lines[number + 1])
            if reason:
                waits[name] = reason.group(1)
    return status, waits


def roots(status, waits):
    """Counts, for each failure, how many blocked declarations wait on it."""
    counted = collections.Counter()
    for name, verdict in status.items():
        if verdict != "block":
            continue
        current, seen = name, set()
        # A chain can in principle close on itself, so stop if it repeats.
        while current in waits and current not in seen:
            seen.add(current)
            current = waits[current]
        if status.get(current) == "FAIL":
            counted[current] += 1
    return counted


def main():
    if len(sys.argv) != 2:
        print("usage: roots.py <report.txt>")
        return 2
    lines = open(sys.argv[1]).read().splitlines()
    status, waits = read(lines)
    counted = roots(status, waits)
    failures = sum(1 for verdict in status.values() if verdict == "FAIL")
    print(f"{failures} failures block {sum(counted.values())} declarations\n")
    print("blocked  root failure")
    for name, number in counted.most_common(20):
        print(f"{number:7}  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
