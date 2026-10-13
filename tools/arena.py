#!/usr/bin/env python3
"""Scores this checker against the Lean Kernel Arena.

    curl -sSLO https://arena.lean-lang.org/lean-arena-tests.tar.gz
    tar xzf lean-arena-tests.tar.gz -C /tmp/arena
    python3 tools/arena.py /tmp/arena

The arena is a test suite for **kernel checkers**, from the Lean project
itself: 126 exports that a checker must accept and 72 that it must reject. Its
own scoring puts them in that order of importance, and so does this script:

1. a **bad** test that we accept is a soundness bug, and nothing else on the
   list matters while one of those is open;
2. a **good** test that we reject is a rule we are missing, or a limit we set
   too low;
3. the time comes last.

# The distinction this script adds

A bad test that we reject **because we ran out of budget** is the right answer
for the wrong reason. The kernel says so itself: `OutOfFuel` and `OutOfStack`
mean "we did not check it", not "this is wrong". A checker that refused
everything would score perfectly on the bad half and be useless, and the way
that failure begins is one test at a time. So a rejection by a limit is counted
and named apart from a rejection by a rule.

See chapter 20.
"""

import os
import re
import subprocess
import sys
import time

# The messages the kernel uses for a limit rather than a refusal. See
# `TypeError::is_a_limit` in `rean_kernel`.
LIMIT = re.compile(r"units of work|of stack it is allowed|levels of recursion")

CHECKER = os.environ.get("REAN", "./target/release/rean")


def run(path, seconds):
    """Checks one export. Returns (accepted, cause, elapsed)."""
    started = time.time()
    try:
        done = subprocess.run(
            [CHECKER, "check", path],
            capture_output=True,
            text=True,
            timeout=seconds,
        )
    except subprocess.TimeoutExpired:
        return False, f"no answer in {seconds}s", time.time() - started
    elapsed = time.time() - started
    if done.returncode == 0:
        return True, "", elapsed
    # The first line under the first FAIL or block is the cause.
    cause = ""
    lines = (done.stdout + done.stderr).splitlines()
    for index, line in enumerate(lines):
        if line.startswith(("  FAIL", "  block")) and index + 1 < len(lines):
            cause = lines[index + 1].strip()
            break
    if not cause:
        for line in lines:
            if line.startswith("error:"):
                cause = line[6:].strip()
                break
    return False, cause, elapsed


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "/tmp/arena"
    only = sys.argv[2] if len(sys.argv) > 2 else ""
    seconds = int(os.environ.get("ARENA_TIMEOUT", "300"))

    tests = []
    for expected in ("good", "bad"):
        base = os.path.join(root, expected)
        for here, _, files in os.walk(base):
            for name in sorted(files):
                if name.endswith(".ndjson"):
                    full = os.path.join(here, name)
                    label = os.path.relpath(full, base)[: -len(".ndjson")]
                    if only and only not in label:
                        continue
                    tests.append((expected, label, full))
    if not tests:
        print(f"arena.py: no tests under {root}")
        return 1

    wrongly_accepted, wrongly_rejected, by_limit, right = [], [], [], []
    for expected, label, path in sorted(tests):
        accepted, cause, elapsed = run(path, seconds)
        mark = "?"
        if expected == "good":
            if accepted:
                right.append((label, elapsed))
                mark = "ok"
            else:
                wrongly_rejected.append((label, cause, elapsed))
                mark = "REJECTED"
        else:
            if accepted:
                wrongly_accepted.append((label, elapsed))
                mark = "ACCEPTED"
            elif LIMIT.search(cause):
                by_limit.append((label, cause, elapsed))
                mark = "limit"
            else:
                right.append((label, elapsed))
                mark = "ok"
        print(f"{mark:>9}  {expected:<4} {label:<46} {elapsed:6.1f}s  {cause[:60]}")

    good = sum(1 for e, _, _ in tests if e == "good")
    bad = len(tests) - good
    print()
    print(f"accepted of {good} good:  {good - len(wrongly_rejected)}")
    print(f"rejected of {bad} bad:   {bad - len(wrongly_accepted)}")
    print()
    if wrongly_accepted:
        print(f"**{len(wrongly_accepted)} wrongly accepted**, which are soundness bugs:")
        for label, _ in wrongly_accepted:
            print(f"    {label}")
    else:
        print("no bad test was accepted")
    if by_limit:
        print(f"{len(by_limit)} rejected by a **limit** and not by a rule:")
        for label, cause, _ in by_limit:
            print(f"    {label}: {cause[:60]}")
    if wrongly_rejected:
        print(f"{len(wrongly_rejected)} wrongly rejected:")
        for label, cause, _ in wrongly_rejected:
            print(f"    {label}: {cause[:70]}")
    slowest = sorted(right, key=lambda row: -row[1])[:5]
    if slowest:
        print("slowest of the ones we got right:")
        for label, elapsed in slowest:
            print(f"    {elapsed:6.1f}s  {label}")
    return 1 if wrongly_accepted or wrongly_rejected else 0


if __name__ == "__main__":
    sys.exit(main())
