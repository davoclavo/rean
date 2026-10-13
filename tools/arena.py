#!/usr/bin/env python3
"""Scores this checker against the Lean Kernel Arena.

    curl -sSLO https://arena.lean-lang.org/lean-arena-tests.tar.gz
    tar xzf lean-arena-tests.tar.gz -C /tmp/arena
    python3 tools/arena.py /tmp/arena

The arena is a test suite for **kernel checkers**, from the Lean project
itself: 126 exports that a checker must accept and 72 that it must reject.

# It scores through the exit code, so this script does too

The arena runs a checker as `run: <command>` with the test file in `$IN`, and
it reads the exit code. Nothing here parses a message.

| code | the arena calls it | what `rean` means |
|---|---|---|
| 0 | accepted | every declaration checked |
| 1 | rejected | the kernel refused one, by a rule |
| 2 | declined | a limit stopped us, so there is no verdict |
| anything else | an error in the checker | our own bug |

A **declined** test is ignored for both soundness and completeness. The arena
gives the reason, and it is the reason this kernel keeps `TypeError::is_a_limit`
apart from a refusal: a decline does not claim that the proof is invalid. A
checker that refused everything would score perfectly on the bad half and be
useless, and the way that failure starts is one test at a time.

# The order it scores in

1. a **bad** test we accept is a soundness bug, and nothing else on the list
   matters while one of those is open;
2. a **good** test we reject is a rule we are missing;
3. the arena then ranks by the time on its `mathlib` test, and last by the
   number of declined tests.

So a decline is not free. It is the tiebreaker, and it is the honest answer
while it is true.

See chapter 28.
"""

import os
import subprocess
import sys
import time

CHECKER = os.environ.get("REAN", "./target/release/rean")

ACCEPTED, REJECTED, DECLINED, CRASHED, TIMEOUT = range(5)

# What the arena asks for, by the half of the suite a test is in.
WANTED = {"good": ACCEPTED, "bad": REJECTED}


def run(path, seconds):
    """Checks one export. Returns (answer, why, elapsed)."""
    started = time.time()
    try:
        done = subprocess.run(
            [CHECKER, "check", path],
            capture_output=True,
            text=True,
            timeout=seconds,
        )
    except subprocess.TimeoutExpired:
        # A timeout is recorded as declined by the arena as well, and for the
        # same reason: it is not a verdict.
        return TIMEOUT, f"no answer in {seconds}s", time.time() - started
    elapsed = time.time() - started
    answer = {0: ACCEPTED, 1: REJECTED, 2: DECLINED}.get(done.returncode, CRASHED)
    if answer == ACCEPTED:
        return answer, "", elapsed
    # The first line under the first verdict that is not `ok` is the cause.
    why = ""
    lines = (done.stdout + done.stderr).splitlines()
    for index, line in enumerate(lines):
        if line.startswith(("  FAIL", "  decl", "  block")) and index + 1 < len(lines):
            why = lines[index + 1].strip()
            break
    if not why:
        for line in lines:
            if line.startswith("error:"):
                why = line[6:].strip()
                break
    if answer == CRASHED:
        why = f"exit {done.returncode}: {why}"
    return answer, why, elapsed


def tests_under(root, only):
    """Every test of the suite, as (expected, label, path)."""
    found = []
    for expected in WANTED:
        base = os.path.join(root, expected)
        for here, _, files in os.walk(base):
            for name in sorted(files):
                if not name.endswith(".ndjson"):
                    continue
                full = os.path.join(here, name)
                label = os.path.relpath(full, base)[: -len(".ndjson")]
                if only and only not in label:
                    continue
                found.append((expected, label, full))
    return sorted(found)


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "/tmp/arena"
    only = sys.argv[2] if len(sys.argv) > 2 else ""
    seconds = int(os.environ.get("ARENA_TIMEOUT", "300"))

    tests = tests_under(root, only)
    if not tests:
        print(f"arena.py: no tests under {root}")
        return 1

    # One list per thing the arena counts, and one for what we got right.
    wrong = {"good": [], "bad": []}
    declined = {"good": [], "bad": []}
    crashed, right = [], []
    totals = {"good": 0, "bad": 0}

    for expected, label, path in tests:
        totals[expected] += 1
        answer, why, elapsed = run(path, seconds)
        if answer == WANTED[expected]:
            right.append((label, elapsed))
            mark = "ok"
        elif answer == CRASHED:
            crashed.append((label, why))
            mark = "CRASH"
        elif answer in (DECLINED, TIMEOUT):
            declined[expected].append((label, why))
            mark = "declined"
        else:
            wrong[expected].append((label, why))
            mark = "REJECTED" if expected == "good" else "ACCEPTED"
        print(f"{mark:>9}  {expected:<4} {label:<46} {elapsed:6.1f}s  {why[:60]}")

    print()
    for half, verb in (("good", "accepted"), ("bad", "rejected")):
        kept = totals[half] - len(wrong[half]) - len(declined[half])
        print(
            f"of {totals[half]:>3} {half:<4} {verb} {kept:>3}, "
            f"declined {len(declined[half]):>2}, wrong {len(wrong[half]):>2}"
        )
    print()

    if wrong["bad"]:
        print(f"**{len(wrong['bad'])} wrongly accepted**, which are soundness bugs:")
        for label, _ in wrong["bad"]:
            print(f"    {label}")
    else:
        print("no bad test was accepted")
    if wrong["good"]:
        print(f"**{len(wrong['good'])} wrongly rejected**, which are rules we lack:")
        for label, why in wrong["good"]:
            print(f"    {label}: {why[:70]}")
    else:
        print("no good test was rejected")
    if crashed:
        print(f"**{len(crashed)} crashed**, which is always our own bug:")
        for label, why in crashed:
            print(f"    {label}: {why[:70]}")
    every_decline = declined["good"] + declined["bad"]
    if every_decline:
        print(f"{len(every_decline)} declined, which the arena ignores and counts last:")
        for label, why in every_decline:
            print(f"    {label}: {why[:66]}")
    slowest = sorted(right, key=lambda row: -row[1])[:5]
    if slowest:
        print("slowest of the ones we got right:")
        for label, elapsed in slowest:
            print(f"    {elapsed:6.1f}s  {label}")
    return 1 if wrong["good"] or wrong["bad"] or crashed else 0


if __name__ == "__main__":
    sys.exit(main())
