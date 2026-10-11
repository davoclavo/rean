#!/usr/bin/env python3
"""Fails when a chapter names a function or a test that does not exist.

Chapter 1 states the project's rule: "A comment goes stale in silence. A test
does not." It then named five tests, chapter 2 closed the gaps those tests
carried, the tests were **deleted**, and the chapter went on naming them for ten
commits. The rule was right and nothing enforced it.

This does. Every `snake_case` name in backticks in a document must be defined
somewhere in the code, as a Rust `fn` or a Python `def`.

    python3 tools/cite.py

`devbox run check` runs it, so a chapter that cites a test nobody wrote, or that
somebody removed, fails the gate.

A name needs an entry in KNOWN only when it is neither: a Lean tactic, a tool,
or an environment variable.
"""

import glob
import re
import sys

# Names that are not ours to define.
KNOWN = {
    "native_decide",  # a Lean tactic
}

# A cited name is at least this long, so that ordinary prose in backticks does
# not count. Every real test name in this project is far longer.
SHORTEST = 12

DEFINED = re.compile(r"\b(?:fn|def)\s+([a-z0-9_]+)\s*[(<]")
CITED = re.compile(r"`([a-z][a-z0-9_]*)`")


def defined_names():
    names = set()
    for pattern in ("crates/*/src/*.rs", "crates/*/tests/*.rs", "tools/*.py"):
        for path in glob.glob(pattern):
            names.update(DEFINED.findall(open(path).read()))
    return names


def main():
    names = defined_names()
    if not names:
        print("cite.py: found no code. Run it from the top of the repository.")
        return 2
    missing = []
    for doc in sorted(glob.glob("docs/*.md")) + ["README.md"]:
        for number, line in enumerate(open(doc).read().splitlines(), start=1):
            for cited in CITED.findall(line):
                if len(cited) < SHORTEST or "_" not in cited:
                    continue
                if cited in names or cited in KNOWN:
                    continue
                # An environment variable is upper case, so it cannot reach
                # here. A file name carries a dot, and the pattern excludes one.
                missing.append((doc, number, cited))
    if not missing:
        print(f"cite.py: every cited name exists, out of {len(names)} defined")
        return 0
    print("cite.py: these documents name something that does not exist:")
    for doc, number, cited in missing:
        print(f"  {doc}:{number}: {cited}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
