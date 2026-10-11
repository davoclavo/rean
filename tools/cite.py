#!/usr/bin/env python3
"""Fails when a chapter names something that does not exist.

Two kinds of citation, and both can rot without anybody noticing:

1. a function or a test name, in backticks;
2. a cross-reference to another chapter's section, as "chapter 9, section 9.6"
   or as the short form "§9.6".

Chapter 1 states the project's rule: "A comment goes stale in silence. A test
does not." It then named five tests, chapter 2 closed the gaps those tests
carried, the tests were **deleted**, and the chapter went on naming them for ten
commits. The rule was right and nothing enforced it.

This does. Every `snake_case` name in backticks in a document must be defined somewhere in
the code, as a Rust `fn` or a Python `def`. Every section a document points at
must be a heading of that chapter.

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
HEADING = re.compile(r"^## (\d+\.\d+)", re.M)
CHAPTER = re.compile(r"^docs/(\d+)")
# "chapter 9, section 9.6" and the short form "§9.6".
LONG_REF = re.compile(r"[Cc]hapter (\d+), section (\d+\.\d+)")
SHORT_REF = re.compile(r"§(\d+\.\d+)")


def defined_names():
    names = set()
    for pattern in ("crates/*/src/*.rs", "crates/*/tests/*.rs", "tools/*.py"):
        for path in glob.glob(pattern):
            names.update(DEFINED.findall(open(path).read()))
    return names


def chapter_sections():
    """Returns the set of section numbers that each chapter actually has."""
    sections = {}
    for path in glob.glob("docs/[0-9]*.md"):
        number = int(CHAPTER.match(path).group(1))
        sections[number] = set(HEADING.findall(open(path).read()))
    return sections


def bad_references(sections):
    """Finds every cross-reference that points at no heading."""
    missing = []
    for doc in sorted(glob.glob("docs/*.md")) + ["README.md"]:
        for number, line in enumerate(open(doc).read().splitlines(), start=1):
            found = [
                (int(c), s) for c, s in LONG_REF.findall(line)
            ] + [(int(s.split(".")[0]), s) for s in SHORT_REF.findall(line)]
            for chapter, section in found:
                if section not in sections.get(chapter, set()):
                    missing.append((doc, number, f"chapter {chapter} section {section}"))
    return missing


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
    sections = chapter_sections()
    missing += bad_references(sections)
    if not missing:
        print(
            f"cite.py: every citation resolves. {len(names)} names, "
            f"{sum(len(s) for s in sections.values())} sections."
        )
        return 0
    print("cite.py: these documents name something that does not exist:")
    for doc, number, cited in missing:
        print(f"  {doc}:{number}: {cited}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
