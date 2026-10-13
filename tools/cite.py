#!/usr/bin/env python3
"""Fails when a chapter names something that does not exist.

Two kinds of citation, and both can rot without anybody noticing:

1. a function or a test name, in backticks;
2. a cross-reference to another chapter's section, as "chapter 17, section 17.6"
   or as the short form "§17.6".

Part I of the book lives in `docs/book/`, and it is numbered on its own. A
cross-reference inside the book resolves against the book, and a
cross-reference inside a later chapter resolves against those chapters. So
"chapter 15, section 15.4" means two different headings, and this tool knows
which one each document means.

Chapter 9 states the project's rule: "A comment goes stale in silence. A test
does not." It then named five tests, chapter 10 closed the gaps those tests
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

A chapter also cites a function of **Lean's own** C++ kernel, which this
repository does not hold. Those names live in FOREIGN, with the file that
defines each one. Check a new entry against that file before you add it.

The third check is a numbered link. A link written "[17](17-name.md)" must
point at the chapter its text names, because a renumber moves the file and
leaves the text behind. The renumber of the chapters from 1..20 to 9..28 left
five of them behind, and nothing but this check noticed.

The fourth check is a chapter number. "chapter 12" must name a chapter that
exists, and so must each number of "chapters 19 and 20". A renumber moves the
first number of a range, because only that one carries the word, and the
second one stays behind and still reads as a chapter. Twenty of them did.
This check finds a number that names **nothing**. It cannot find a number that
names the wrong chapter, so a renumber still needs a reader.

The fifth check is a glossary link. A chapter links a mathematical term to its
definition, as `[definitional equality](../GLOSSARY.md#definitional-equality)`,
and the anchor has to be there. Each term of the glossary carries one.

The sixth check is the reading order. The book is meant to be read in
sequence, so every chapter must say where the reader is, and every chapter but
the last must name the next one. A chapter that names nothing is a dead end,
and a reader who reaches one has to guess.
"""

import glob
import os
import re
import sys

# Names that are not ours to define.
KNOWN = {
    "native_decide",  # a Lean tactic
    # A declaration of the Lean library. Most of those carry a dot or a capital
    # and never match CITED, so this set only needs the few that read like one
    # of our test names.
    "of_decide_eq_true",
}

# A function of Lean's own source, or of another prover. We cannot check these
# against our code, so each one carries the file that defines it. Read the file
# in the repository `leanprover/lean4` before you add a name here.
FOREIGN = {
    # src/kernel/type_checker.cpp
    "infer_type_core": "src/kernel/type_checker.cpp",
    "is_def_eq_core": "src/kernel/type_checker.cpp",
    "is_def_eq_app": "src/kernel/type_checker.cpp",
    "is_def_eq_proof_irrel": "src/kernel/type_checker.cpp",
    "is_def_eq_unit_like": "src/kernel/type_checker.cpp",
    "quick_is_def_eq": "src/kernel/type_checker.cpp",
    "lazy_delta_reduction": "src/kernel/type_checker.cpp",
    "lazy_delta_reduction_step": "src/kernel/type_checker.cpp",
    "unfold_definition": "src/kernel/type_checker.cpp",
    "reduce_recursor": "src/kernel/type_checker.cpp",
    "try_eta_struct_core": "src/kernel/type_checker.cpp",
    "reduce_bin_nat_op": "src/kernel/type_checker.cpp",
    "reduce_bin_nat_pred": "src/kernel/type_checker.cpp",
    "check_nat_size": "src/kernel/type_checker.cpp",
    "cache_success": "src/kernel/type_checker.cpp",
    "cache_failure": "src/kernel/type_checker.cpp",
    "succeeded_before": "src/kernel/type_checker.cpp",
    "failed_before": "src/kernel/type_checker.cpp",
    "scope_rec_depth": "src/kernel/type_checker.cpp",
    # src/kernel/inductive.cpp
    "nat_lit_to_constructor": "src/kernel/inductive.cpp",
    "check_no_nested_aux": "src/kernel/inductive.cpp",
    "check_uniform_ind_occs": "src/kernel/inductive.cpp",
    "expand_eta_struct": "src/kernel/inductive.cpp",
    "is_non_rec_structure": "src/kernel/inductive.cpp",
    # src/kernel/expr.h
    "get_loose_bvar_range": "src/kernel/expr.h",
    # Rocq, formerly Coq. A reduction machine, not a function of ours.
    "native_compute": "the Rocq reference manual",
}

# A cited name is at least this long, so that ordinary prose in backticks does
# not count. Every real test name in this project is far longer.
SHORTEST = 12

DEFINED = re.compile(r"\b(?:fn|def)\s+([a-z0-9_]+)\s*[(<]")
CITED = re.compile(r"`([a-z][a-z0-9_]*)`")
HEADING = re.compile(r"^## (\d+\.\d+)", re.M)
CHAPTER = re.compile(r"^docs/(\d+)")
BOOK_CHAPTER = re.compile(r"^docs/book/(\d+)")
# "chapter 17, section 17.6" and the short form "§17.6". A reference that begins
# with "Part I " belongs to the book, and PART_I_REF below reads it instead.
LONG_REF = re.compile(r"(?<!Part I )[Cc]hapter (\d+), section (\d+\.\d+)")
SHORT_REF = re.compile(r"§(\d+\.\d+)")
# "Part I chapter 6, section 6.9", which a later chapter writes to point into
# the book. The chapter number may carry a markdown link.
PART_I_REF = re.compile(r"Part I chapter \[?(\d+)\]?(?:\([^)]*\))?, section (\d+\.\d+)")


# The reading order, as `docs/README.md` states it. Part I first, then the
# implementation chapters. Chapter 0 is the appendix, so it is not in the
# chain.
def reading_order():
    return sorted(glob.glob("docs/book/[0-9]*.md")) + sorted(
        p for p in glob.glob("docs/[0-9][0-9]-*.md")
        if not p.startswith("docs/00-")
    )


# "chapter 12", and each number of "chapters 19 and 20" or "chapters 9, 10, 12".
CHAPTER_NUMBER = re.compile(r"(?<!Part I )[Cc]hapters? (\d+)(?: (?:and|to|or) (\d+))?")
CHAPTER_LIST = re.compile(r"(?<!Part I )[Cc]hapters? (\d+), (\d+)(?:, (\d+))?")
PART_I_CHAPTER = re.compile(r"Part I chapters? \[?(\d+)\]?")


def bad_chapter_numbers(chapters, book):
    """Finds a chapter number that names no chapter."""
    missing = []
    for doc in documents():
        here = book if doc.startswith("docs/book/") else chapters | {0}
        for number, line in enumerate(open(doc).read().splitlines(), start=1):
            found = set()
            for pattern in (CHAPTER_NUMBER, CHAPTER_LIST):
                for groups in pattern.findall(line):
                    found.update(g for g in groups if g)
            for cited in sorted(found):
                if int(cited) not in here:
                    missing.append((doc, number, f"chapter {cited}"))
            for cited in PART_I_CHAPTER.findall(line):
                if int(cited) not in book:
                    missing.append((doc, number, f"Part I chapter {cited}"))
    return missing


GLOSSARY_LINK = re.compile(r"GLOSSARY\.md#([a-z0-9_-]+)")
GLOSSARY_ANCHOR = re.compile(r'<a id="([a-z0-9-]+)"></a>')
GLOSSARY_HEADING = re.compile(r"^#{2,3} (.+)$", re.M)


def heading_anchor(title):
    """The anchor a site builds from a heading: lower case, spaces to hyphens."""
    plain = re.sub(r"[^a-zA-Z0-9 -]", "", title.replace("`", ""))
    return re.sub(r" +", "-", plain.strip().lower())


def bad_glossary_links():
    """Finds a link into the glossary that no anchor answers."""
    text = open("docs/GLOSSARY.md").read()
    anchors = set(GLOSSARY_ANCHOR.findall(text))
    anchors |= {heading_anchor(t) for t in GLOSSARY_HEADING.findall(text)}
    missing = []
    for doc in documents():
        for number, line in enumerate(open(doc).read().splitlines(), start=1):
            for anchor in GLOSSARY_LINK.findall(line):
                if anchor not in anchors:
                    missing.append((doc, number, f"the glossary has no #{anchor}"))
    return missing


# A link whose text starts with a number, pointing at a chapter file.
NUMBERED_LINK = re.compile(
    r"\[(\d+)[^\]]*\]\((?:\.\./)?(?:docs/)?(?:book/)?(\d\d)-[a-z0-9-]+\.md\)"
)


def bad_numbered_links():
    """Finds a link whose text names one chapter and whose target is another."""
    missing = []
    for doc in documents():
        for number, line in enumerate(open(doc).read().splitlines(), start=1):
            for text, target in NUMBERED_LINK.findall(line):
                if int(text) != int(target):
                    missing.append(
                        (doc, number, f"link text {text} points at chapter {target}")
                    )
    return missing


def broken_chain():
    """Finds a chapter with no `Where you are`, and one that names no next."""
    order = reading_order()
    missing = []
    for index, path in enumerate(order):
        text = open(path).read()
        if "**Where you are.**" not in text:
            missing.append((path, 1, "no `Where you are` block"))
        if index + 1 == len(order):
            continue
        following = os.path.basename(order[index + 1])
        tail = text[-700:]
        if following not in tail:
            missing.append((path, len(text.splitlines()), f"does not lead to {following}"))
    return missing


def documents():
    """Every file this tool reads, once each, in the order a reader meets them."""
    ordered = (
        ["docs/README.md", "docs/book/README.md"]
        + sorted(glob.glob("docs/book/[0-9]*.md"))
        + sorted(glob.glob("docs/*.md"))
        + ["README.md"]
    )
    return list(dict.fromkeys(ordered))


def defined_names():
    names = set()
    for pattern in ("crates/*/src/*.rs", "crates/*/tests/*.rs", "tools/*.py"):
        for path in glob.glob(pattern):
            names.update(DEFINED.findall(open(path).read()))
    return names


def chapter_sections(pattern, chapter_of):
    """Returns the set of section numbers that each chapter actually has."""
    sections = {}
    for path in glob.glob(pattern):
        number = int(chapter_of.match(path).group(1))
        sections[number] = set(HEADING.findall(open(path).read()))
    return sections


def bad_references(sections, book_sections):
    """Finds every cross-reference that points at no heading."""
    missing = []
    for doc in documents():
        here = book_sections if doc.startswith("docs/book/") else sections
        for number, line in enumerate(open(doc).read().splitlines(), start=1):
            found = [
                (int(c), s) for c, s in LONG_REF.findall(line)
            ] + [(int(s.split(".")[0]), s) for s in SHORT_REF.findall(line)]
            for chapter, section in found:
                if section not in here.get(chapter, set()):
                    missing.append((doc, number, f"chapter {chapter} section {section}"))
            for chapter, section in PART_I_REF.findall(line):
                if section not in book_sections.get(int(chapter), set()):
                    missing.append(
                        (doc, number, f"Part I chapter {chapter} section {section}")
                    )
    return missing


def main():
    names = defined_names()
    if not names:
        print("cite.py: found no code. Run it from the top of the repository.")
        return 2
    missing = []
    for doc in documents():
        for number, line in enumerate(open(doc).read().splitlines(), start=1):
            for cited in CITED.findall(line):
                if len(cited) < SHORTEST or "_" not in cited:
                    continue
                if cited in names or cited in KNOWN or cited in FOREIGN:
                    continue
                # An environment variable is upper case, so it cannot reach
                # here. A file name carries a dot, and the pattern excludes one.
                missing.append((doc, number, cited))
    sections = chapter_sections("docs/[0-9]*.md", CHAPTER)
    book_sections = chapter_sections("docs/book/[0-9]*.md", BOOK_CHAPTER)
    missing += bad_references(sections, book_sections)
    missing += bad_chapter_numbers(set(sections), set(book_sections))
    missing += bad_glossary_links()
    missing += bad_numbered_links()
    missing += broken_chain()
    if not missing:
        print(
            f"cite.py: every citation resolves. {len(names)} names, "
            f"{sum(len(s) for s in sections.values())} sections, "
            f"{sum(len(s) for s in book_sections.values())} book sections, "
            f"{len(FOREIGN)} foreign names, "
            f"{len(reading_order())} chapters in one chain."
        )
        return 0
    print("cite.py: these documents name something that does not exist:")
    for doc, number, cited in missing:
        print(f"  {doc}:{number}: {cited}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
