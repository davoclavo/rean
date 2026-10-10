# Roadmap

## The strategy

This project is an educational experiment. The goal is to understand a proof
checker by building one, not to ship a competitor.

So we build the whole pipeline ourselves, and we use the real Lean as a
**ground truth**. `lean4export` writes Lean's elaborated terms to a file. We read
that file, and at each stage we ask: does our answer agree?

```
  foo.lean  ───[ our lexer ]──[ our parser ]──[ our elaborator ]──> our Expr
      │                                                                │
      │                                                                │
      └───────[ real Lean ]───[ lean4export ]──> foo.ndjson ──> Lean's Expr
                                                                       │
                                        the two must meet here  <──────┘
```

The file is a checkpoint. It is also a source of test data that we do not have
to invent, and it is the only honest way to know that our kernel agrees with
Lean's kernel.

## Where the two islands are today

| Island | Input | Output | Status |
|---|---|---|---|
| **A** the lexer | `.lean` text | `Vec<Token>` | works |
| — the parser | `Vec<Token>` | `Syntax` | missing |
| — the elaborator | `Syntax` | `Expr` | missing |
| **B** the kernel | `Expr` | yes or no | works. β ζ δ ι η, proof irrelevance, projections. |
| **B** the importer | `.ndjson` | `Environment` | works |

The two islands still do not touch. Nothing in a `.lean` file reaches the
kernel. But island B now reads real Lean terms, so it is testable on its own.
That is what the ground truth bought.

## The checkpoint ladder

One refinement matters. **Do not compare terms at first. Compare types.**

Lean's elaborator does things our elaborator will not do the same way:

- It fills an implicit argument by unification, and a different term can be just
  as correct.
- It generates helper declarations that nobody wrote, with names such as
  `foo.match_1`.
- It compiles recursion on a well founded order into a call to `WellFounded.fix`.
- It attaches `mdata` annotations.

So an exact term match is the wrong gate. Use three levels instead, and treat
each one as a separate number.

### Level 1: our kernel checks Lean's terms

```
foo.ndjson  ──>  [ our importer ]  ──>  Expr  ──>  [ our kernel ]  ──>  ok / fail
```

Needs no parser and no elaborator. It makes `rean` an independent checker, which
is the whole reason `lean4export` exists. See chapter 0, section 0.16.

**Metric:** we check N of M declarations of a module.

### Level 2: our pipeline inhabits Lean's type

```
foo.lean  ──>  [ our pipeline ]  ──>  our Expr
foo.ndjson  ──>  Lean's TYPE for that declaration
                 question: does our Expr have that type?
```

We do not have to match Lean's proof. We only have to produce **some** term of
the type that Lean reports. That is a strong signal and a reachable one.

**Metric:** we elaborate N of M declarations to a term of the right type.

### Level 3: our term matches Lean's term

`alpha_eq` first, then `is_def_eq`. Realistic for a simple definition and not
for a tactic proof. Report it per declaration as a bonus, never as a gate.

**Metric:** N of M terms match, split by `alpha_eq` and by `is_def_eq`.

## The bootstrap bonus

This is the part that makes the plan better than it looks.

Our elaborator cannot resolve the name `Nat` until an environment holds a
declaration for it. Building that environment needs an elaborator. That is a
circle.

The ground truth file breaks it. **Load Lean's export of the prelude as our
environment.** Then our elaborator can resolve `Nat`, `Nat.succ`, and `HAdd.hAdd`
on its first day, long before we can elaborate the prelude ourselves.

So this becomes a real test very early:

```lean
def two : Nat := 2
```

Our lexer reads it, our parser builds the tree, our elaborator resolves `Nat`
against Lean's declaration, and our kernel checks the result. Every stage is
ours. Only the library comes from outside.

## The chapter sequence

| Chapter | Adds | Unlocks |
|---|---|---|
| 0 | the kernel terms. **Done.** | `Expr`, `Level`, de Bruijn |
| 1 | the type checker. **Done.** | implicational logic |
| 2 | `Environment`, declarations, δ, ι, η, proof irrelevance, projections, level normalization. **Done.** | a name has a type |
| 3 | the importer and the Level 1 harness. **Done.** | **32 of 32 on the fixture** |
| 4 | strict positivity, recursor re-derivation, K-like ι, the quotient rules | a checker you can **trust** |
| 5 | the Pratt parser, with the extensible precedence table | `Vec<Token>` becomes `Syntax` |
| 6 | the elaborator: name resolution, implicit arguments, unification | **Level 2 opens** |
| 7 | metavariables, instance search, tactics | real proofs from real text |
| 8 | the exporter | closes the loop. Short, by then. |
| later | LCNF and a backend | a program that runs |

Note where the exporter sits. It is last and it is small, because by chapter 8
the reader in chapter 3 will have pinned down every detail of the format.

## Ground truth hygiene

Four rules, so the oracle stays trustworthy.

1. **Pin the version.** The format carries a `meta` line with the exporter
   version, the Lean version, and the format version. Record all three next to
   the fixture file. The format already changed once, from a line based table to
   NDJSON.
2. **Commit a small fixture, not the prelude.** A few kilobytes of export for a
   handful of declarations belongs in the repository. The full prelude does not.
   Generate that on demand.
3. **Never trust the file to be well formed.** The importer reports a
   diagnostic. It does not panic.
4. **A trusted checker re-derives.** The file hands us the recursor and the right
   hand side of every ι rule. A first version may store and use them. A version
   you trust re-derives the recursor and runs the positivity check itself.

## What the first real file taught us

`fixtures/lean4export/Nat.add_succ.ndjson` is a committed ground truth file. It
settled four questions that the specification document does not answer, and it
contradicted that document twice.

### Confirmed by the file

| Question | Answer |
|---|---|
| Is name index 0 pre-populated? | **yes.** No line defines it. It is `Name.anonymous`. |
| Is level index 0 pre-populated? | **yes.** No line defines it. It is `Level.zero`. |
| Is term index 0 pre-populated? | **no.** Term indices start at 0 and the first line defines it. |
| Does a reference point backwards? | **yes.** The file is in topological order. |
| Is the `meta` line first? | **yes**, with three separate version numbers. |

### Two places where the document and the file disagree

The specification on the `lean4export` master branch describes a newer format
than the committed example file. Master pins Lean v4.35.0-rc4. The example file
reports format 3.0.0 and Lean 4.27.0-rc1.

| Thing | The document says | The file says |
|---|---|---|
| inductive fields | `types`, `ctors`, `recs` | `inductiveVals`, `constructorVals`, `recursorVals` |
| a `def` or `thm` payload | one object | an **array** of objects, for a mutual group |

So the rule is: **read the file, not the document.** Our reader must branch on
the `meta` line and must reject a version it does not know, rather than guess.

JSON key order also varies between lines, so the reader must not depend on it.

## The one number

Each level reports one number. Put all three in the README and move them up.

```
level 1   our kernel checks        32 of 32 declarations   <- as of 2026-10-10
level 2   our elaborator inhabits   0 of 32 types          <- needs a parser
level 3   our term matches Lean's    0 of 32 terms
```

That beats a hand written test as a correctness oracle, and it is how the other
independent checkers were built.
