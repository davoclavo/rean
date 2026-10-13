# How Lean 4 is built, from the ground up

This is a book about one question: **how does a computer check a proof?**

It answers the question by building the thing. Part I is the theory that Lean 4
rests on. Parts II to VII build a working proof checker in Rust, point it at the
real Lean library, and measure what it costs.

Start at [Part I chapter 1](book/01-a-proof-is-a-program.md). It assumes
nothing.

---

## How to read this

**In order.** Each chapter adds one thing, and the next one uses it. The order
is not a suggestion, and the table in section 4 says exactly what you miss if
you jump.

**With the commands.** Every chapter has a `Try it` section. Run it. A rule you
have watched run is a rule you keep.

**Kindly.** Nothing here is obvious. Where a part is hard, it says so. Where a
question catches everybody, it is answered rather than avoided.

**One note on numbers.** The chapters run from 1 to 28 with no repeats.
Part I holds 1 to 8 and lives in `docs/book/`. The chapters that build the
checker hold 9 to 28. A reference into Part I is written in full, as
"Part I chapter 4", because Part I sits in a folder of its own.

**If you write TypeScript or Scala 3.** You already use most of the ideas here
under other names. The glossary opens with a table that maps them:
[if you come from TypeScript or Scala 3](GLOSSARY.md#if-you-come-from-typescript-or-scala-3).
Every chapter of Part I also has a section with that name, which puts the
chapter next to `never`, `Nothing`, `given`, a match type, a GADT, or the `R`
channel of `Effect<A, E, R>`.

Two files stay open beside you the whole way.

| File | For |
|---|---|
| [the glossary](GLOSSARY.md) | a word you do not know |
| [the references](REFERENCES.md) | the source for a claim, with a link |

---

## 1. The one picture

Lean turns text into a program and into a proof. It does that in five stages.

```
  text ──1──> tokens ──2──> Syntax ──3──> Expr ──4──> yes or no
                                            │
                                            └──5──> a program that runs
```

| Stage | Name | What it does | Who must trust it |
|---|---|---|---|
| 1 | lex | text becomes tokens | nobody |
| 2 | parse | tokens become a `Syntax` tree | nobody |
| 3 | elaborate | the tree becomes an `Expr` | nobody |
| 4 | check | the kernel checks the `Expr` | **everybody** |
| 5 | run | the term becomes a running program | a user, not a reader of a proof |

Stage 4 is small. Stages 1 to 3 are large, and they are untrusted, because the
kernel re-reads their output and checks it from nothing.

That is why this book builds stage 4 first.

---

## 2. The parts

### Part I — The ideas. Read this first.

Eight short chapters, and no code of ours. This is the Calculus of Inductive
Constructions, which is the theory Lean's kernel implements.

| # | Chapter | Adds |
|---|---|---|
| 1 | [A proof is a program](book/01-a-proof-is-a-program.md) | propositions as types |
| 2 | [Terms, binders, and names you do not need](book/02-terms-and-binders.md) | the language, substitution, de Bruijn indices |
| 3 | [Types that depend on values](book/03-types-that-depend-on-values.md) | the Pi type |
| 4 | [Prop, Type, and Sort](book/04-prop-type-and-sort.md) | the universes, and `imax` |
| 5 | [The Calculus of Constructions](book/05-the-calculus-of-constructions.md) | the five rules, and the limit they hit |
| 6 | [Inductive types, and the I in CoIC](book/06-inductive-types.md) | data, logic, recursors, ι, positivity |
| 7 | [Definitional equality](book/07-definitional-equality.md) | the relation the kernel decides, and `whnf` |
| 8 | [What you must trust](book/08-what-you-must-trust.md) | the kernel, the axioms, the second opinion |

[The contents of Part I](book/README.md) hold the dependency chain in one
picture.

### Part II — The kernel, built

Now the code. These two chapters turn Part I into a program that checks a
proof.

| # | Chapter | Adds |
|---|---|---|
| 9 | [The type checker](09-the-type-checker.md) | `alpha_eq`, the local context, `whnf`, `is_def_eq`, `infer_type` |
| 10 | [The environment and the five equations](10-the-environment.md) | a name with a value, δ, ι, η, proof irrelevance, projections |

### Part III — Meeting the real Lean

| # | Chapter | Adds |
|---|---|---|
| 11 | [The ground truth](11-the-ground-truth.md) | reading a file that the real Lean wrote |
| 12 | [Making it work](12-making-it-work.md) | `Nat` literals, K-like ι, quotients, strict positivity in code |

### Part IV — Making it trustworthy

| # | Chapter | Adds |
|---|---|---|
| 13 | [What a checker must check](13-what-a-checker-must-check.md) | a crafted proof of `False`, and the check that stops it |
| 14 | [What a theorem rests on](14-what-a-theorem-rests-on.md) | the axiom report, and unsafe isolation |
| 15 | [Mutual and nested](15-mutual-and-nested.md) | a group of types that refer to each other |

### Part V — The frontend

| # | Chapter | Adds |
|---|---|---|
| 16 | [The frontend](16-the-frontend.md) | stage 1, and why a Lean lexer holds no keyword list |

Part V needs only Part I chapter 1. Read it whenever you like.

### Part VI — What a kernel costs, measured

Ten chapters of measurement, in order. **Read them for the method, not for the
numbers.** Each one takes a single failure, measures it, and lets the
measurement overrule the plan. Four plans die that way.

| # | Chapter | The method it teaches |
|---|---|---|
| 17 | [Structures, and what the kernel costs](17-structures-and-cost.md) | what a term node must cache, and why |
| 18 | [The cache](18-the-cache.md) | a hash **finds** an answer, equality **decides** whether to trust it |
| 19 | [Compare before you unfold](19-compare-before-you-unfold.md) | take one failure out of 676 |
| 20 | [Ask the cheapest question first](20-ask-the-cheapest-question.md) | rank the failures by what each one blocks |
| 21 | [A hundred million](21-a-hundred-million.md) | when a profiler stops helping, count in the language of the problem |
| 22 | [What the others do](22-what-the-others-do.md) | read the other kernels. One of them had already found our bug. |
| 23 | [The last two hundred and forty-eight](23-the-last-two-hundred.md) | eleven hypotheses, and eight of them wrong |
| 24 | [The front door](24-the-front-door.md) | `rean check Demo.lean`, on a file of your own |
| 25 | [Twelve seconds](25-twelve-seconds.md) | measure against something that is not yourself |
| 26 | [Thirty-four per cent](26-thirty-four-per-cent.md) | six changes, three kept and three reverted |

### Part VII — A program that runs

| # | Chapter | Adds |
|---|---|---|
| 27 | [A program that runs](27-a-program-that-runs.md) | stage 5. Our evaluator runs a Lean program and matches Lean's output. |

### Part VIII — The outside test suite

| # | Chapter | Adds |
|---|---|---|
| 28 | [The arena](28-the-arena.md) | what a suite written by other people found that our own tests did not |

Chapter 28 belongs with Part IV, because it is about what a checker must
**refuse**. It reads last, because it measures everything the earlier parts
built.

### Appendix

| File | What it is |
|---|---|
| [The foundations in one file](00-introduction-to-the-kernel.md) | all of Part I, dense, in one file, for reference. Not a first read. |
| [The glossary](GLOSSARY.md) | every word |
| [The references](REFERENCES.md) | every source |
| [The roadmap](ROADMAP.md) | what is built, what is not, and the plan |

---

## 3. Three short paths

| You have | Read |
|---|---|
| 20 minutes | Part I chapter 1, and run `cargo run -p rean -- prove` |
| one evening | Part I chapters 1 to 5 |
| two evenings | all of Part I. You then know what Lean's kernel implements. |
| a week | Parts I to IV, and one chapter of Part VI |

---

## 4. What you miss if you skip

Sequence matters here, and this table is why.

| Skip | And you will not understand |
|---|---|
| Part I chapter 2 | why a bound variable is a number, so every term in the book looks wrong |
| Part I chapter 3 | why a checker has to compute at all |
| Part I chapter 4 | `imax`, `Prop`, erasure, and half of the kernel's rules |
| Part I chapter 5 | which rule each arm of `infer_type` implements |
| Part I chapter 6 | a recursor, a motive, a minor premise. Every later chapter uses those words. |
| Part I chapter 7 | the conversion rule, so every cost chapter will read as noise |
| Part II | the five functions that the rest of the code is made of |
| Part III | where the test data comes from, and why it is trustworthy |

---

## 5. Run it while you read

```sh
devbox shell
devbox run build
cargo run -p rean -- prove                                      # Part I, 1 and 5
cargo run -p rean -- check fixtures/lean4export/shapes.ndjson   # Part I, 6 and 7
cargo run -p rean -- lex examples/tokens.lean                   # Part V
cargo run -p rean -- demo                                       # the four stages
```

With a real Lean toolchain on the machine, point it at your own file:

```sh
cargo run --release -p rean -- show  Demo.lean twice
cargo run --release -p rean -- check Demo.lean --decl twice_two
cargo run --release -p rean -- run   Prog.lean main
```

Every claim in a chapter has a test, the chapter names it, and `tools/cite.py`
fails the build when a chapter names a test that nobody wrote.
