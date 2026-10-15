# How Lean 4 is built, from the ground up

This is a book about one question: **how does a computer check a proof?**

It answers the question by building the thing. Part I is the theory that Lean 4
rests on, and it is written in TypeScript. Parts II to VII build a working proof
checker in Rust, point it at the real Lean library, and measure what it costs.

Start at [Part I chapter 1](book/01-a-proof-is-a-program.md). It assumes
nothing.

---

## How to read this

**In order.** Each chapter adds one thing, and the next one uses it. The order
is not a suggestion, and the table in section 4 says exactly what you miss if
you jump.

**In a language you already read.** Part I holds no Lean syntax and no code of
ours. Every idea in it arrives as a TypeScript type and one short function, so
you can read the whole theory before you meet a new language. Lean syntax
arrives in chapter 12, where a file that the real Lean wrote arrives with it.

**With the `Try it` section.** Every chapter has one. In Part I it is TypeScript
you can paste into a playground, and it ends by telling you what to break. From
chapter 10 on it is a command line. Run it either way. A rule you have watched
run is a rule you keep.

**Kindly.** Nothing here is obvious. Where a part is hard, it says so. Where a
question catches everybody, it is answered rather than avoided.

**One note on numbers.** The chapters run from 1 to 30 with no repeats.
Part I holds 1 to 9 and lives in `docs/book/`. The chapters that build the
checker hold 10 to 30. A reference into Part I is written in full, as
"Part I chapter 5", because Part I sits in a folder of its own.

**If you write TypeScript.** You already use most of the ideas here under other
names. The glossary opens with a table that maps them:
[if you come from TypeScript](GLOSSARY.md#if-you-come-from-typescript).
Every chapter of Part I also has a section called **If you write TypeScript**,
which puts the chapter next to `never`, `unknown`, a discriminated union, a
conditional type, the `tsc` error `TS2589`, or the three channels of
`Effect<A, E, R>`.

**How Part I is built.** Every section of Part I runs the same four beats:
**the idea** in plain words, then **the data** as a type, then **the code** as
one short function, then **the rule** as notation. An idea comes before a type,
a type comes before code, and code comes before a formula, with no exceptions.
[The contents of Part I](book/README.md) states the method and names the seven
books it comes from.

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

Nine short chapters. No Lean syntax, and no code of ours. This is the Calculus
of Inductive Constructions, which is the theory Lean's kernel implements, and
every type in it is a TypeScript type you can paste into a playground.

| # | Chapter | Adds |
|---|---|---|
| 1 | [A proof is a program](book/01-a-proof-is-a-program.md) | propositions as types |
| 2 | [Every type the kernel has](book/02-every-type-the-kernel-has.md) | the five types the whole job is written in |
| 3 | [Terms, binders, and names you do not need](book/03-terms-and-binders.md) | the language, substitution, de Bruijn indices |
| 4 | [Types that depend on values](book/04-types-that-depend-on-values.md) | the Pi type |
| 5 | [Prop, Type, and Sort](book/05-prop-type-and-sort.md) | the universes, and `imax` |
| 6 | [The Calculus of Constructions](book/06-the-calculus-of-constructions.md) | the five rules, and the limit they hit |
| 7 | [Inductive types, and the I in CoIC](book/07-inductive-types.md) | data, logic, recursors, ι, positivity |
| 8 | [Definitional equality](book/08-definitional-equality.md) | the relation the kernel decides, and `whnf` |
| 9 | [What you must trust](book/09-what-you-must-trust.md) | the kernel, the axioms, the second opinion |

[The contents of Part I](book/README.md) hold the dependency chain in one
picture.

### Part II — The kernel, built

Now the code, and it is Rust. These two chapters turn Part I into a program that
checks a proof.

| # | Chapter | Adds |
|---|---|---|
| 10 | [The type checker](10-the-type-checker.md) | `alpha_eq`, the local context, `whnf`, `is_def_eq`, `infer_type` |
| 11 | [The environment and the five equations](11-the-environment.md) | a name with a value, δ, ι, η, proof irrelevance, projections |

### Part III — Meeting the real Lean

Lean syntax starts here, because the input of chapter 12 is a file that the real
Lean wrote.

| # | Chapter | Adds |
|---|---|---|
| 12 | [The ground truth](12-the-ground-truth.md) | reading a file that the real Lean wrote |
| 13 | [Making it work](13-making-it-work.md) | `Nat` literals, K-like ι, quotients, strict positivity in code |

### Part IV — Making it trustworthy

| # | Chapter | Adds |
|---|---|---|
| 14 | [What a checker must check](14-what-a-checker-must-check.md) | a crafted proof of `False`, and the check that stops it |
| 15 | [What a theorem rests on](15-what-a-theorem-rests-on.md) | the axiom report, and unsafe isolation |
| 16 | [Mutual and nested](16-mutual-and-nested.md) | a group of types that refer to each other |

### Part V — The frontend

| # | Chapter | Adds |
|---|---|---|
| 17 | [The frontend](17-the-frontend.md) | stage 1, and why a Lean lexer holds no keyword list |

Part V needs only Part I chapter 1. Read it whenever you like.

### Part VI — What a kernel costs, measured

Ten chapters of measurement, in order. **Read them for the method, not for the
numbers.** Each one takes a single failure, measures it, and lets the
measurement overrule the plan. Four plans die that way.

| # | Chapter | The method it teaches |
|---|---|---|
| 18 | [Structures, and what the kernel costs](18-structures-and-cost.md) | what a term node must cache, and why |
| 19 | [The cache](19-the-cache.md) | a hash **finds** an answer, equality **decides** whether to trust it |
| 20 | [Compare before you unfold](20-compare-before-you-unfold.md) | take one failure out of 676 |
| 21 | [Ask the cheapest question first](21-ask-the-cheapest-question.md) | rank the failures by what each one blocks |
| 22 | [A hundred million](22-a-hundred-million.md) | when a profiler stops helping, count in the language of the problem |
| 23 | [What the others do](23-what-the-others-do.md) | read the other kernels. One of them had already found our bug. |
| 24 | [The last two hundred and forty-eight](24-the-last-two-hundred.md) | eleven hypotheses, and eight of them wrong |
| 25 | [The front door](25-the-front-door.md) | `rean check Demo.lean`, on a file of your own |
| 26 | [Twelve seconds](26-twelve-seconds.md) | measure against something that is not yourself |
| 27 | [Thirty-four per cent](27-thirty-four-per-cent.md) | six changes, three kept and three reverted |

### Part VII — A program that runs

| # | Chapter | Adds |
|---|---|---|
| 28 | [A program that runs](28-a-program-that-runs.md) | stage 5. Our evaluator runs a Lean program and matches Lean's output. |

### Part VIII — The outside test suite

| # | Chapter | Adds |
|---|---|---|
| 29 | [The arena](29-the-arena.md) | what a suite written by other people found that our own tests did not |
| 30 | [The eleven that were not wrong](30-the-eleven.md) | the exit code as an interface, and a tree walk over a graph |

Part VIII belongs with Part IV, because it is about what a checker must
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
| 20 minutes | Part I chapters 1 and 2. No toolchain needed. |
| one evening | Part I chapters 1 to 6 |
| two evenings | all of Part I. You then know what Lean's kernel implements. |
| a week | Parts I to IV, and one chapter of Part VI |

---

## 4. What you miss if you skip

Sequence matters here, and this table is why.

| Skip | And you will not understand |
|---|---|
| Part I chapter 2 | the name of anything. Every later chapter points at a type this one gives. |
| Part I chapter 3 | why a bound variable is a number, so every term in the book looks wrong |
| Part I chapter 4 | why a checker has to compute at all |
| Part I chapter 5 | `imax`, `Prop`, erasure, and half of the kernel's rules |
| Part I chapter 6 | which rule each arm of `infer_type` implements |
| Part I chapter 7 | a recursor, a motive, a minor premise. Every later chapter uses those words. |
| Part I chapter 8 | the conversion rule, so every cost chapter will read as noise |
| Part II | the five functions that the rest of the code is made of |
| Part III | where the test data comes from, and why it is trustworthy |

---

## 5. Run it, from chapter 10 on

Part I needs nothing installed. From chapter 10 the book builds a program, and
these are its commands.

```sh
devbox shell
devbox run build
cargo run -p rean -- prove                                      # chapters 10 and 11
cargo run -p rean -- check fixtures/lean4export/shapes.ndjson   # chapters 12 and 13
cargo run -p rean -- lex examples/tokens.lean                   # chapter 17
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
