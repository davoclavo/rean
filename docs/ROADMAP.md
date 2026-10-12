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
| **B** the kernel | `Expr` | yes or no | works. Every reduction rule, plus strict positivity. |
| **B** the importer | `.ndjson` | `Environment` | works |
| **B** the front door | `.lean` text | `.ndjson` | works, **by calling the real Lean**. See chapter 16. |

The two islands still do not touch. Nothing in a `.lean` file reaches the kernel
**through our own stages**. But island B now reads real Lean terms, so it is
testable on its own, and the front door makes that one command:

```sh
rean check Demo.lean --decl twice_two     # 39 declarations, all of them checked
rean check prelude                        # 59,349 declarations
```

Read that row carefully. The front door is Lean's elaborator, not ours. It
closes the **ergonomic** gap, not the pipeline gap, and the usage text says so,
because a reader must not mistake it for a parser.

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
| 4 | `Nat` literals, K-like ι, the quotient rules, strict positivity, coverage. **Done.** | a checker that handles what a beginner writes |
| 5 | recursor shape and rule checking, large elimination, universe hygiene, structure eta. **Done.** | a checker that is hard to **lie to** |
| 6 | derived minor premises, the axiom trust report, unsafe isolation. **Done.** | a plain declaration is hard to lie to |
| 7 | mutual groups, nested positivity, the inductive universe constraint. **Done.** | a mutual or nested declaration is hard to lie to as well |
| 7b | a **mutual fixture**, full recursor re-derivation, `Quot` types | the ordering of chapter 7 validated against real Lean |
| 5 | the Pratt parser, with the extensible precedence table | `Vec<Token>` becomes `Syntax` |
| 6 | the elaborator: name resolution, implicit arguments, unification | **Level 2 opens** |
| 7 | metavariables, instance search, tactics | real proofs from real text |
| 8 | the exporter | closes the loop. Short, by then. |
| later | LCNF and a backend | a program that runs |

Chapter 16 sits outside that table on purpose. It adds no rule and no stage. It
makes the kernel **reachable**, and it turns the one answer a report cannot
carry — a stack overflow — into a verdict.

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

## Speed, measured

The checker now runs the **whole Lean prelude** and finishes.

```
level 1: checked 54308 of 57512 declarations (115 failed, 3089 blocked)
trust: 7 axiom(s): Classical.choice, Lean.ofReduceBool, Lean.ofReduceNat,
                   Lean.trustCompiler, Quot.sound, propext, sorryAx
real 252s
```

Getting there took three measurements and one wrong guess.

### What the profile said, and what it did not

| Frame | Before | After |
|---|---|---|
| `Arc<Expr>::drop_slow` | 121,445 | **7,982** |
| `drop_glue::<Expr>` | 55,427 | **3,906** |
| `Expr::instantiate_at` | 35,385 | 41,436 |

Substitution rebuilt every node of every subterm, even where nothing changed,
and then dropped the lot. `instantiate_at`, `lift` and `abstract_fvar` now
return `None` for "nothing changed", so an unchanged subterm keeps its existing
`Arc` and costs one reference count bump.

Then I guessed. `instantiate` lifts the substituted value once **per
occurrence**, so I made it compute "is this value closed" up front and skip the
lift. That is a real quadratic in theory and it was not the one being paid: the
profile had `lift_opt` at 4,790 against `instantiate_at` at 41,436. The change
took a 487 declaration slice from under a second to **88 seconds**, because the
up front check costs the size of the value on every call while the lift it
replaced was already free at depth zero.

**Measure the thing you are about to change, not the thing next to it.**

### Fuel must pay for work, not for steps

A budget of two million steps still let one `BitVec` theorem reduce for minutes.
The reason is that an ι step **makes the term larger**, so one step can cost
unboundedly much. A budget that counts steps does not bound anything.

So a step is now charged the size of the term it produced, and
[`Expr::size_up_to`] caps that count, because an `Expr` shares its subterms and
counting every node of the tree would be the very blow up this measures.

The budget itself comes from a sweep, not from taste:

| budget | the 487 slice | the prelude | time |
|---|---|---|---|
| 2 million | 465 of 487 | 31,426 | 115 s |
| **20 million** | **483 of 487** | **33,539** | **196 s** |
| 200 million | 483 of 487 | did not finish | |

`REAN_FUEL` overrides it, so a reader can see for themselves what a smaller one
gives up.

One bug in that sweep is worth recording: the first run of it reported
**identical** numbers for every budget, because `check_declaration` reset the
fuel to the constant and overwrote the override. A sweep that cannot move its
own variable measures nothing, and three equal rows should have been the clue.

### What is left, and the honest fix

Both caches named below are now **done**, and chapter 9 reports what each one
bought. The summary:

| change | checked | time |
|---|---|---|
| start | 33,539 | 198 s |
| `loose` cached in every node | 33,539 | 181 s |
| `size` cached too | 33,539 | 160 s |
| three structure rules | 33,855 | 185 s |
| a cheap guard before `infer_type` | 33,862 | 171 s |
| a name compared without a `String` | 33,862 | 163 s |
| a cache on `whnf` | 34,419 | 172 s |
| a cache on `is_def_eq` | 35,115 | 190 s |
| compare before you unfold | 39,066 | 205 s |
| proof irrelevance first, and an `infer_type` cache | 39,244 | 192 s |
| read a number in constructor form, and a linear trust report | 48,804 | 141 s |
| charge a step for what it adds, and charge for inference | 54,187 | 291 s |
| a batched β spine, and a cap on reading successors | 54,308 | 252 s |
| **lazy δ by height** | **54,320** | **239 s** |

Read the first three rows together. The `loose` and `size` caches moved the
**time** and not the **count**, because the budget is charged by work and a
faster kernel does the same work faster. That is worth reading twice before
trusting any performance claim.

Of these, the two caches moved the count by making the work smaller. The last
row moved it by making the work **unnecessary**, and it is the smallest diff of
them all: `spine_eq` already existed, and the change is where it is called. See
chapter 11, which is as much about how the fault was found as about the fix.

Raising the budget then found a third fault that had nothing to do with either:
a **stack overflow**. The kernel recurses over terms, a reduced term can be very
deep, and 8 MB of main thread stack is not enough. The checker now runs on a
thread with 512 MB, as `rustc` does.

Of the 115 failures that remain, **112 are out of budget** —
`WellFounded.Nat.fix_eq`, `Nat.modCore_eq_mod`, and their relatives, all well
founded recursion. The other 8 are one cascade from a single rejected
constructor, and not a gap in the rules.

Both caches are now **done**, and they are the first changes that moved the
declaration count rather than only the time. Together they took 1,287
declarations out of `blocked`, and 1,253 of those passed. Chapter 10 reports
them, including the threshold sweep and the one rule that keeps a cache in a
proof checker honest: a hash **finds** an answer, and `alpha_eq` **decides**
whether to trust it, because two terms can share a hash and a checker may not be
probably right.

The same measurement removed a **second** limit inside `whnf` that had a
constant of its own. The budget already bounded that loop, because a step spends
a unit before it tries any rule, so the second limit could only fire earlier and
then report the wrong cause: "reduction did not stop" for a declaration that was
correct and simply expensive. It changed no verdict and cost about 33 s at the
larger budget. We kept the removal for the message and for one constant fewer.

**Lazy δ by height is retired, unwritten.** Chapter 12 followed the method onto
`Nat.mul_add_div._f` and the profile showed the two heads already **matching**,
so a rule that picks the taller of two different heads had nothing to do. That
is the second plan this roadmap has dropped without writing a line of it, and
both times the measurement was cheaper than the code.

One item is left:

- Our `whnf` is **eager** and rebuilds a whole term for each step, which is why
  `drop_slow` sat at the top of our profile and not of Lean's. Lean's `whnf` is
  lazy. This is a change to every rule.

**The budget matters again, and that is because the work got cheaper.** Chapter
12 recorded "the budget is no longer the lever" and that sentence was true for
the code it was measured on. After chapter 13 it was false: a larger budget buys
real work once the waste is gone. A conclusion about a knob is only true for the
code you measured it on.

| budget | checked | failed | time |
|---|---|---|---|
| 20,000,000, the default | 54,308 | 115 | 252 s |
| 800,000,000 | **57,264** | 68 | 2,637 s |

Those two rows are Lean 4.27 and the numbers that chapters 13 to 15 measured.
Chapter 16 re-measured against Lean **4.35.0-rc3**, which is a different and
larger prelude, and the first row of the new table is the one to compare
against:

| settings, Lean 4.35.0-rc3 | checked of 59,349 | failed | blocked | time |
|---|---|---|---|---|
| default | 55,754 | 74 | 3,521 | 209 s |

And one row of the old table was never a timeout. At a hundred times the default
budget the run **crashed**, after 16,583 declarations, on a 4 GB stack. Chapter
16 section 16.4 has it. The kernel now measures the stack it has used and
reports `OutOfStack`, so a large budget is a setting and not a way to kill the
process.

At the larger budget that is **99.57%**, and the 68 that remain are one family:
`Int32`, `Int64`, `ISize`. Chapter 15 asks **nine** questions of them. Eight answers changed nothing,
including the budget at two hundred times the default and one of the two
rewrites chapter 14 had named. The ninth, **lazy δ by height**, is now built and
bought twelve declarations: chapter 12 had retired it on the evidence of a
single case, and 31% of the comparisons in this family turn out to need it.

What is left is normalisation by evaluation, and that is a different project.

**At the default budget one declaration blocks 2,690 of the 3,089 that
remain**, which is 87% of them. `tools/roots.py` says so, and it keeps saying something different each
time, so run it again rather than trusting the last answer:

```text
115 failures block 3089 declarations

blocked  root failure
   2690  ..String.Decode.0.ByteArray.utf8DecodeChar?.assemble₄._proof_3
     57  Lean.Grind.Ring.OfSemiring.mul_helper
     45  ..String.Decode.0.String.utf8EncodeChar_eq_utf8EncodeCharFast._proof_1_12
```

That one passes at a budget of **800,000,000**, in thirty seconds. So the
remaining question is the budget and the time it costs, not whether the kernel
can do it.

**What chapter 14 took from the other external checkers**, and what it did not:

- **Taken:** three-valued proof irrelevance, from a `nanoda` bug report. It
  bought nothing on our input and is right anyway.
- **Taken:** a batched β spine, from `nanoclo`'s delayed instantiation. Our step
  was the O(n²) version it names.
- **Ruled out by measurement**, chapter 15 §15.7: a term as a pointer **plus a
  shift**, as `nanobruijn` does. Eight million lifts in one declaration and
  **not one did any work**, because the `loose` number chapter 9 caches already
  makes a lift of a closed term free. That rewrite would replace something that
  costs nothing.
- **Not taken:** normalisation by evaluation, which the fastest checker in the
  arena uses.

The last two change the representation of a term, which is the one change that
would cost this project its ergonomics. Neither is needed to read the prelude.
The current profile says where they would pay: the drop of terms the kernel
built and discarded is the heaviest frame, with `infer_type` behind it.

## The one number

Each level reports one number. Put all three in the README and move them up.

```
level 1   our kernel checks        95 of 95 on the two committed fixtures
          and                   55754 of 59349 of the Lean prelude, in 209 s
          and                   59199 of 59349 at REAN_FUEL=2000000000
                                                 REAN_STACK=8192, in 36 min
level 2   our elaborator inhabits     0 types              <- needs a parser
level 3   our term matches Lean's     0 terms

tests     467
coverage  see devbox run coverage
red team  39 lies refused, each one once accepted
trust     every axiom reported, by name
crashes   none, at any setting
```

99.75%, and the 45 failures that remain are one family of signed integer
lemmas. **No rule is missing**, and chapter 16, section 16.7, is the correction
of the sentence that chapter 15 ended on.

**There is an oracle for speed now, and it is not us.** `leanchecker Init`, the
kernel of the Lean that made this export, re-checks the whole prelude in
**12 seconds** and fails nothing. Chapter 17 has the table. That number is the
one to work against, because fifteen chapters of measuring against our own last
week is how chapter 15 reached a conclusion that chapter 16 had to take back.

Those 45 split in two, and the split is what to work on next:

- **5 want budget**, and they reach it. One of them passes at
  `REAN_FUEL=8000000000`, in five minutes of real work for one theorem.
- **40 want stack**, and that knob does not reach them. The stack was doubled
  from 8 GB to 16 GB and **not one of them closed**. They need Rust stack
  because the descent into a major premise is a Rust recursion, so the cure is
  an evaluator with an explicit stack, on the heap. That is the measured case
  for normalisation by evaluation, and it replaces the guess that chapter 14
  recorded.

The first number cannot grow without a bigger fixture, and the ordering of a
mutual recursor is still **unvalidated against real Lean**. Getting a mutual
fixture is the highest value item left, and `rean export` now makes one in a
command. See `fixtures/lean4export/PROVENANCE.md`.

## Four kinds of oracle

The project now uses four, and each one found something the others could not.

| Oracle | Finds | Found |
|---|---|---|
| **ground truth**, a real Lean file | shapes nobody writes by hand | a projection at the head of an application spine |
| **coverage**, `devbox run coverage` | paths that no data took | a driver that could not be tested, and two dead branches |
| **red team**, a crafted lie | checks that are absent | a recursor that smuggled in an axiom and proved `False` |
| **another checker**, `leanchecker` | how far off our **speed** is | 12 seconds against our 209, on the same input |

The fourth is new in chapter 17 and it is the one that changes what the others
mean. A project that measures only against itself can learn that it is
improving and nothing else.

The third is still the one to grow. See chapter 5, section 5.8, for the full
inventory of what a checker must check and where we stand.

## Coverage is part of the oracle

Chapter 3 said the ground truth beats a hand written test. Chapter 4 found the
other half of that: **one real module exercises only the paths that one module
needs.** The chapter 3 fixture left the NDJSON reader at 72%, because it has no
`letE`, no `mdata`, no literal, no `axiom`, no `opaque`, and no `quot`.

So the two are complementary, not substitutes:

- **Ground truth** proves the paths that real data takes, and finds shapes
  nobody would write by hand. It found a projection at the head of a spine.
- **Coverage** finds the paths that no data took. It found a driver that could
  not be tested, and two dead branches in `level.rs`.

Target every branch that an input can reach, not a round number. See chapter 4,
section 4.6, for the 51 lines that stay and why.

That beats a hand written test as a correctness oracle, and it is how the other
independent checkers were built.
