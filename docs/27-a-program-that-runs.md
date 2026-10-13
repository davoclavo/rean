# Chapter 27 — A program that runs

> **Where you are.** Chapter 27 of 28, Part VII of [the guide](README.md).
>
> **Before this.** [The environment](10-the-environment.md), for the
> reduction rules, and [the front door](24-the-front-door.md), which hands this
> chapter its terms.
>
> **After it you can** say how a checker and a runtime differ, and why this one
> is lazy.

The roadmap has had one line at the bottom of its table from the start:

> | later | LCNF and a backend | **a program that runs** |

This is that line, and the route to it was not the one the table drew.

```sh
rean run Prog.lean main
```

```text
export: Prog -> /tmp/rean-export/Prog.ndjson (4.6 MB) in 0.4s, by Lean 4.35.0-rc3
level 1: checked 1750 of 1750 declarations
hello from rean
fib 25 = 75025
  square of 0 is 0
  square of 1 is 1
  square of 2 is 4
  square of 3 is 9
  square of 4 is 16

main ran
6149 steps, 133 levels deep
```

**Lean's own `#eval main` prints those seven lines, byte for byte.** The whole
thing takes 0.97 seconds: Lean elaborates the file, our kernel checks every one
of the 1,750 declarations the program rests on, and our evaluator runs it.

---

## 27.1 Why this was reachable without a parser

The table expects stage 5 after stages 2 and 3, because that is the order a
compiler runs in. But stage 5 does not need our parser or our elaborator. It
needs an `Expr`, and chapter 24 built a front door that hands us the `Expr` of
any Lean program there is.

So the order of the **work** is not the order of the pipeline:

```
  Prog.lean ──[ Lean's parser ]──[ Lean's elaborator ]──> Expr
                                                           │
                           our kernel, stage 4  ───────────┤  is it correct?
                                                           │
                           our evaluator, stage 5 ─────────┘  what does it do?
```

Two of the four stages are ours, and they are the two that this project is
about: the one that decides whether a proof is correct, and the one that
decides what a program does. The two in the middle are Lean's, and chapter 24
says so every time it prints a line.

**The check is not optional.** `rean run` checks first and only the declarations
that pass go into the environment the evaluator runs against, so a refused
declaration cannot be run by accident. `--no-check` skips it and says that it
did.

---

## 27.2 A different job from the kernel

The kernel and the evaluator both reduce terms, and they are not the same
program.

| | the kernel, stage 4 | the evaluator, stage 5 |
|---|---|---|
| asks | is this term correct? | what does it come to? |
| universes | compares them, substitutes them | **ignores** them |
| types | infers them, compares them | ignores them |
| proofs | checks them | never looks inside one |
| order | the head, weakly | to a value, by need |
| numbers | a literal, with rules to keep it one | a machine integer, always |
| budget | fuel, by nodes built | a step count, so a loop ends |

The universe row is the one to sit with. Chapter 26 measured
`instantiate_levels` at 7% of a profile, and chapter 24 found it rebuilding
every node of every value the δ rule unfolds. **The evaluator drops every
universe argument on the floor**, because nothing it will ever do compares a
`Sort`. A stage that asks a smaller question can afford a smaller machine.

---

## 27.3 It is lazy, and that is not a taste

An argument becomes a thunk, and a thunk is forced at most once.

That is forced by the input, not chosen for elegance. An elaborated Lean term
carries arguments that **must not** be evaluated: the type arguments of a
polymorphic function, and the proofs that a dependent function asks for.
`List.map` takes two types before it takes a function. Lean's own compiler
**erases** them, which it can do because it knows their types. This evaluator
has no types at all, so it does the next best thing: it never forces what
nobody asks for.

The same property pays for itself twice over on real code:

```lean
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)
```

Read naively, `fib 25` is 242,785 calls. It took **2,571 steps**.

Lean compiles that recursion to `Nat.brecOn`, whose course-of-values table
holds an answer for every smaller number, and chapter 25 showed what the table
costs the **kernel**: `Nat.sub._f` unfolding a million times to build one. A
lazy table computes only the entries somebody projects, so the exponential
reading of `fib` becomes linear for free, and nobody wrote a memo table.

---

## 27.4 Three bugs, and all three are the same bug

The evaluator took a day and three of its failures were worth more than the
code.

### `2 + 2` came to `Nat.add ..2`

`Nat.add` is a primitive here, matched where a constant is the **head** of an
application. But `2 + 2` elaborates to `HAdd.hAdd Nat Nat Nat (instHAdd Nat
instAddNat) 2 2`, and that **projects** `Nat.add` out of a structure. So it
arrives as a value with no arguments, and the arguments come afterwards.
Appending them and stopping gave `Nat.add ..2`.

`apply` now asks `constant` again for any head the environment knows.

### A program ran its first statement and no more

```text
hello from rean
main ran
```

Two `IO.println` calls, one line of output, no error. The `do` block is a
`bind`, and a bind takes apart the value that the first action gave back. Our
runtime fabricates that value, because the effect is ours, and it fabricated
`EStateM.Result.ok`.

**Lean 4.35 calls it `EST.Out.ok.`** The recursor found no rule for the
constructor it was handed, stopped quietly, and the rest of the program never
happened. `io_ok` now asks the environment which of the names it holds.

### `toString` of a list came to `String.push ..2`

`text_of` knew what a `String` **is**: a structure over a `List Char`. That was
true of Lean once. In 4.35 a string is a byte array, `String.mk` goes through
`String.ofByteArray`, and reading one by projecting fields finds a byte array
where it wanted a list.

So it stopped knowing. `text_of` asks `String.toList` and `code_point` asks
`Char.toNat`, and both of those are stable across the versions that moved the
representation twice.

> **A runtime may know what a value means. It may not know what a value is
> made of.** Everything this evaluator hardcoded about a library type was
> wrong within one Lean release, and every one of those failures was **silent**:
> a program that did a third of its job, and no message.

---

## 27.5 What a primitive is, and why the list is short

Lean marks a handful of functions `@[extern]` and its compiler emits a call
into C. A runtime has to do the same work somewhere, and ours does it here.

- `Nat` arithmetic: `add`, `sub`, `mul`, `div`, `mod`, `pow`, `gcd`, the
  bitwise four, the shifts, and the three comparisons. Also `succ`, `pred` and
  `zero`, so that a number is a machine integer and never a tower.
- `String`: `append`, `push`, `length`.
- `IO.print` and `IO.println`.

**Everything absent from that list still runs**, through the definition Lean
exported, and the only cost is speed. That property is what keeps the list
honest: a primitive is a promise that our answer matches Lean's, so each one is
a thing to be right about, and `Nat.add` is a much smaller promise than
`List.foldl`.

The `IO` pair is the one place we cut higher up the chain than Lean does.
Lean's `IO.println` reaches `IO.getStdout`, which is a C function, and writes
through a stream whose fields are more C functions. A program that builds its
own stream will not run here. One that says `IO.println` will.

An `IO a` in Lean is a function of the state of the world, so running one is
handing it that state, and nothing looks inside the token.

---

## 27.6 What it runs

Measured, on one program per row, each one compared with Lean's `#eval`.

| Lean | ours | Lean's |
|---|---|---|
| `fib 25`, structural recursion | 75025 | 75025 |
| `(List.range 20).foldl (fun a n => a + n * n) 0` | 2470 | 2470 |
| `"hello, " ++ "world"` | "hello, world" | "hello, world" |
| a structure and a projection | `norm1 = 7` | `norm1 = 7` |
| an inductive and a `match` over it | `total = 24` | `total = 24` |
| `List.map` with a closure | `names = [a!, bb!]` | `names = [a!, bb!]` |
| `(Array.range 10).foldl (· + ·) 0` | `arr = 45` | `arr = 45` |
| `(some 7).getD 0` | 7 | 7 |
| a `do` block, `s!` interpolation, a `for` loop | seven lines | the same seven |

The limits, named rather than implied:

- A `String` built as a byte array needs `String.toList`, and the runtime asks
  for that **only if the program did**. Asking the exporter for it took one
  program from 4.6 MB to 16.9 MB and brought in the UTF-8 decoding family that
  chapters 24 and 25 are about: ten declarations our kernel cannot check at the
  default budget. The honest trade is to leave it out.
- A number past a `u128` is reported and not wrapped, exactly as the kernel
  reports it. A Lean `Nat` has no upper bound and this does.
- `IO` beyond `print` and `println` is not there.
- A `partial def` can loop, and the step budget is what ends it.

---

## 27.7 What this is not

It is a tree walking evaluator. Lean's stage 5 lowers to LCNF and then to C,
and this is the step the roadmap put before that: "the kernel term becomes
LCNF, then C code **or an interpreter call**".

So "compile" is still ahead, and the thing that is behind us is larger than it
sounds. Before this chapter, nothing in this repository could **do** anything
with a Lean program except say yes or no about it. Now it says yes, and then it
runs it, and the output matches the output of the compiler that elaborated it.

---

## 27.8 How other systems do it

Stage 5 is the stage where Lean stops being a proof assistant and becomes a
compiler, so this is the chapter with the most company.

| | Lean's stage 5 | ours |
|---|---|---|
| the form it works on | LCNF, then an IR, then C or an interpreter | the kernel `Expr` itself |
| types and proofs | **erased**, because the compiler knows the types | ignored, because we have no types. A thunk is never forced unless somebody asks. |
| order | strict, with an explicit thunk where Lean asks for one | lazy, by need |
| memory | reference counting, with an optimisation for a unique owner | Rust's own ownership, and a thunk cell |
| numbers | a machine number, with a big number library behind it | a machine integer |

Four notes.

- **Lean has an interpreter and a compiler.** `#eval` runs the interpreter,
  `src/library/ir_interpreter.cpp`, and `lake build` goes through LCNF to C.
  Our `rean run` is the first of those two, and the output of this chapter is
  compared against `#eval`.
- **Reference counting is a design, not an accident.** The paper *Counting
  Immutable Beans* is about the optimisation that makes it cheap in a pure
  language: when a value has one owner, update it in place.
- **Laziness is older than this chapter.** Launchbury wrote the semantics in
  1993 and the Spineless Tagless G-machine is how a real lazy runtime is built.
  Haskell is lazy by default for the whole language. OCaml and Rust are strict
  and offer a thunk when you ask. Lean is strict, and section 27.3 explains why
  **our** evaluator cannot be.
- **The free memo table is worth one more look.** Section 19.3 gets `fib 25` in
  2,571 steps rather than 242,785, because Lean compiled the recursion to
  `Nat.brecOn` and a lazy evaluator fills only the entries somebody reads. The
  same table costs the **kernel** a million steps, chapter 25, section 25.4.
  One table, two stages, opposite results.

## 27.9 References

**Our code**

- `crates/rean_eval/src/lib.rs`, the evaluator
- `crates/rean_eval/src/prim.rs`, the primitives of section 27.5
- `crates/rean_eval/tests/run.rs` and `crates/rean/tests/programs.rs`, which
  check our output against Lean's own answers

**Lean's own source**

- `src/Lean/Compiler/LCNF.lean` and the directory beside it, which is stage 5
  as Lean does it
- `src/library/ir_interpreter.cpp`, the interpreter that `#eval` uses

**Read more**

- Ullrich and de Moura, *Counting Immutable Beans*, 2019, for the memory model
  of Lean's stage 5. <https://arxiv.org/abs/1908.05647>
- Launchbury, *A natural semantics for lazy evaluation*, 1993, for a thunk
  forced at most once.
  DOI [10.1145/158511.158618](https://doi.org/10.1145/158511.158618)
- Peyton Jones, *Implementing lazy functional languages on stock hardware*,
  1992, for how a lazy runtime is built in earnest.
  <https://www.microsoft.com/en-us/research/publication/implementing-lazy-functional-languages-on-stock-hardware-the-spineless-tagless-g-machine/>
- *The Lean Language Reference*, run-time code, for what Lean guarantees about
  a program it compiles.
  <https://lean-lang.org/doc/reference/latest/Run-Time-Code/>
- *Functional Programming in Lean*, for Lean as a language that runs.
  <https://lean-lang.org/functional_programming_in_lean/>

---

**That is the whole book.** You read the theory in Part I, built the checker in
Parts II to IV, saw where a compiler begins in Part V, measured the cost in
Part VI, and ran a program in Part VII.

What is left is in [the roadmap](ROADMAP.md): our own parser, our own
elaborator, and the two checkpoints that need them. One thing comes before any
of that, and the next chapter is it: an outside test suite, and the fourteen
lies it caught us accepting.

---

**Next:** [The arena](28-the-arena.md)
