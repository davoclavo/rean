# Chapter 23 — The last two hundred and forty-eight

> **Where you are.** Chapter 23 of 28, in Part VI of [the guide](README.md). The
> lab notebook. Read it for the method.
>
> **Before this.** [What the others do](22-what-the-others-do.md).
>
> **After it you can** read a list of refuted hypotheses as a result, which is
> what most of a performance investigation produces.

The checker reads **57,264 of the 57,512** declarations of the Lean prelude.
That is 99.57%, and it took forty-four minutes at a budget forty times the
default.

This chapter is about the 248 that are left, and it is mostly a list of things
that turned out **not** to be the reason. Eleven hypotheses, each plausible,
eight refuted by a measurement. One ruled out a rewrite, one was worth twelve
declarations, and the last found a crash that every earlier measurement had read
as a slow run.

---

## 23.1 They are one family

```sh
./target/release/rean check full.ndjson > report.txt
python3 tools/roots.py report.txt
```

```text
68 failures block 180 declarations

blocked  root failure
     36  Int32.ofInt_eq_ofNat
     34  Int64.ofInt_eq_ofNat
     28  ..ISize.toInt_ofInt_of_le._proof_1_2
```

Every one of the 68 is a signed integer: `Int32`, `Int64`, `ISize`, and the
`Lean.Grind` instances for them. The tail is flat — the worst root holds up 36
declarations, where one of them once held up 15,272.

One family means **one cause**, probably. That is the good news and the trap.

---

## 23.2 Not the budget

The first thing to rule out, because it is the cheapest.

| budget | stack | result on the slice |
|---|---|---|
| 20,000,000 | 512 MB | fails |
| 800,000,000 | 8 GB | fails |
| **4,000,000,000** | **32 GB** | **still fails** |

Two hundred times the default budget, and a stack sixty times the default.
`Int32.ofInt_eq_ofNat` does not finish. Everything else in its slice does: 10,747
of 10,748.

§23.11 later found a better reason for this row than the one it was written
with. Those runs were not slow. They **crashed**, and a measurement that reads a
crash as a timeout is a measurement that has not been checked.

So there is a real inefficiency. The rest of this chapter is four attempts to
name it.

---

## 23.3 Not `u128` overflow, and my instrument was lying

`nat_lit.rs` names this limit in its own first paragraph:

> A Lean `Nat` has no upper bound. This module uses `u128`, so it refuses to
> compute past that. The real Lean kernel links a big number library.

And the failures are all 64-bit integer lemmas, with names like
`toInt_ofNat_of_lt_two_pow_numBits`. `2^64` and products of it are exactly
where `u128` runs out. The story was perfect.

The count of overflows was **zero**.

Worse, I had reported "`nat_step` never declines" from an instrument that
watched **one of its three exits**. The function can decline because a number
cannot be read, because the arithmetic overflows, or because it has fewer than
two arguments, and my counter sat on the first one only.

| decline | count |
|---|---|
| a number could not be read | 41, all `Nat.mul` |
| the arithmetic overflowed | **0** |
| fewer than two arguments | **0** |

**An instrument that watches one exit of three reports a fact about the
instrument.** That is the most useful thing in this chapter.

---

## 23.4 Not cache thrash

The declaration performs 447,907 ι steps. Our `whnf` cache clears itself at
200,000 buckets. So it clears twice and throws everything away, twice.

Twenty times the cache:

| `CACHE_CAP` | checked | time |
|---|---|---|
| 200,000 | 10,385 | **33 s** |
| 4,000,000 | 10,385 | 191 s |

Same answer, **six times slower**. A bigger cache costs memory and hashing and
buys nothing here. Reverted.

---

## 23.5 Not an under-applied `Nat.sub`

The δ tally has a suspicious pair:

```text
283,803  delta Nat.casesOn
220,996  delta Nat.mul.match_1
220,848  delta Nat.sub._f
 57,984  delta Nat.pow.match_1
```

`Nat.sub._f` is the compiled recursive body of `Nat.sub`, and unfolding it
builds a large term. We accelerate `Nat.sub` on two numbers, so reaching its
body means the fast path declined — and `instSubNat` holds `Nat.sub`
**unapplied**, so projecting that structure is exactly how an under-applied
`Nat.sub` would arise.

The count of "fewer than two arguments" was zero, and **`Nat.sub` itself never
appears in the δ tally at all.** Only `Nat.sub._f` does.

So the kernel never unfolds `Nat.sub`. Lean's exported proof terms **mention
`Nat.sub._f` directly**, because that is what the equation compiler left behind.
There is no `Nat.sub` application to accelerate. The subterm is simply there.

---

## 23.6 Not the universe substitution either

`Nat.casesOn` is unfolded 283,803 times, and each unfold substitutes the
universe arguments into its value, which walks the whole value. The same name
with the same levels gives the same body every time, so a cache keyed by name
and levels should remove 283,803 walks.

| | checked | time |
|---|---|---|
| without the cache | 10,385 | 33 s |
| with it | 10,385 | 35 s |

Nothing, and slightly slower. Reverted, by the rule chapter 20 set when
`rec.clone()` measured to nothing: a cache for an unmeasurable gain is a cost
with no payment.

---

## 23.7 Not lifting, and this one rules out a rewrite

Chapter 22 §22.7 named two cures, and both change what a term **is**. The
cheaper of the two is `nanobruijn`'s: keep a term as a pointer **plus a shift**,
so that lifting costs nothing and one cache entry serves every shifted variant
of a subterm.

That is a large change, and it touches every place that reads a de Bruijn index.
So measure first. Count how many lifts happen, how many of them do any work,
and how many nodes they walk.

```text
lift: 3,906,385 free, 0 real, 0 nodes walked
lift: 5,644,324 free, 0 real, 0 nodes walked
lift: 8,111,897 free, 0 real, 0 nodes walked
```

**Eight million lifts, and not one of them did any work.**

The reason is already in the kernel. `Expr::lift` begins

```rust
if amount == 0 || loose_range(self) <= cutoff {
    return self.clone();
}
```

and chapter 17 cached `loose` in every node precisely so that this test is O(1).
The values a β step substitutes come from the spine, and a term from the spine is
closed, so its lift is free. Every time.

So a representation that makes lifting O(1) would replace something that already
costs nothing. **One of the two remaining rewrites is ruled out, and no line of
it was written.** The other, normalisation by evaluation, is untouched by this
measurement.

This is the third plan this project has retired by measuring instead of
building, and the cheapest of the three to retire: twelve lines of counter and
one run.

---

## 23.8 What it actually is

With five explanations gone, the remaining reading is the plain one. For this
single declaration the kernel performs about **1.3 million reduction steps**:

```text
447,907  iota Nat.rec
283,803  delta Nat.casesOn
220,996  delta Nat.mul.match_1
220,848  delta Nat.sub._f
114,131  peel of the literal 4294967296
```

and each step **builds a term**. Chapter 21 measured 84 million nodes built for
a comparable declaration. There is no shortcut being missed. The work is being
done, correctly, one freshly built term at a time.

That is the cost of an **eager** `whnf`, and chapter 22 §22.7 already named the
two cures and the reason we have not taken them. Both change what a term **is**:

- ~~a term as a pointer **plus a shift**~~, ruled out in §23.7: our lifts
  already cost nothing;
- normalisation by evaluation, which the fastest checker in the arena uses, and
  which this chapter does **not** rule out.

The honest position is this. **99.57% is where an eager kernel with four caches
gets to.** The last 0.43% is not a missing rule, not a budget, and not a cache.
It is the representation, and changing it is a different project from the one
these fifteen chapters describe.

---

## 23.9 Lazy δ by height, which chapter 20 retired too early

One rule-level difference from Lean was still unbuilt. Lean records a **height**
for every definition in `ReducibilityHints`, and when two sides of a comparison
have different constant heads it unfolds only the **taller** one, then looks
again. Our `is_def_eq` called `whnf` on both sides, which unfolds each of them
until no rule applies at its head.

Chapter 20 §20.1 retired this on the evidence of one declaration, where the
profile showed the two heads already **matching** so the rule had nothing to do.
That was one declaration. Here is the same question asked of this family:

```text
is_def_eq past the quick tests:
   same head        882
   both unfold   19,783
   one unfolds   48,049
   neither          824
   not two constants  153,498
```

**31%** of the comparisons that get past the quick tests have two different
constant heads where at least one unfolds. So the rule does apply, often, and
chapter 20's conclusion was true only of the case it looked at.

So it is built. `whnf` splits in two: **core** reduction is every rule except δ,
and `lazy_delta` reduces both sides by core, then unfolds one of them.

```rust
let (unfold_left, unfold_right) = match (tall_left, tall_right) {
    (None, None) => return Ok((left, right)),
    (Some(_), None) => (true, false),
    (None, Some(_)) => (false, true),
    // Equal heights give no reason to prefer one, so take both.
    (Some(x), Some(y)) => (x >= y, y >= x),
};
```

### What it bought

| | checked | failed | time |
|---|---|---|---|
| before | 54,308 | 115 | 228 s |
| with lazy δ | **54,320** | **112** | 239 s |

**Twelve declarations and three failures, for 5% more time.**

That is a small payoff for about a hundred lines and a second cache, and it is
recorded here rather than dressed up. It is kept for two reasons. The gain is
real and repeatable, unlike the six changes above it that measured to nothing.
And it is the rule Lean states, which this project would rather own than
describe.

---

## 23.10 A test failed because the kernel got more correct

Building lazy δ broke one test, and the break is the interesting part.

The broken one was the control for proof irrelevance from chapter 20. Its name
is not written here in backticks, because the name no longer exists in the code
and `tools/cite.py` is right to refuse a citation that does not resolve.

It gave two terms a `Type` instead of a `Prop` and asserted that the comparison
would **run out of budget**, to prove that the test beside it passed because of
proof irrelevance and not because the terms were cheap.

With lazy δ it answered `Ok(true)` inside the budget. And it was right: those
two terms were **equal all along**. `Slow` unfolds through a `Wrap` that throws
its argument away, so it reduces to the very term it was compared with. The old
assertion was not measuring proof irrelevance. It was measuring the length of a
detour that eager reduction used to take.

So the control now tests the thing it was named for. `T` has **two**
inhabitants, and `Slow` reduces to the second one:

```rust
assert_eq!(tc.is_def_eq(&slow, &plain), Ok(false));   // in `Type`
assert_eq!(tc.is_def_eq(&slow, &plain), Ok(true));    // in `Prop`
```

The same two shapes, one answer each way, and the difference between them is
exactly what proof irrelevance is.

> **A test that asserts a cost is asserting the route, not the destination.**
> Make the route faster and the test fails while the kernel improves.

Every budget-based test in chapters 19 to 22 is open to this, and they earn
their place only where the cost is the **point** — unfolding a definition twice
when congruence would have settled it, or walking a tower of successors. Where
the point is the answer, assert the answer.

---

## 23.11 A profile, and the crash it was hiding

Nine hypotheses had come from reading the tally of which rules fire. The tenth
came from a plain profile of the hard workload, and it was not subtle.

**3,959 of 4,000 samples sat in one chain, more than a thousand frames deep:**

```text
read_nat → whnf → reduce → read_nat → whnf → reduce → ...   (× 340)
```

Everything else was far behind: `drop_slow` 1,779, `infer_type` 632,
`instantiate_levels` 503, `spine_eq` 445.

The cause is plain once seen. To compute `Nat.sub a b` the kernel must reduce
`a` first, and if `a` is itself `Nat.sub c d` then reducing it reduces `c`. The
descent is a **mutual recursion** between `read_nat` and `whnf`, so its depth is
the depth of the term — and §23.5 measured `Nat.sub._f` unfolding 220,848 times,
which is what builds a term that deep.

### The budget sweep was never a timeout

A sweep was running at the same time, and its result changes what §23.2 means:

```text
int slice at  4,000,000,000   crashed   345 s
int slice at 16,000,000,000   crashed   341 s
```

**The same duration at four billion units and at sixteen billion.** A budget
that is four times larger cannot take the same time unless the budget is not
what stopped it. It was the **stack**, overflowing at 32 GB.

So §23.2's conclusion — "not the budget" — was right, and for a reason better
than the one given there. No budget could **ever** close those declarations,
because the run died before it could spend one.

### The fix, and what it bought

`read_nat` now forces sixteen levels of nested arithmetic and then declines.
Declining is only slower and never wrong: the kernel falls back to unfolding.

| | result |
|---|---|
| before | **crashed** a 32 GB stack in 345 s |
| after | **completes** in 379 s, and reports 10,747 of 10,748 |

The failure that remains is honest instead of fatal, and a large budget became a
usable setting rather than a way to kill the process.

This was a regression of my own, from chapter 21. I capped the successor
**peeling** when `read_nat` first reached the top of a profile. That cap was
right and it left this one alone, because the recursion is not through peeling.
It is through `whnf` of an argument.

### And the cache that needs no confirmation

`nat_step` is tried on every reduction step whose head is a `Nat` operation, and
each try forces both arguments. A term that is not a number stays one, so the
answer is worth keeping. 38 seconds became 35.

That cache breaks chapter 18's rule on purpose, and the exception is the
interesting part. Chapter 18 §18.3 insists that a hash only **finds** an answer
and `alpha_eq` **decides**, because two terms can share a hash. Here a collision
makes the kernel call a number "not a number", so it declines and unfolds the
definition instead.

> **A cache may skip its confirmation exactly when being wrong costs time rather
> than truth.**

---

## 23.12 The part worth keeping

Eleven hypotheses, eleven measurements. Eight of them changed nothing in the
kernel, one bought twelve declarations, and the last two came from a plain
profile — one of which turned out to be a **crash** that had been reading as a
slow run for hours.

That reads like waste and is not, because each measurement **removed** something
from the list, and the list is what a future reader inherits. The next person to
open this file does not have to re-test the budget, the cache size, the overflow
path, the under-application, the universe substitution, the clone of a spine
that no rule reads, caching every term, **or the shift in the representation**.
They are all ruled out, with numbers, and the last of those
would have been a week of work.

And one of the five was worth the whole day on its own: the instrument that
watched one exit of three. Every number this project reports comes from an
instrument, and that one had been quietly telling me what I wanted to hear.

> Before you trust a count of something not happening, check that you are
> counting every way it could happen.

---

## 23.13 How other systems do it

The declarations that remain are proofs that Lean generated from a recursion on
a well founded order. Section 15.8 says what they are made of, and every system
has a version of this problem.

- **Lean compiles that recursion to `WellFounded.fix`**, which computes through
  `Acc.rec`. The kernel then has to reduce a proof of accessibility to get one
  step of the function. That is why a one-line Lean definition can cost a
  checker a million unary steps, and chapter 25, section 25.4 names the
  declaration that does it.
- **Rocq's `Program Fixpoint` and `Function` do the same thing**, and the same
  reduction cost appears there.
- **A deep recursion needs a big stack in any language.** Our `whnf` walks a
  term by recursion, so the work budget and the stack are coupled, and section
  15.11 is a crash that eight earlier measurements had read as a slow run.
  `rustc` answers this by running the compiler on a thread with a large stack,
  and Lean's kernel answers it with a recursion depth guard that raises an
  error before the stack runs out.

One note on method. Eight of the eleven hypotheses here were wrong, and the
chapter keeps them. A performance report that lists only the change that worked
teaches nobody where the time went.

## 23.14 References

**Our code**

- `crates/rean_kernel/src/typeck.rs`, the δ step by height of section 23.9
- `crates/rean_kernel/tests/sweep_last.rs` and `tests/limits.rs`
- `tools/roots.py`, the ranking of section 23.1

**Lean's own source**

- `src/kernel/type_checker.cpp`, the function `lazy_delta_reduction_step`,
  which is the height rule we tried, and `scope_rec_depth`, which is the depth
  guard
- `src/Lean/Elab/PreDefinition/WF/`, where Lean turns a recursion on a well
  founded order into `WellFounded.fix`

**Read more**

- Carneiro, *The Type Theory of Lean*, for `Acc` and what its recursor costs.
  <https://github.com/digama0/lean-type-theory>
- The Lean Kernel Arena, for the declarations other checkers find hard.
  <https://arena.lean-lang.org/>

---

**Next:** [The front door](24-the-front-door.md)
