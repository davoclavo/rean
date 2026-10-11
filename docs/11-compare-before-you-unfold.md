# Chapter 11 — Compare before you unfold

Chapter 10 ended with 676 declarations of the Lean prelude out of budget, all of
them well-founded recursion, and a plan: make `whnf` lazy.

The plan was wrong, and one measurement said so. This chapter is about that
measurement, because the method matters more than the fix.

```sh
devbox run -- cargo test -p rean_kernel --test comparison
```

---

## 11.1 Look at one declaration, not at 676

676 failures with one cause is a guess. A guess about 676 things is worse than a
guess about one.

So the first step was to get **one** of them alone. The export is in topological
order, so a prefix of the file is a module in its own right: every index a line
mentions is defined on an earlier line. Cut the file after the declaration you
want, and you have its dependencies and nothing else.

`Nat.modCore_eq_mod` is the first real failure of the prelude. Its prefix holds
886 declarations, and the slice checks in **under a second**.

Then the question that changed everything: how much budget does that one
declaration want?

| budget | result |
|---|---|
| 20,000,000 | failed |
| 100,000,000 | failed |
| **500,000,000** | **passed, in 1 second** |

Read the last row. The declaration is **not slow**. It wants 25 times the
default budget and takes one second to spend it.

The budget is charged by work, and this slice spent somewhere above 100 million
units in about a second. So a budget of 20 million is, in practice, a small
fraction of a second per declaration. We were refusing correct Lean for want of
that fraction.

---

## 11.2 But a bigger budget was not the answer either

The obvious move is to raise the budget. So I raised it, a long way, on a slice
of 1,905 declarations.

| budget | checked | time |
|---|---|---|
| 2,000,000,000 | 1,896 | 17 s |
| 8,000,000,000 | 1,896 | 54 s |
| 32,000,000,000 | 1,897 | 142 s |

One more declaration for sixteen times the budget. A term that wants **32
billion** units of work is not a term Lean struggles with, and Lean checks this
whole file in seconds.

So the budget was hiding a real fault, and the fault was ours. Two facts about
the shape of the work now had to be explained, not worked around:

1. The work is **enormous**, far beyond what the theory needs.
2. It is also **cheap per unit**, so it is not one hard reduction. It is a very
   large number of easy ones.

A very large number of easy reductions means the kernel is reducing something it
did not have to reduce at all.

---

## 11.3 What it was reducing, and why it did not have to

Here is the order `is_def_eq` used to ask its questions.

```rust
if a.alpha_eq(b) { return Ok(true); }   // are they the same term?
let a = self.whnf(a)?;                  // no. So reduce both,
let b = self.whnf(b)?;                  // and then look at the shape.
```

`whnf` reduces the head, and **δ is one of the head rules**. So when the two
sides are

```text
Nat.modCore x y   ≟   Nat.modCore x y'
```

the kernel unfolds `Nat.modCore` on the left, unfolds it on the right, and then
compares two much larger terms. `Nat.modCore` is defined by well-founded
recursion, so each unfolding drags in `WellFounded.fix`, `Acc.rec`, and the
accessibility proof. That is where the billions of units went.

And none of it was necessary. The two sides have the **same head**. If the
arguments are equal, the terms are equal, by congruence. The question to ask
first costs the arguments, not the unfolding:

```rust
if self.spine_eq(a, b)? {
    return Ok(true);
}
let a = self.whnf(a)?;
```

`spine_eq` already existed, and the whole change is **where it is called**. It
used to run after both sides were reduced, which is exactly too late.

Lean's kernel asks in this order too, and now the reason is clear.

### Why a `false` answer must not be trusted

`spine_eq` returning `false` does **not** mean the terms differ. `Nat.add 1 1`
and `Nat.add 2 0` have the same head and unequal arguments, and they are the
same number.

So only a `true` answer is a decision. A `false` answer falls through to the
full comparison, which is unchanged. This is the same discipline as the cache of
chapter 10, read from the other side: there, a hit had to be confirmed; here, a
miss must not conclude.

Test: `a_shared_head_with_unequal_arguments_falls_through`.

---

## 11.4 A test that measures work, not time

A performance fix needs a test, or the next person undoes it. But a test that
reads a clock is a test that fails on a slow machine and passes on a fast one.

The budget is a **count**. It is the same on every machine and in every run. So
the test sets a budget that is far too small to unfold the head, and asks for
the right answer anyway:

```rust
tc.set_fuel(2_000);
let left = Expr::const_("Big", vec![]).app(Expr::const_("E", vec![]));
let right = Expr::const_("Big", vec![]).app(Expr::const_("Nat", vec![]));
assert_eq!(tc.is_def_eq(&left, &right), Ok(true));
```

`Big` is 1,201 nodes, so unfolding it on both sides cannot fit in 2,000 units.
The test passes only if the kernel compares before it unfolds.

And one test is not enough, because the terms might simply be cheap. The
control gives the two sides **different** heads, so there is nothing to compare
and the unfolding must happen:

```rust
assert_eq!(tc.is_def_eq(&left, &nat), Err(TypeError::OutOfFuel(2_000)));
```

I checked that the first test fails without the fix. **A regression test that
passes both ways is not a test.** It took one revert and one run to find out,
and it is the only way to know.

Tests: `the_same_head_is_compared_before_it_is_unfolded`,
`a_different_head_still_costs_the_unfolding`.

---

## 11.5 What it bought

| | checked | failed | blocked | time |
|---|---|---|---|---|
| chapter 10 ended at | 35,115 | 684 | 21,713 | 190 s |
| compare before unfold | **39,066** | **229** | 18,217 | 205 s |

3,951 more declarations, and **two thirds of the failures gone**, for one moved
line and 15 seconds.

Put it beside the rest of the session and the shape is plain:

| change | declarations gained |
|---|---|
| cache `loose` and `size` in every node | 0 |
| one bound instead of two | 0 |
| a cheap test before `infer_type` | 7 |
| `Name::two_parts` | 0 |
| three structure rules | 316 |
| cache `whnf` | 557 |
| cache `is_def_eq` | 696 |
| **compare before you unfold** | **3,951** |

Every other change made the same work faster or smaller. This one made the work
**unnecessary**, and that is a different kind of win. It is also the smallest
diff of the eight.

---

## 11.6 The method, which is the real lesson

The fix is three lines. Finding it took five steps, and none of them was a
guess.

1. **Take one case, not the class.** 676 failures became one declaration, and
   one declaration fits in a second.
2. **Ask what it wants, not whether it fails.** The budget sweep said 500
   million, and that number was the whole clue.
3. **Follow the number where it leads, even away from your plan.** The plan was
   a lazy `whnf`. The number said the work should not happen at all, which is a
   different fix and a much smaller one.
4. **Explain both halves of what you see.** The work was huge *and* cheap per
   unit. Either fact alone is unremarkable. Together they say the kernel is
   reducing something it never needed to touch.
5. **Make the test measure the thing you fixed.** The budget is a count, so the
   test is deterministic. Then break the fix on purpose and watch the test fail.

Chapter 10 reported two changes that moved no declaration at all. This chapter
is why that reporting mattered. Had I trusted the plan at the end of chapter 10,
I would have rewritten `whnf` to be lazy — a long change, across every rule —
and the three lines here would still have been missing.

---

## 11.7 What is left

**221 declarations out of budget**, and the same 8 from one rejected
constructor.

The next question is the one this chapter asked, asked again: take one of the
221, cut its slice, sweep the budget, and see what the number says. The answer
will not be a guess.

Two candidates are already in view, and both are things Lean does and we do not.

- **Lazy δ by height.** Lean stores a height in `ReducibilityHints`, and when
  two sides have **different** constant heads it unfolds only the taller one.
  We unfold both. Our `Declaration` carries the hints already and the checker
  ignores them.
- **A lazy `whnf`.** Still true, still the deeper change, and no longer the
  first thing to try.
