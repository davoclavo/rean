# Chapter 18 — The cache, and the rule that keeps it honest

> **Where you are.** Chapter 18 of 28, in Part VI of [the guide](README.md). The
> lab notebook. Read it for the method.
>
> **Before this.** [Structures, and what the kernel costs](17-structures-and-cost.md),
> for the cached numbers and the work budget.
>
> **After it you can** state the one rule that keeps a cache in a proof checker
> honest.

Chapter 17 ended with one number and one frame. The number was **642
declarations out of budget**, all of them well-founded recursion. The frame was

```text
drop_slow   9,677 samples
```

which is the time spent **destroying terms**. A checker that spends its largest
share there is building terms and throwing them away. So it is reducing the same
subterm again, and again, and again.

This chapter adds the cache that stops it, and the one discipline a cache in a
proof checker must keep.

```sh
devbox run -- cargo test -p rean_kernel --test cache
```

---

## 18.1 Why the same work happens twice

`whnf` takes a term and reduces it until the head cannot move. The checker calls
it everywhere: `is_def_eq` calls it on both sides, `infer_type` calls it on
every type it reads, and each reduction rule calls it on an argument before it
looks at the shape.

Those calls overlap. One unfolding of `WellFounded.fix` produces a term that
holds the same subterm in several places, and `is_def_eq` then walks into each
place and reduces that subterm from the start.

Nothing about the subterm changed between the two calls. The answer is a
function of the term, the environment, and the local context, and none of the
three moved.

So remember the answer.

---

## 18.2 The third number in every node

A cache needs a key, and the key has to be cheap. Walking a term to make a key
costs the same walk the cache is meant to avoid.

So every node now caches a **hash**, computed in constant time from the hashes
of its children. It is the same pattern as `loose` and `size` of chapter 17, for
the third time:

```rust
pub struct Sub {
    expr: Arc<Expr>,
    loose: u32,
    size: u32,
    hash: u64,
}
```

```rust
Expr::App { fun, arg } => mix(mix(6, fun.hash), arg.hash),
```

`mix` is one exclusive or and one multiply. The kernel needs a hash that is
cheap, not one that resists an attack.

### What the hash must leave out

A hash has one contract: **two terms that are equal must hash equally.** Break
it and every lookup of those terms misses, so the cache does nothing.

Our equality is `alpha_eq`, and it is looser than the shape of the term in two
places. So the hash leaves both out:

| `alpha_eq` ignores | so the hash ignores |
|---|---|
| the **name** of a binder, because a de Bruijn index does the work | `binder_name` |
| the **shape** of a universe level, because it compares by `Level::is_equiv` | every level |

That second row is the surprising one. `Sort u` and `Sort (max u u)` are the
same type, so they must land in the same bucket, and the only cheap way to
promise that is to hash no level at all.

Tests: `a_binder_name_does_not_change_the_hash`,
`an_equivalent_level_does_not_change_the_hash`, and
`a_different_term_usually_hashes_differently`, which checks that the filter
still filters.

---

## 18.3 The rule: a hash finds, `alpha_eq` decides

Two different terms **can** share a 64-bit hash. It is unlikely. It is not
impossible.

A compiler may take that bet. A proof checker may not. If a collision returned
the normal form of some other term, the checker would accept a proof of
anything, and it would do so quietly and rarely, which is the worst way for a
checker to be wrong.

So the cache stores the **question** next to the answer, and a lookup confirms:

```rust
if let Some(bucket) = self.whnf_cache.get(&key)
    && let Some((_, answer)) = bucket.iter().find(|(question, _)| question.alpha_eq(e))
{
    return Ok(answer.clone());
}
```

One bucket holds a list, because one hash can name more than one question. The
hash narrows the search to a short list; `alpha_eq` makes the decision.

**A hash finds an answer. Equality decides whether to trust it.**

Test: `the_answer_is_the_same_whether_it_is_cached_or_not`.

---

## 18.4 When an answer stops being true

A cached answer is true as long as the question means the same thing. Two things
can change that, and both clear the cache.

1. **A new declaration.** A term that mentions a free variable only means
   something in the context that holds it, and each declaration brings its own
   context. `check_declaration` starts with an empty cache.
2. **A new mutual group.** δ unfolds the declarations under check as well as the
   ones in the environment, so an answer found while one group was pending may
   rest on a declaration that is no longer there. `with_group` clears the cache
   on the way in and on the way out.

Within one declaration the local context only **grows**, and that is safe. A new
free variable cannot change the type of an old one, and a term that mentions the
new variable was never in the cache.

Test: `a_cached_answer_does_not_outlive_its_declaration`.

A cap guards memory. Past 200,000 buckets the cache starts again, because
answers that no later declaration asks for are only memory.

---

## 18.5 Do not cache what is cheap to recompute

The first version cached every call, and it was slower than it had to be.

A lookup costs a hash of the top node, a hash table probe, and an `alpha_eq`
against each question in the bucket. For a **small** term that is as much work
as the reduction it saves. Worse, most calls to `whnf` are on a term that is
already in normal form, so the honest answer is "nothing happened" and an entry
for it is pure cost.

Two tests now stand in front of the cache:

```rust
let worth_it = e.size_up_to(CACHE_MIN_SIZE) >= CACHE_MIN_SIZE;
...
if worth_it && steps > 0 {
    self.remember_whnf(key, e, &answer);
}
```

`steps` is the number of rules that fired, which `whnf` already knows and used
to throw away.

And the threshold comes from a sweep, not from taste:

| `CACHE_MIN_SIZE` | checked | failed | time |
|---|---|---|---|
| no threshold | 34,419 | 683 | 187 s |
| **4** | **34,419** | **683** | **173 s** |
| 12 | 34,412 | 688 | 193 s |
| 32 | 34,057 | 623 | 177 s |

Four is the pick. It keeps every declaration that the cache won and gives back
most of the time the cache cost.

Read the last row before you trust any single run of this table. A threshold of
32 reports **60 fewer failures** than a threshold of 4, and that is not better:
it checked 362 fewer declarations, because the ones it did not check were
blocked rather than attempted. **A failure count alone can be improved by
attempting less.** Read it with the checked count or do not read it.

---

## 18.6 The same cache on `is_def_eq`

`whnf` is not the only place the checker answers the same question twice.
`is_def_eq` is called on the same pair of terms again and again while one
well-founded definition unfolds, and it starts from nothing every time.

The cache is the same shape, with the key built from both sides:

```rust
let key = mix_hashes(a.hash_value(), b.hash_value());
```

and a hit confirmed against **both** questions:

```rust
.find(|(left, right, _)| left.alpha_eq(a) && right.alpha_eq(b))
```

Two differences from the `whnf` cache are worth naming.

1. **A negative answer is kept.** `Ok(false)` means "these two are not equal",
   and that is a decision worth remembering. A comparison that ran out of
   budget returns `Err` instead, and no error is ever kept: it says nothing
   about the terms, only about the budget that was left. If the kernel kept it,
   one declaration with a small budget would poison every later comparison.
2. **There is no size threshold.** `is_def_eq` already has a cheap test in
   front of the cache, which is `alpha_eq` on the two terms as they arrived.
   Past that test the work is unbounded, so every answer is worth keeping
   whatever the size.

Tests: `a_negative_answer_is_remembered_too`,
`a_comparison_that_ran_out_of_budget_is_not_remembered`.

---

## 18.7 What the caches bought

| | checked | failed | blocked | time |
|---|---|---|---|---|
| chapter 17 ended at | 33,862 | 650 | 23,000 | 163 s |
| a cache on `whnf` | 34,419 | 683 | 22,410 | 172 s |
| a cache on `is_def_eq` too | **35,115** | 684 | 21,713 | **190 s** |

1,287 declarations moved out of **blocked**, and 1,253 of them passed. The cost
is 27 seconds, which is the hash in every node plus the lookups.

The failure count rose by 34, and §18.5 is why that is not a regression. Those
34 were blocked before. The checker had never asked them a question, so they
could not fail. Now it asks, and they run out of budget like their 642
relatives.

Every failure is still one of the two kinds chapter 17 named:

| kind | count |
|---|---|
| out of budget | 676 |
| unknown constant, from one rejected constructor | 8 |

So the checker still refuses no correct Lean on this input for want of a rule.

---

## 18.8 A faster kernel exposed a limit that lied

A larger budget after the caches brought a failure the prelude had never shown:

```text
108  reduction did not stop after 100000 steps
```

That is not the budget. It was a **second** limit, inside one call of `whnf`,
with a constant of its own. Its own doc comment said what it was:

> The budget in `FUEL` bounds a whole declaration, and every step here spends a
> unit of it, so this limit is a second line of defence rather than the main one.

Read that again and the limit answers itself. `whnf_step` spends a unit of the
budget **before** it tries any rule, so the loop cannot run more times than the
budget holds. The budget already bounds the loop. The second limit could only
ever fire **earlier** than the real one.

So the loop now has one bound, which is the budget:

```rust
// The budget is the only bound this loop needs, and it is a real one.
// `whnf_step` spends a unit before it tries any rule, so the loop
// cannot run more times than the budget holds.
loop {
    match self.whnf_step(&current)? {
```

### And now the measurement, which says I was half wrong

| | checked | failed | time |
|---|---|---|---|
| two bounds | 36,209 | 509 | 329 s |
| one bound | **36,209** | **509** | 362 s |

**Not one declaration changed its verdict.** Those 108 did not get released. They
reduce for a while longer and then run out of budget, which was always going to
happen. 393 out of budget plus 108 at the step limit became 501 out of budget,
and 501 is the same 501.

And the removal costs about 33 seconds, because the checker now keeps reducing
a hopeless declaration until the real limit stops it. The old limit was an
accidental early exit.

So why keep the change? For the **message**, and for one constant fewer.

```text
before:  reduction did not stop after 100000 steps
after:   this declaration needed more than 100000000 units of work
```

The first sentence tells the reader to look for a loop or a corrupt file. There
was neither. The declaration was correct and simply expensive, and the reader
who trusted that message would hunt a bug that does not exist.

**A second safety limit that is not derived from the first will one day fire
before it, and then it reports the wrong cause.** The cost of removing it is 10%
of the time at a budget nobody uses by default. The gain is that every failure
on this input now names its real reason.

### The same measurement found a second false message

The report said

```text
this declaration needed more than 20000000 units of work
```

on a run whose budget was **100,000,000**. The message read the default
constant, and `REAN_FUEL` had overridden it. The error now carries the budget
that the run actually set:

```rust
Err(TypeError::OutOfFuel(self.budget))
```

A report that names the wrong number is worse than one that names none, because
a reader will trust it and tune the wrong knob.

Test: `a_definition_that_unfolds_to_itself_hits_the_limit`, which now sets a
budget of 1,000 and asks for that number back.

---

## 18.9 The honest summary of three chapters of speed

Four changes, each measured, each with a different lesson:

| change | what it moved | the lesson |
|---|---|---|
| cache `loose` and `size` in every node | 198 s → 160 s, **no** new declarations | a faster kernel is not a stronger one |
| a 512 MB stack | nothing, until the budget rose | read the exit code, not the clock |
| cheap test before `infer_type` | 185 s → 171 s | a new rule has a cost, and the profile names it |
| `Name::two_parts` | 171 s → 163 s | do not allocate inside the loop |
| cache `whnf` | **+557 declarations**, 163 s → 172 s | the first one that moved the real number |
| cache `is_def_eq` | **+696 declarations**, 172 s → 190 s | the same idea pays twice |
| one bound instead of two | nothing, and 33 s slower | a redundant limit reports the wrong cause |

Only the two caches moved the number the project reports, and they are the only
two that made the **work smaller** rather than the same work faster. Three of
the six changes moved no declaration at all, and each one was still worth
making for a different reason. Say which reason.

---

## 18.10 What is left

**676 declarations out of budget.** Still well-founded recursion, and still the
whole gap.

A larger budget shows how much of that gap is the budget and how much is the
checker:

| budget | checked | failed | time |
|---|---|---|---|
| 20,000,000 | 35,115 | 684 | 190 s |
| 100,000,000 | **36,209** | **509** | 362 s |

Five times the budget buys 1,094 declarations and cuts the failures by 175. So
the budget is still a real part of the gap, and 509 declarations are beyond even
that.

Do not compare this table with the one in chapter 17 §17.12. That measurement ran
on an earlier binary, and a comparison across two binaries measures both
changes at once.

Both caches are in, so what remains looked like the deeper change: our `whnf`
is **eager**, and it rebuilds a whole term for each step. Lean's is lazy, and
that is why `drop_slow` sat at the top of our profile and not of theirs.

That plan was wrong, and [chapter 19](19-compare-before-you-unfold.md) is the
one measurement that said so. The fix was three lines, and it took 455 of these
676 failures away. Read chapter 19 before trusting any plan in this one.

Neither is a soundness gap. The checker has every rule it needs for this input.
What is left is the engineering, and the roadmap says so.

---

## 18.11 How other systems do it

Lean's kernel caches the same two questions, and it keeps the same discipline.

| Ours | Lean's, in `src/kernel/type_checker.cpp` |
|---|---|
| a cache on `whnf` | a `whnf` cache in the checker state |
| a cache on `is_def_eq` | **two** caches. `cache_success` records a pair that matched, and `cache_failure` records a pair that did not. |
| confirm a hit with `alpha_eq` | compare the pointer with `is_eqp` first, and the key is the term itself, not a hash alone |

Three notes.

- **A negative cache is the half we do not have.** Lean remembers a pair that
  was **not** equal, because asking twice costs as much as asking once.
  Section 10.6 is the positive half only.
- **Pointer equality comes before everything.** Lean's first test in a
  comparison is whether the two terms are the same object. That test is free,
  and it works because Lean's elaborator shares subterms. Chapter 26, section
  18.9 asks what sharing would be worth to us, and the answer surprised us.
- **The honest rule is not special to proofs.** A hash table does the same
  thing: hash to find a bucket, then compare the key. Section 10.3 only says
  that a proof checker may not skip the second half to go faster, because
  "probably equal" is not a verdict a kernel is allowed to give.

## 18.12 References

**Our code**

- `crates/rean_kernel/src/typeck.rs`, both caches and the confirmation step
- `crates/rean_kernel/src/expr.rs`, the cached hash code
- `crates/rean_kernel/tests/cache.rs`, every claim of this chapter

**Lean's own source**

- `src/kernel/type_checker.cpp`. The four cache methods are `cache_success`,
  `cache_failure`, `succeeded_before` and `failed_before`, and
  `quick_is_def_eq` reads the positive cache before it does anything else.
- `src/kernel/expr_eq_fn.cpp`, alpha equivalence with its own cache

**Read more**

- Filliâtre and Conchon, *Type-safe modular hash-consing*, 2006, for making
  two equal terms one object, which is the other answer to this chapter's
  problem. <https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf>
- Grégoire and Leroy, *A compiled implementation of strong reduction*, 2002,
  for the design that avoids the repeated work instead of caching it.
  <https://xavierleroy.org/publi/strong-reduction.pdf>

---

**Next:** [Compare before you unfold](19-compare-before-you-unfold.md)
