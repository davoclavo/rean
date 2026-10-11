# Chapter 10 — The cache, and the rule that keeps it honest

Chapter 9 ended with one number and one frame. The number was **642
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

## 10.1 Why the same work happens twice

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

## 10.2 The third number in every node

A cache needs a key, and the key has to be cheap. Walking a term to make a key
costs the same walk the cache is meant to avoid.

So every node now caches a **hash**, computed in constant time from the hashes
of its children. It is the same pattern as `loose` and `size` of chapter 9, for
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

## 10.3 The rule: a hash finds, `alpha_eq` decides

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

## 10.4 When an answer stops being true

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

## 10.5 Do not cache what is cheap to recompute

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

## 10.6 What the cache bought

| | checked | failed | blocked | time |
|---|---|---|---|---|
| chapter 9 ended at | 33,862 | 650 | 23,000 | 163 s |
| with the cache | **34,419** | 683 | 22,410 | **172 s** |

590 declarations moved out of **blocked**, and 557 of them passed. The cost is
about 9 seconds, which is the hash in every node plus the lookups.

The failure count rose by 33, and §10.5 is why that is not a regression. Those
33 were blocked before. The checker had never asked them a question, so they
could not fail. Now it asks, and they run out of budget like their 642
relatives.

Every failure is still one of the two kinds chapter 9 named:

| kind | count |
|---|---|
| out of budget | 675 |
| unknown constant, from one rejected constructor | 8 |

So the checker still refuses no correct Lean on this input for want of a rule.

---

## 10.7 The honest summary of three chapters of speed

Four changes, each measured, each with a different lesson:

| change | what it moved | the lesson |
|---|---|---|
| cache `loose` and `size` in every node | 198 s → 160 s, **no** new declarations | a faster kernel is not a stronger one |
| a 512 MB stack | nothing, until the budget rose | read the exit code, not the clock |
| cheap test before `infer_type` | 185 s → 171 s | a new rule has a cost, and the profile names it |
| `Name::two_parts` | 171 s → 163 s | do not allocate inside the loop |
| cache `whnf` | **+557 declarations**, 163 s → 172 s | the first one that moved the real number |

Only the last one moved the number the project reports, and it is the only one
that made the **work smaller** rather than the same work faster.

---

## 10.8 What is left

**675 declarations out of budget.** Still well-founded recursion, and still the
whole gap.

The next cache is `is_def_eq`, keyed the same way and confirmed the same way.
After that the deeper change: our `whnf` is **eager**, and it rebuilds a whole
term for each step. Lean's is lazy, and that is why `drop_slow` sits at the top
of our profile and not of theirs.

Neither is a soundness gap. The checker has every rule it needs for this input.
What is left is the engineering, and the roadmap says so.
