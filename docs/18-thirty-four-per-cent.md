# Chapter 18 — Thirty-four per cent

Chapter 17 ended with an oracle: Lean's own kernel reads the prelude in twelve
seconds and ours took 199. This chapter is six attempts to close some of that,
measured one at a time, of which **three were kept and three were reverted**.

The whole prelude, in CPU time, with the same verdict every time:

| step | CPU time | cumulative |
|---|---|---|
| where chapter 17 left it | 213.96 s | — |
| a faster allocator | 186.91 s | −13% |
| a hash that may refuse, and a name that carries one | 142.58 s | **−33%** |
| one hasher for keys that are already hashes | 141.42 s | −34% |

**55,835 of 59,349 declarations, at every step.** Not one was gained and not one
was lost, which is the first thing to check about a performance change: a
cheaper node is the same work done faster.

Why CPU time and not the clock? The machine was loaded, and the wall clock said
anything between 21 and 50 seconds for the same slice. A measurement that moves
by a factor of two when nothing changes is not a measurement. CPU time of the
process is stable to about one per cent here, and every number in this chapter
is the best of three to five runs.

---

## 18.1 The allocator, which is one line

Nearly half of the profile was `malloc` and `free`. The kernel builds a term for
every reduction step and drops it on the next one, so the allocator is not a
detail of the work. For a while it **was** the work: chapter 15 found
`Arc<Expr>::drop_slow` at the top of the list with 121,445 samples.

```rust
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;
```

| allocator | CPU time, the slice |
|---|---|
| the system allocator | 24.57, 24.37, 24.42 s |
| **`mimalloc`** | **19.84, 19.96, 19.92 s** |

Nineteen per cent on the slice and thirteen on the prelude, for one line and one
dependency. It is in the **driver** and not in `rean_kernel`: a global allocator
is a property of the program, the kernel is the part you have to trust, and
anybody who uses `rean_kernel` as a library picks their own.

### The method went wrong first

The first A/B printed **six identical rows**. `zsh` refused to overwrite the file
the timings were going to, so every row reported the first run.

Chapter 13 wrote the rule after a budget sweep did the same thing: three equal
rows should have been the clue. It took a second reading to see it here, in a
session that had already quoted that rule twice.

> **A measurement that cannot move is not measuring.**

---

## 18.2 A hash may refuse

Chapter 10 states the rule that keeps a cache in a proof checker honest: a hash
**finds** an answer and `alpha_eq` **decides**, because two terms can share a
hash. The other half of that rule is free, and `alpha_eq` never used it.

Two terms with **different** hashes cannot be alpha-equal.

So `Sub::alpha_eq` tests three things, cheapest first: the pointer, because a
term is a graph and the same subterm arrives again and again; then the stored
hash; and only then the shape. It is an inherent method, so it shadows the
`Deref` to `Expr::alpha_eq` and **every recursive call inside that function
gained both fast paths without being edited**.

That refusal is sound only because `hash_range` leaves a thing out exactly where
`alpha_eq` leaves it out: a binder name, and a universe level. Nothing held the
two together, so three tests in `tests/sweep.rs` now do:
`a_binder_name_is_ignored_by_both`,
`a_universe_written_two_ways_is_ignored_by_both`, and
`the_pairs_really_are_written_differently`.

Its pairs are written by hand, and that detail is the whole value of the test. A
loop over the `one_of_each` corpus would have been **vacuous**: every pair in
that list is unequal, so "alpha-equal implies the same hash" would hold for the
self-pairs and for nothing else. The pairs here are alpha-equal and written
differently, one for each thing the hash ignores: a lambda, a `Forall` and a
`Let` that differ only in the binder name, a `Sort` whose level is `max 0 u`
against `u`, and a constant whose level argument is written both ways.

> **A test that passes for the wrong reason is worse than no test**, because it
> is paid for once and trusted for ever.

### It was worth nothing on its own

| | CPU time, the slice |
|---|---|
| the allocator alone | 19.65, 19.82, 20.00 s |
| and the fast paths | 19.77, 20.29, 19.75 s |

Nothing. Three runs each and the two lists interleave.

The reason is in the function it was built on. `hash_range` of a **constant**
called `hash_name`, which walked the name's last part, so the fast path was
paying for the hash it was using. A `Const` is the most common node in a real
term, and most comparisons in this kernel are of small terms where the walk it
saved was shorter than the hash it needed.

---

## 18.3 A name that carries its own hash

So give a [`Name`] its hash and its part count, computed once where the part is
added.

Three paths were walking that chain, and all three run per reduction step:

- `Environment::lookup` hashed every byte of every part, with SipHash, to find
  a declaration;
- `nat_lit::is_binop` asked `two_parts`, which asked `len`, which walked;
- `hash_name` walked the last part for **every constant node the kernel built**.

`Eq` compares the hash first, then the shared pointers, which fire often because
the export reader builds every name of a module out of one prefix. `Hash` writes
the one number.

| | CPU time, the slice |
|---|---|
| the allocator alone | 19.86, 19.93, 19.74 s |
| **and the fast paths and the name** | **17.96, 17.97, 17.52 s** |

Ten per cent on the slice, and **twenty-four on the prelude**, which is the
larger number because the prelude asks 59,349 names of a map with 59,349 entries
in it where the slice asks 4,144 of 4,144.

Two changes, one measurement, because the first is worth nothing without the
second. Chapter 12 set that rule when a pair of changes had to be measured
together, and this is the clearest case of it the project has had.

The old `hash_name` also hashed only the **last** part and the length, so
`Nat.succ` and `Int.succ` collided by design. They no longer do, and nothing
measured that; it is simply better.

One consequence, which `clippy` found rather than a measurement: a `Name` is 16
bytes larger, which pushed `TypeError::FieldTooLarge` to 132 bytes and over the
threshold for a value that sits in the return of the hot path. The payload is
boxed, which is what that enum's own comment already said to do.

[`Name`]: https://docs.rs/rean_core

---

## 18.4 One hasher for keys that are already hashes

Every map in the kernel is keyed by a `u64` that the kernel computed, or by a
name that now carries one. The standard hasher is SipHash, which is built to
resist somebody who chooses the keys in order to collide them. **Nobody chooses
these keys.**

`KeyHasher` writes the number through with one FNV mix, which is the mix
`expr.rs` already had, so the kernel keeps its one dependency.

| input | before | after |
|---|---|---|
| the slice, five runs, best | 17.65 s | **16.91 s** |
| the whole prelude | 142.58 s | **141.42 s** |

Four per cent on the slice and under one on the prelude. It is the smallest
keeper in this chapter and it is still a keeper: the direction held in four of
five pairs, and the code is shorter than the comment that explains it.

Its `write` falls back to FNV over the bytes rather than answering zero. Nothing
in the kernel takes that path, and a hasher that quietly returned the same
number for a shape it did not expect would turn every map into a list.

---

## 18.5 Two that measured to nothing

Chapter 15 kept a list of eight. Here are two more, with the reason each one
failed, because the reason is the part a reader can use.

### `Arc<[Level]>` for the levels of a constant

The premise: a constant is the most common node in a real term, and **every
clone of one allocates a `Vec`**.

The second half is false. Most constants carry **no** level at all, and an empty
`Vec` in Rust allocates **nothing**, while an `Arc<[Level]>` always allocates its
header. The change made the common case worse in order to improve the rare one:
16.97 s against 16.77 s on the slice.

> **Know which case is common before you make it faster.**

### A graph walk for `collect_level_params`

This one is the more interesting failure, because the identical change to its
sibling was worth **120 times**.

`collect_constants` walks the graph, with a visited set keyed by the address of
the shared node, and chapter 17 measured that at two minutes against 1.06
seconds on one declaration of `Std`. `collect_level_params` has the same shape
and the same hazard, so it got the same treatment:

| input | tree walk | graph walk |
|---|---|---|
| the slice that blocks 2,283 | 16.97 s | 16.61 s |
| the bitblasting slice | 11.61 s | 11.30 s |
| the whole `Lean` library | **231.64 s** | 233.90 s |

Nothing, and a little worse on the biggest input, where the visited set is
343,634 allocations that find nothing to skip.

The reason is **which declarations reach it**. `check_universes` runs on a
declaration that the kernel is about to check, and the colossal ones are
`blocked` by a dependency that failed, so they never arrive. Its sibling is
called by the **driver**, for every declaration in the file, before anything is
blocked.

> **The same fault in two functions can be worth a hundredfold in one and
> nothing in the other. Which callers reach it decides.**

`mentions_fvar` was left alone for that reason before it was touched: it runs
once per recursor check over index terms, so a visited set there costs more than
it can save.

---

## 18.6 One that was kept without a measurement

`Expr::PRETTY_LIMIT` stops every printer in the kernel at a megabyte.

It buys no time, and it is kept because of what chapter 17 found: the
`bv_decide` lemma of `Std` holds **2,617,556,290 nodes as a tree**, and asking
for its text asked the allocator for 13 GB and took two minutes. `rean show`
guards itself by reading the node count first. A **message** cannot:
`TypeError::render` builds one out of the terms that failed, so a type mismatch
on a term like that would spend gigabytes while reporting a failure.

`rean show --full` on that lemma now prints a megabyte in **0.55 seconds**, and
the message says a megabyte rather than promising all of it.

> **A failure must be cheaper to report than it was to find.**

---

## 18.7 What a run costs now

Every library the toolchain ships, with the final binary, in one sitting:

| library | declarations | checked | CPU | clock |
|---|---|---|---|---|
| `Init`, the prelude | 59,349 | 55,835 | 146 s | 155 s |
| `Std` | 99,619 | 95,237 | 245 s | 268 s |
| `Lean`, the compiler | 171,817 | 150,420 | 280 s | 299 s |

Chapter 17 measured the same three at 231, 330 and 367 seconds on the clock. The
counts are identical, which is the point: this chapter moved no verdict.

---

## 18.8 The profile after, and what is left

Same declaration, same command, same fifteen seconds of sampling.

| frame | before, of 8,963 | after, of 5,850 |
|---|---|---|
| the allocator and the drop of a term | about 4,000, **45%** | 2,374, **41%** |
| hashing a node, a name, or a cache key | 945, 10% | 164, **2.8%** |
| `Sub::new`, which builds a node | 926, 10% | 609, 10% |

Hashing is dealt with. **The allocator is not**, and that is the finding that
sets up whatever comes next: `mimalloc` made each allocation cheaper and the
**number** of them is unchanged. Two fifths of this kernel is still building
nodes and dropping them.

Everything in this chapter made the same work cheaper. The next tier has to make
the work smaller, and chapter 17 section 17.8 names the two candidates: a cache
that persists across declarations, because all 59,349 of them currently re-reduce
the same prelude subterms from scratch, and hash-consing the nodes the kernel
builds, which would turn `alpha_eq` into the pointer test that section 18.2 only
reaches sometimes, and would cut nodes built rather than their cost.

The oracle is still twelve seconds.
