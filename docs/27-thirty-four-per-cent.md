# Chapter 27 — Thirty-four per cent

> **Where you are.** Chapter 27 of 28, and the last of Part VI in
> [the guide](README.md). The lab notebook. Read it for the method.
>
> **Before this.** [Twelve seconds](26-twelve-seconds.md), for the oracle, and
> [Structures, and what the kernel costs](18-structures-and-cost.md) for the
> cached numbers.
>
> **After it you can** read a performance chapter in which half of the work was
> reverted, and see why that is the normal result.

Chapter 26 ended with an oracle: Lean's own kernel reads the prelude in twelve
seconds and ours took 199. This chapter is six attempts to close some of that,
measured one at a time, of which **three were kept and three were reverted**.

The whole prelude, in CPU time, with the same verdict every time:

| step | CPU time | cumulative |
|---|---|---|
| where chapter 26 left it | 213.96 s | — |
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

## 27.1 The allocator, which is one line

Nearly half of the profile was `malloc` and `free`. The kernel builds a term for
every reduction step and drops it on the next one, so the allocator is not a
detail of the work. For a while it **was** the work: chapter 24 found
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

Chapter 22 wrote the rule after a budget sweep did the same thing: three equal
rows should have been the clue. It took a second reading to see it here, in a
session that had already quoted that rule twice.

> **A measurement that cannot move is not measuring.**

---

## 27.2 A hash may refuse

Chapter 19 states the rule that keeps a cache in a proof checker honest: a hash
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

## 27.3 A name that carries its own hash

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
second. Chapter 21 set that rule when a pair of changes had to be measured
together, and this is the clearest case of it the project has had.

The old `hash_name` also hashed only the **last** part and the length, so
`Nat.succ` and `Int.succ` collided by design. They no longer do, and nothing
measured that; it is simply better.

One consequence, which `clippy` found rather than a measurement: a `Name` is 16
bytes larger, which pushed `TypeError::FieldTooLarge` to 132 bytes and over the
threshold for a value that sits in the return of the hot path. The payload is
boxed, which is what that enum's own comment already said to do.

[`Name`]: ../crates/rean_core/src/name.rs

---

## 27.4 One hasher for keys that are already hashes

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

## 27.5 Two that measured to nothing

Chapter 24 kept a list of eight. Here are two more, with the reason each one
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
the shared node, and chapter 26 measured that at two minutes against 1.06
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

## 27.6 One that was kept without a measurement

`Expr::PRETTY_LIMIT` stops every printer in the kernel at a megabyte.

It buys no time, and it is kept because of what chapter 26 found: the
`bv_decide` lemma of `Std` holds **2,617,556,290 nodes as a tree**, and asking
for its text asked the allocator for 13 GB and took two minutes. `rean show`
guards itself by reading the node count first. A **message** cannot:
`TypeError::render` builds one out of the terms that failed, so a type mismatch
on a term like that would spend gigabytes while reporting a failure.

`rean show --full` on that lemma now prints a megabyte in **0.55 seconds**, and
the message says a megabyte rather than promising all of it.

> **A failure must be cheaper to report than it was to find.**

---

## 27.7 What a run costs now

Every library the toolchain ships, with the final binary, in one sitting:

| library | declarations | checked | CPU | clock |
|---|---|---|---|---|
| `Init`, the prelude | 59,349 | 55,835 | 146 s | 155 s |
| `Std` | 99,619 | 95,237 | 245 s | 268 s |
| `Lean`, the compiler | 171,817 | 150,420 | 280 s | 299 s |

Chapter 26 measured the same three at 231, 330 and 367 seconds on the clock. The
counts are identical, which is the point: this chapter moved no verdict.

---

## 27.8 The profile after, and what is left

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
the work smaller, and chapter 26 section 26.8 named two candidates. One of them
is now **ruled out by measurement**, and that is the last section.

---

## 27.9 Eighty-two per cent are duplicates, and sharing them is slower

The second candidate was to share the nodes the kernel builds, so that a term
built twice is one object. It would turn `alpha_eq` into the pointer test that
section 27.2 only reaches sometimes, and it would cut the **number** of
allocations rather than their cost, which is exactly what section 27.8 says is
left.

The hypothesis is correct and the number is larger than anyone guessed. On the
declaration that blocks 2,283 others, of the nodes that reach `Sub::new`:

```text
71,312,529  node shared with one built before
15,582,296  node built for the first time
```

**Eighty-two per cent of the nodes this kernel builds, it has built already.**

It is still slower. Twice:

| `Sub::new` | CPU time |
|---|---|
| **as it was** | **17.5 s** |
| with a `HashMap` of every node, by hash | 30.7 s |
| with a 65,536 slot direct-mapped cache, 2 MB, no allocation per bucket | 27.9 s |

The second row was the obvious suspect: 87 million probes of a growing hash map,
with a `Vec` allocated for every one of the 15 million new buckets. So the table
became an array, indexed by one mask, small enough to sit in the processor's own
cache. It is **barely better**.

So the lookup was not the price. The price is everything else that a share
needs. The `Expr` has already been built on the stack by the time `Sub::new`
sees it, with a reference count bump for each of its children; then comes the
probe, the structural confirmation, the clone of the node that was found, and
the drop of the one just built, with a decrement for each child again.

> **Section 19.1 made an allocation cheap. It is now cheaper than remembering
> that you did not need one.**

That is a pleasing way for a chapter to eat its own tail, and it is a real rule
for anybody optimising in this order: a change that makes an operation cheap
**devalues every cache that exists to avoid it**. The hash-consing idea was
drawn up against the profile before `mimalloc`, and it would have been measured
against the wrong world.

The 82% is not refuted. It says, with a bigger number than before, that this
kernel's remaining cost is the **count** of nodes it builds. What is refuted is
collecting that saving **here**, after the node exists. It has to be collected
where the duplicate is built, in the way chapter 18 taught
`Expr::instantiate_at` to return "nothing changed" and keep the `Arc` it had.

The largest of those sites is the one chapter 23 named: every reduction step
rebuilds the whole application spine, and the arguments of that spine did not
change. Not materialising a spine at all is the explicit-stack evaluator, which
the roadmap has called a different project since chapter 23, and which now has a
measured reason rather than an argument from first principles.

---

## 27.10 And the other candidate, priced

The remaining idea was a cache that outlives a declaration. Today the driver
builds a fresh `TypeChecker` for every one of the 59,349, so every cache dies
with it, and the question is how much is being thrown away.

That is a measurement, not an argument, and it needed an instrument: a set of
every `whnf` question the **run** has asked, which can tell a question that is
new to the run from one that is new to this declaration.

```text
1,102,431  whnf asked
  824,336  whnf question new to the run
   34,795  answered by a cache
```

So a quarter of the questions are repeats, and the cache answers **3.2%** of
all of them. The other **22% are asked again and recomputed**, because the
answer was thrown away when the declaration changed. A cache that persisted
could answer seven times as many.

Two warnings on that number, both of which keep it an upper bound. The set is
keyed by the hash alone, and a repeat may mention a free variable or rest on a
declaration under check, which makes it **unsafe** to reuse. Pricing the safe
fraction needs the taint tracking that the real change would carry anyway.

It is the strongest of the cheap ideas that are left, and it is not cheap: the
driver has to stop building a checker per declaration, which is a borrow, and
the kernel has to know when an answer depended on the group under check, which
is a flag through `lookup`. Nobody should start it without the fourth number in
`Sub` that says whether a term holds a free variable.

### The instrument reads the right population now

The first version of this measurement said **99.88%** of questions were new to
the run, and that the cache answered 296 of 690,288. Both numbers were true and
neither answered the question, because the tally prints for the declaration that
**failed**, and I read one declaration's numbers as the run's.

The same mistake, caught by switching the cache off: 18.1 s became 25.6 s, so
the cache that "answered 296 questions" is worth **42%**. Its hits are the
expensive ones, which is why a count of questions cannot be turned into a
share of the time.

So the tally now has two sets of counters, and the driver prints the run-wide
one at the end of a check.

> **A per-declaration instrument answers "why is this one expensive". It does
> not answer "where does the run spend itself", and reading one as the other is
> a mistake this project has now made twice.**

---

So the candidate list ends this chapter one shorter than it started:

- **ruled out**, here: sharing a node after it is built;
- **ruled out**, chapter 24 section 24.7: a term as a pointer plus a shift;
- **priced**, section 27.10: a cache that persists across declarations could
  answer 22% of all `whnf` questions where the present one answers 3.2%. The
  work is a borrow in the driver and a taint flag in the kernel;
- **untested and now the strongest**: an evaluator that does not build the
  spine.

The oracle is still twelve seconds.

---

## 27.11 How other systems do it

Each of the three changes that were kept has a counterpart in Lean itself,
which is a useful check on whether a change is sound engineering or a trick.

| Our change | Lean's version |
|---|---|
| a faster allocator, section 27.1 | Lean links mimalloc as well, in `src/runtime/mimalloc.cpp` |
| a name that carries its own hash, section 27.3 | `src/util/name.h` caches a hash on a name, and its comparison uses the hash first |
| one hasher for a key that is already a hash, section 27.4 | Lean's cached hash is 32 bits wide, and the comment in `src/Lean/Expr.lean` gives the layout |

And the change that was **not** taken has a counterpart too. Section 19.9
measures that 82% of the nodes this kernel builds are duplicates, and that
sharing them is still slower. The technique with a name is hash-consing, and
the 2006 paper by Filliâtre and Conchon is the standard description. Lean gets
the same effect for free in one direction: the elaborator hands the kernel
terms that already share their subterms, so a pointer comparison usually
succeeds. We build every node from a text file, so there is nothing to share
until we pay for it.

One note on method, because it is the reason this chapter is readable. Every
row of the table at the top is CPU time, best of three to five runs, with the
same verdict on all 59,349 declarations. A performance change that moves a
verdict is not a performance change.

## 27.12 References

**Our code**

- `crates/rean_core/src/name.rs`, the name that carries its own hash
- `crates/rean_kernel/src/expr.rs`, the hash that may refuse
- `crates/rean_kernel/src/typeck.rs`, the caches that use it
- `crates/rean_kernel/tests/cache.rs`

**Lean's own source**

- `src/runtime/mimalloc.cpp`, the same allocator
- `src/util/name.h`, a cached hash on a name, and a comparison that reads it
  first
- `src/Lean/Expr.lean`, the bit layout of the cached word

**Read more**

- Filliâtre and Conchon, *Type-safe modular hash-consing*, 2006, for the change
  section 27.9 priced and did not take.
  <https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf>
- Ullrich and de Moura, *Counting Immutable Beans*, 2019, for how Lean manages
  memory in the stage after this one. <https://arxiv.org/abs/1908.05647>

---

**Next:** [A program that runs](28-a-program-that-runs.md)
