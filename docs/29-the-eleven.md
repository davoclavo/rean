# Chapter 29 — The eleven that were not wrong

> **Where you are.** The last chapter, and it follows
> [the arena](28-the-arena.md) directly.
>
> **Before this.** [The arena](28-the-arena.md), for the suite and the six
> soundness rules, and [Thirty-four per cent](26-thirty-four-per-cent.md),
> whose method this chapter uses and one of whose conclusions it overturns.
>
> **After it you can** say why a tree walk over a graph is the most expensive
> bug in this repository, and why the same measurement can be right about one
> input and wrong about every other.

Chapter 28 closed every soundness hole the arena found and left eleven tests
that we got wrong. All eleven were in the `perf/` set, all eleven were
**valid** proofs, and we reported all eleven as invalid.

Now: **124 of 126 accepted, 72 of 72 rejected, nothing wrongly accepted,
nothing wrongly rejected, two declined.**

---

## 29.1 The interface is the exit code, and we had two of the three

The arena runs a checker as `run: ./target/release/rean check "$IN"` and reads
the exit code. The contract is four lines:

| code | the arena calls it | what it means |
|---|---|---|
| 0 | accepted | the proof checks |
| 1 | rejected | the proof is not valid |
| 2 | **declined** | the checker cannot answer |
| anything else | an error in the checker | a bug in us |

A declined test is **ignored** for both soundness and completeness. The arena
explains why in its own README: a decline says "you are not claiming that the
proof is not valid".

This kernel has had that distinction since chapter 25. `OutOfFuel` and
`OutOfStack` mean "we did not check it", `TypeError::is_a_limit` names them,
and `tools/arena.py` was written to count them apart. And then the driver
exited **1** for both, which told the arena that eleven valid proofs were
invalid.

So the three answers are three exit codes now, `Verdict::Declined` carries the
limit through the report, and the bit comes from the kernel rather than from a
regular expression over the message. `a_limit_is_a_decline_and_not_a_failure`
is the test.

> A distinction that only exists in a comment is not a distinction. This one
> was in the type system of the kernel and in the harness, and the one place it
> was missing was the only place the outside world could see.

---

## 29.2 One bug, three times: a walk of a graph

A term is a **graph**. `Expr` shares its subterms through `Arc`, so a walk of
one as a tree is a walk of the tree it stands for, and the two differ by an
exponent. Chapter 17 found that in `collect_constants` and fixed it. The arena
found three more, and each one was the whole running time of a test.

| where | the test | what it was | what it is |
|---|---|---|---|
| `Expr::collect_level_params` | `perf/app-lam` | a tree walk | a graph walk, with a visited set |
| `Expr::has_loose_bvars_from` | `perf/shared-subterm` | a tree walk | two field reads |
| `Sub::instantiate_at` | `perf/app-lam` | rebuilds each path | rebuilds each **node**, once |

### The one that was already fixed and then reverted

`collect_level_params` is the painful one. Chapter 26 gave it the visited set,
measured it on three real inputs, found nothing, and **took it out again**,
leaving the table in a comment:

| input | tree walk | graph walk |
|---|---|---|
| the slice that blocks 2,283 | 16.97 s | 16.61 s |
| the bitblasting slice | 11.61 s | 11.30 s |
| the whole `Lean` library | 231.64 s | 233.90 s |

Every number in that table is still true. `good/perf/app-lam` builds a term of
4,000 levels where each level applies a constant to the **same** lambda twice.
As a graph it is linear. As a tree it is 2⁴⁰⁰⁰. `check_universes` is the first
rule a declaration meets, so this function ran before any other and never
returned: 4,743 samples of a profile, 4,743 of them here.

> A measurement answers the question it was given. "Is this faster on the
> prelude" is not the question "does this terminate on every input", and no
> amount of care with the first one tells you anything about the second.

### The one that did not need a walk at all

`Sub` stores the loose range of every term it wraps, for the O(1) skip in
substitution. `Expr::has_loose_bvars_from(depth)` asks "is there a loose
variable at `depth` or past it", which is `loose_range(self) > depth`: two
field reads. It walked instead, 511 frames deep, for all of
`perf/shared-subterm`.

The node already knew.

### The one that is a win on ordinary code too

A substitution that visits a shared node once per path rebuilds the tree.
`SubMemo` remembers what a rewrite has already produced, keyed by the address
of the node **and** the depth, and only for a node with more than one owner,
because a node with one owner occurs once.

It was added for `app-lam` and it pays for itself on the prelude: **62 more
declarations and 7% less time**. Lean's own kernel gets the same property for
free, because its terms are maximally shared and a rewrite of one node is a
rewrite of all of its uses.

---

## 29.3 A hash may refuse an answer. Only an address may confirm one

Chapter 18 states the rule that every cache here obeys: a hash may **refuse**
an answer and may not **confirm** one, because two terms can share a hash. So
each of the five caches found its bucket by hash and then confirmed the entry
with `Expr::alpha_eq`.

`alpha_eq` walks. On a graph it walks the tree.

`perf/app-lam` made **510,755** confirmations and **800 million** node
comparisons inside them in eighty seconds, which was the whole of its running
time. The memo that fixes a single walk does not help, because the cost is not
one walk: it is half a million of them, each on a term that is equal and
distinct.

`Expr::same_node` is the other half of chapter 18's rule. It compares the
**children by address**: two nodes whose children are the same objects are the
same term, with no walk, because an address is an exact name. It can only say
yes, and `cheap_eq` puts the two tests in the order of their cost:

```rust
fn cheap_eq(a: &Expr, b: &Expr) -> bool {
    a.same_node(b) || (a.size_up_to(CONFIRM_LIMIT + 1) <= CONFIRM_LIMIT && a.alpha_eq(b))
}
```

A term too large for both tests is a **miss**, and a miss is sound: the answer
is computed again. That is the one direction a cache may be wrong in.

The bound is measured, and the first value was wrong:

| `CONFIRM_LIMIT` | the prelude | its time |
|---|---|---|
| 64, on one cache | 55,831 | 153.6 s |
| 1,024, on one cache | 55,831 | 153.1 s |
| **65,536, on every cache** | **55,835** | **144.4 s** |

A small bound loses the hits that a real library earns most from, and those
four declarations are the measurement saying so: a cache miss costs work, work
costs budget, and a declaration near its budget declines.

---

## 29.4 Two things built, measured, and taken out

Chapter 26 recorded eight of these. Here are two more, and the method is the
point.

**A memo for `alpha_eq`**, keyed by pairs of addresses, so that an equal pair
is settled once. It is sound and it looked obviously right. It got **zero
hits** on `app-lam`: the nodes being compared were built by a substitution and
had one owner each, so they could not recur inside one walk, and the memo is
thrown away between walks. Removed.

**A cache for `infer_type` keyed by the identity of the node**, holding the
`Sub` so that the address stayed its own. It works, and by the time it was
measured `cheap_eq` had already made `app-lam` fast, so it bought nothing and
cost **3.7%** of the prelude. Removed.

The whole sweep, because a measurement is the settings and the number:

| configuration | the prelude | its time | `app-lam` |
|---|---|---|---|
| chapter 28 | 55,835 | 141 s | never finishes |
| the three walk fixes, bound 64 on the infer cache, both extra caches | 55,831 | 153.6 s | 3 s |
| without the identity cache | 55,831 | 147.7 s | 3 s |
| without the pair memo as well | 55,831 | 143.8 s | 4 s |
| and without the substitution memo | 55,769 | 154.8 s | never finishes |
| **what shipped**: three walk fixes, `cheap_eq` at 65,536 everywhere | **55,835** | **144.4 s** | **3.5 s** |

Two and a half per cent of time, no declaration lost, and a test that went
from "never" to three seconds.

---

## 29.5 A budget for a question is not a budget for a batch

Seven of the eleven needed no new rule at all. They needed a **budget**, and
they answer in one to fourteen seconds when they get one.

A budget exists so that one declaration cannot stall the rest of a file. A
file with one declaration in it **has** no rest. Those are two different
questions and they had one answer, which served neither: 40,000,000 nodes is
right for 59,349 declarations and absurd for one.

So `budget_for` reads the size of the file first:

| the file | the budget | why |
|---|---|---|
| up to 10,000 declarations | 20,000,000,000 | nothing is waiting. The clock is the limit, and the reader is holding it. |
| more than that | the kernel's default | a report that arrives beats a declaration that might. |

The threshold is measured as well. A single-declaration arena test carries its
whole dependency tree, so `grind-ring-5` is 2,275 declarations and the arena's
own `init-prelude` is 1,824, while the real libraries start at 59,349. Ten
thousand sits in that gap with room on both sides. `REAN_FUEL` still overrides
both, and every measurement in this book was taken with it.

---

## 29.6 The score

| | chapter 28 | now |
|---|---|---|
| accepted of 126 good | 115 | **124** |
| rejected of 72 bad | 72 | **72** |
| wrongly accepted | 0 | **0** |
| wrongly rejected | 11 | **0** |
| declined | 0 | 2 |

And the three libraries, which is the measurement that had to hold still:

| library | declarations | checked | before | time |
|---|---|---|---|---|
| `Init`, the prelude | 59,349 | 55,835 | 55,835 | 144 s |
| `Std` | 99,619 | 95,241 | 95,237 | 231 s |
| `Lean`, the compiler | 171,817 | 150,424 | 150,420 | 247 s |

Four more declarations in each of the two larger ones, and 506 tests pass.

---

## 29.7 The two that are left, and what each one needs

**`perf/let-fold` needs `let` without substitution.** The declaration is

```text
let d := bits #n 0; (rfl : d + 0 = Nat.add d 0)
```

where `bits #n 0` is a closed `Nat` that takes 2ⁿ steps to evaluate. The two
sides of the equation differ only in how the addition is written, so unfolding
`HAdd.hAdd` settles it in one step. We substitute the value of the `let` into
the body first, which makes both sides **closed** arithmetic, and the literal
rules of chapter 21 then try to evaluate `bits`.

Lean binds `d` in the local context as a definition and checks the body with
`d` as a free variable, so it never evaluates it. That is the fix, and it is
not a small one: `LocalDecl` would carry a value, `whnf` would unfold a free
variable that has one, and every comparison would have to agree about when it
does. It is the next thing to build and it is not this chapter.

**`perf/magma-list-deep-n36` needs speed.** It is a `decide` certificate over
a magma on `Fin 36` with an inline list operation table, and it is the one test
here that asks for nothing clever: it needs more than twenty thousand million
nodes of honest reduction. `magma-list-deep-n21`, the same workload at a
smaller scale, passes in five seconds.

### And one thing the meter still cannot see

The budget counts **nodes built**. A comparison builds nothing, so a kernel
that spins inside `alpha_eq` spends no budget at all, and two of these tests
ran for three hundred seconds without the limit noticing. `cheap_eq` bounds
each comparison, which is why nothing hangs now, and it does not bound **how
many**. The honest fix is to charge for comparison work as well, the way
`Sub::new` charges for construction, and until that exists the arena's own
timeout is what stands between us and a term built to spin.

---

## 29.8 How other systems do it

The arena is full of answers to exactly these questions, and two of them are
about this chapter's bug.

| | how it keeps a graph a graph |
|---|---|
| the official kernel | terms are **maximally shared**, so one rewrite serves every use, and a pointer compare settles most equalities |
| `nanobruijn` | pure de Bruijn indices with **lazy shifting**: a pointer carries an offset, so a shift is arithmetic and never allocates. Caches are bucketed by binder depth. |
| `lean4lean` | Lean's own algorithms, in Lean, so it inherits the sharing and the caches |
| `rean` | `Arc` sharing, a substitution memo keyed by node and depth, and `cheap_eq` |

Three notes.

- **Maximal sharing is the design that makes everything else cheap.** Chapter
  26 priced hash-consing in this kernel at 1.7 times slower with an 82% hit
  rate, and that measurement stands. What this chapter adds is that without it,
  every cache confirmation and every rewrite has to be written to preserve
  sharing by hand, and three of them were not.
- **`nanobruijn` exists to answer this very test.** Its description names
  `perf/fueled-chain` as the test it times out on, and its design notes are an
  argument about binder representation. A suite that makes implementations
  argue with each other in public is worth more than any one implementation in
  it.
- **The ranking puts soundness first and speed last**, and that order is the
  whole reason this chapter comes after chapter 28 rather than before it. A
  checker that is fast and wrong has the numbers of a checker that does not
  work.

---

## 29.9 References

**Our code**

- `crates/rean/src/main.rs`, for the four exit codes
- `crates/rean/src/lib.rs`, for `Verdict::Declined` and `budget_for`
- `crates/rean_kernel/src/expr.rs`, for `Expr::same_node`, `SubMemo` and the
  two walks that are no longer walks
- `crates/rean_kernel/src/typeck.rs`, for `cheap_eq`
- `tools/arena.py`, which now reads the exit code and nothing else
- `tools/arena-checker.yaml`, which is the submission

**The suite**

- The Lean Kernel Arena, and its README for the interface this chapter
  implements. <https://github.com/leanprover/lean-kernel-arena>
- `nanobruijn`, for lazy shifting and depth-stratified caches.
  <https://github.com/nomeata/nanobruijn>

**Read more**

- Courant and Leroy, POPL 2026, which `perf/shared-subterm` is taken from, for
  what a checker must do to consume a term through its representation.
- Filliâtre and Conchon, *Type-safe modular hash-consing*, 2006, for the
  design that makes all of this unnecessary and costs something else.
  <https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf>
