# Chapter 15 — The last two hundred and forty-eight

The checker reads **57,264 of the 57,512** declarations of the Lean prelude.
That is 99.57%, and it took forty-four minutes at a budget forty times the
default.

This chapter is about the 248 that are left, and it is mostly a list of things
that turned out **not** to be the reason. Five hypotheses, each plausible, each
refuted by a measurement. None of them cost more than twenty minutes, and
together they are worth more than a guess that happened to be right.

---

## 15.1 They are one family

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

## 15.2 Not the budget

The first thing to rule out, because it is the cheapest.

| budget | stack | result on the slice |
|---|---|---|
| 20,000,000 | 512 MB | fails |
| 800,000,000 | 8 GB | fails |
| **4,000,000,000** | **32 GB** | **still fails** |

Two hundred times the default budget, and a stack sixty times the default.
`Int32.ofInt_eq_ofNat` does not finish. Everything else in its slice does: 10,747
of 10,748.

So there is a real inefficiency. The rest of this chapter is four attempts to
name it.

---

## 15.3 Not `u128` overflow, and my instrument was lying

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

## 15.4 Not cache thrash

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

## 15.5 Not an under-applied `Nat.sub`

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

## 15.6 Not the universe substitution either

`Nat.casesOn` is unfolded 283,803 times, and each unfold substitutes the
universe arguments into its value, which walks the whole value. The same name
with the same levels gives the same body every time, so a cache keyed by name
and levels should remove 283,803 walks.

| | checked | time |
|---|---|---|
| without the cache | 10,385 | 33 s |
| with it | 10,385 | 35 s |

Nothing, and slightly slower. Reverted, by the rule chapter 12 set when
`rec.clone()` measured to nothing: a cache for an unmeasurable gain is a cost
with no payment.

---

## 15.7 What it actually is

With five explanations gone, the remaining reading is the plain one. For this
single declaration the kernel performs about **1.3 million reduction steps**:

```text
447,907  iota Nat.rec
283,803  delta Nat.casesOn
220,996  delta Nat.mul.match_1
220,848  delta Nat.sub._f
114,131  peel of the literal 4294967296
```

and each step **builds a term**. Chapter 13 measured 84 million nodes built for
a comparable declaration. There is no shortcut being missed. The work is being
done, correctly, one freshly built term at a time.

That is the cost of an **eager** `whnf`, and chapter 14 §14.7 already named the
two cures and the reason we have not taken them. Both change what a term **is**:

- a term as a pointer **plus a shift**, so that lifting is O(1) and one cache
  entry serves every shifted variant of a subterm;
- normalisation by evaluation, which the fastest checker in the arena uses.

The honest position is this. **99.57% is where an eager kernel with four caches
gets to.** The last 0.43% is not a missing rule, not a budget, and not a cache.
It is the representation, and changing it is a different project from the one
these fifteen chapters describe.

---

## 15.8 The part worth keeping

Five hypotheses, five measurements, five hours. Nothing in the kernel changed.

That reads like waste and is not, because each measurement **removed** something
from the list, and the list is what a future reader inherits. The next person to
open this file does not have to re-test the budget, the cache size, the overflow
path, the under-application, or the universe substitution. They are all ruled
out, with numbers.

And one of the five was worth the whole day on its own: the instrument that
watched one exit of three. Every number this project reports comes from an
instrument, and that one had been quietly telling me what I wanted to hear.

> Before you trust a count of something not happening, check that you are
> counting every way it could happen.
