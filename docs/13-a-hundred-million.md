# Chapter 13 — A hundred million

Chapter 12 left 107 failures and a ranking. One declaration,
`Nat.mul_add_div._f`, held up 4,807 of the 5,827 declarations that the checker
could not read — 82% of what remained.

This chapter follows that one declaration down to a three-line fix, and the
route is four questions, each answered by a measurement rather than a guess.

```sh
devbox run -- cargo test -p rean_kernel --test comparison
```

---

## 13.1 The profile had stopped being useful

Chapter 12 already profiled this declaration, and the stack said:

```text
infer_type -> is_def_eq -> spine_eq -> whnf -> iota_step -> whnf -> iota_step
```

Nested ι, each step doing a β and a substitution. True, and not actionable.
"The kernel is reducing" is what a kernel does. The profile can say **where** the
time goes, and it cannot say **what** is being reduced.

So the next instrument is not a profiler. It is a counter, and it took eleven
lines of temporary code that no commit kept.

### Question one: which recursor?

Count the name of every recursor that the ι rule fires, and print the table when
the budget runs out.

```text
      520370  Nat.rec
         384  List.rec
         214  Bool.rec
         118  Decidable.rec
```

`Nat.rec` fires **1,350 times** more often than anything else. That is not a
distribution. That is one loop.

### Question two: on which number?

`Nat` literals are stored as digits, so ι on one needs the constructor form, and
`to_ctor_if_lit` makes `Nat.succ (n-1)` out of `n`. That peels **one** successor
per step. So record every literal it peels.

```text
--- 346264 literal peels, largest: [100000000, 99999999, 99999998, ...] ---
```

The checker is counting down from **a hundred million**, one at a time. A
hundred million peels at about four thousand units of work each is four hundred
billion units, and the budget is twenty million.

### Question three: whose number is it?

Print the recursor application once, the first time a literal above a million
appears.

```text
HUGE literal 100000000 under Nat.rec
  arg 0: fun (x : Nat) => (fun x1 x2 => Nat.below.{1} (fun x3 => Nat → Bool) x1 → Bool) ...
  arg 3: Nat.Linear.fixedVar
```

`Nat.Linear.fixedVar` **is** a hundred million. It is a sentinel index in Lean's
linear arithmetic, and the motive `Nat → Bool` says the thing being computed is
a two-argument function into `Bool`, compiled through `Nat.below` and
`Nat.brecOn`.

### Question four: how did we get there?

Keep the last twelve names that δ unfolded.

```text
last δ unfolds: ["Nat.Linear.fixedVar", "OfNat.ofNat", "instOfNatNat",
                "Nat.ble", "Nat.brecOn", "Nat.ble._f", "Nat.ble.match_1", ...]
```

**There it is.** The kernel unfolded `Nat.ble`.

---

## 13.2 Why that one line is the whole bug

`Nat.ble` is one of the functions the kernel computes **directly**. Chapter 4
added that, and for the same reason this chapter exists: without it, `2 + 3`
would unfold through `Nat.rec` three times.

So the kernel should have answered `Nat.ble 100000000 2` in one step and never
looked at the definition. Instead it declined, and δ then unfolded `Nat.ble`
into the structural recursion that defines it. That recursion walks its
**first** argument through `Nat.brecOn`, which builds a `Nat.below` tower of
that argument's depth.

The depth was a hundred million.

And the reason it declined is three characters wide. Here is the old reader:

```rust
pub fn value(e: &Expr) -> Option<u128> {
    match e {
        Expr::Lit(Literal::Nat(digits)) => digits.parse().ok(),
        _ => None,
    }
}
```

The second argument of that comparison was not a literal. It was
`Nat.succ (OfNat.ofNat Nat 1 (instOfNatNat 1))`, which is the number **2** in
constructor form. `value` read it as "not a number".

Chapter 4 named this exact obligation and met half of it:

> A literal must behave like a constructor application wherever the rules expect
> one, and a literal must be **definitionally equal** to the matching
> constructor chain.

Both halves were done, for **comparison**. `is_def_eq` has `nat_lit_eq`, so `2`
and `Nat.succ 1` compare equal. Nothing read the constructor form for
**computation**. The two directions are not the same rule, and the gap between
them cost a factor of ten thousand.

---

## 13.3 The reduction has to happen inside the loop

The first attempt was a pure function that peels `Nat.succ` and adds one. It
did not work, and the reason is worth a paragraph.

`whnf` is **weak head** normal form. It reduces the head and stops. So
`Nat.succ (OfNat.ofNat Nat 1 (instOfNatNat 1))` is already in weak head normal
form: its head is a constructor, and no rule applies. The `OfNat.ofNat`
underneath is untouched, and a reader that only looks at the surface sees
`Nat.succ` of something it cannot read.

So the reader must reduce as it peels, which means it needs the checker and not
just the term:

```rust
fn read_nat(&mut self, e: &Expr) -> TypeResult<Option<u128>> {
    let mut extra: u128 = 0;
    let mut current = self.whnf(e)?;
    loop {
        if let Some(found) = nat_lit::value(&current) {
            return Ok(found.checked_add(extra));
        }
        match nat_lit::shape(&current) {
            Some(NatShape::Zero) => return Ok(Some(extra)),
            Some(NatShape::Succ(inner)) => {
                extra = extra.checked_add(1)?;
                current = self.whnf(&inner.clone())?;
            }
            None => return Ok(None),
        }
    }
}
```

The loop ends because each step takes a strictly smaller term. It is cheap when
it fails, because a head that is not `Nat.succ` stops it after one `whnf`.

---

## 13.4 A test that measures work, not time

Same discipline as chapters 11 and 12: the budget is a **count**, so a test
built on it gives the same answer on every machine.

The environment declares `Nat`, its two constructors, `Bool`, and
`Big : Nat := 100000000`. It deliberately does **not** declare `Nat.ble`, so the
kernel's own rule for two numbers is the only way to answer, and a decline
leaves the term stuck where the test can see it.

`Big` is a definition and not a literal on purpose, because
`Nat.Linear.fixedVar` is one too, and δ has to run before the number can be
read at all.

```rust
let term = Expr::const_("Nat.ble", vec![]).apps([
    Expr::const_("Big", vec![]),
    Expr::const_("Nat.succ", vec![]).app(Expr::nat("1")),
]);
assert_eq!(tc.whnf(&term).unwrap().pretty(), "Bool.false");
```

Tests: `a_number_is_read_through_the_constructor_form`,
`a_number_is_read_through_a_chain_of_constructors`, and
`something_that_is_not_a_number_is_not_read_as_one`, because a free variable is
not a number and the rule must decline rather than invent an answer.

I reverted the fix and watched the first two fail. A regression test that passes
both ways is not a test, and this is the third time in three chapters that
checking it was worth the minute.

---

## 13.5 What it bought

On the slice that holds `Nat.mul_add_div._f` and its 1,171 dependencies:

| | checked | time |
|---|---|---|
| before, at 20,000,000 | 1,171 of 1,172 | 1 s |
| before, at 20,000,000,000 | 1,171 of 1,172 | 58 s |
| **after, at 20,000,000** | **1,172 of 1,172** | **1 s** |

A declaration that wanted more than twenty **billion** units now finishes inside
twenty million. That is a factor of a thousand, from three lines.

And the committed regression slice of 487 declarations, which had been **483 of
487** for this whole project, is now **487 of 487**.

On the whole prelude:

| | checked | failed | blocked | time |
|---|---|---|---|---|
| chapter 12 ended at | 39,244 | 115 | 18,153 | 192 s |
| after this fix | **48,804** | 536 | 8,172 | 141 s |

9,560 more declarations, and 10,000 fewer waiting on a failure.

Read the failure column with the checked column, as chapter 10 §10.5 insists.
536 is more than 115, and it is not worse. Those declarations were **blocked**
before: the checker had never asked them a question, so they could not fail. Now
it asks. The failures also spread out — the worst root used to hold up 15,272
declarations, and the worst now holds up 2,593.

---

## 13.6 And then the report cost more than the check

The first full run after the fix did not finish. Forty minutes in, every one of
the 57,512 declarations had a verdict and nothing was printed.

A sample said why, and it was not the kernel:

```text
rean::main -> Thread::join -> ... -> Expr::collect_constants
                                  -> Expr::collect_constants
                                  -> Expr::collect_constants   (× 8 deep)
```

`collect_constants` reads the names a term mentions. It is called by
`axioms_of`, which answers "what does this declaration rest on" by walking the
declaration's whole transitive closure. That is the right **definition**, and
chapter 6 earns it. It is the wrong **algorithm** to call once per declaration,
because it re-walks the term of every declaration it meets, once per caller.

With 39,244 accepted declarations it finished. With 48,804 it did not, and that
is the shape of a quadratic: the fix to the kernel made the report the problem.

The export is **topologically ordered**, so there is no need to walk anything
twice. A declaration rests on whatever its direct dependencies rest on, plus
itself if it is an axiom, and every dependency outside its own mutual group is
already answered.

```rust
for used in &uses {
    if let Some(axioms) = rests_on.get(used) {
        found.extend(axioms.iter().cloned());
    }
}
```

A whole mutual group shares one answer, and that is right rather than a
shortcut: its members refer to each other, so they rest on the same things.

One more quadratic sat beside it. `rejected` was a `Vec`, and
`rejected.contains(used)` runs for every dependency of every declaration, so
each test walked every failure so far. It is a `HashSet` now.

| | time for the prelude |
|---|---|
| before | would not finish |
| after | **141 s** |

141 seconds is also **faster than the 192 seconds** of chapter 12, while
checking 9,560 more declarations. The report had been costing a quarter of the
run all along, and nobody had looked, because it had never been the thing that
failed.

**A fix to the slow part makes some other part the slow part. Measure again
after you win.**

---

## 13.7 The lesson, which is about instruments

Chapters 11 and 12 said: take one declaration, sweep the budget, read the
profile. That was enough twice. Here it was not, and the reason is worth
keeping.

A profiler answers "where does the time go" in terms of **your** code. Every
frame it showed was innocent: `whnf` reduces, `iota_step` applies ι, and
`instantiate` substitutes. The fault was not in any of them. The fault was that
they were called at all, about a term nobody needed to reduce.

To see that, the instrument has to count things in the language of the
**problem** rather than the language of the program: which recursor, which
number, which definition. Eleven lines of counter found in one run what the
profiler could not say in four.

None of those eleven lines are in the repository. They should not be. But the
numbers they produced are in this chapter, which is the part worth keeping.
