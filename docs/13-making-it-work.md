# Chapter 13 — Making it work

> **Where you are.** Chapter 13 of 28, in Part III of [the guide](README.md).
>
> **Before this.** [The ground truth](12-the-ground-truth.md), and
> Part I chapter [7](book/07-inductive-types.md), section 7.9, which names the
> two extras this chapter builds.
>
> **After it you can** say what a kernel owes you when it stores `3` as digits,
> and why a bad `inductive` must be refused rather than trusted.

A checker that reads one real module is not yet a checker that reads Lean.

This chapter asks one question. **Does it handle what a beginner writes?** The
answer was no, and the six things that were missing are the four rules of this
chapter.

```sh
devbox run -- cargo run -p rean -- check fixtures/lean4export/Nat.add_succ.ndjson
devbox run -- cargo test --workspace
devbox run coverage
```

---

## 13.1 The honest answer was no

Six probes, all written in a scratch test, all shapes a person writes on the
first day with Lean. Every one of them failed.

| Probe | Before chapter 13 |
|---|---|
| `whnf(2 + 3)` | a wall of `Nat.brecOn`, stuck |
| `is_def_eq(2 + 3, 5)` | **false** |
| `is_def_eq(1, Nat.succ Nat.zero)` | **false** |
| `is_def_eq(Nat.succ (Nat.succ (Nat.succ Nat.zero)), 3)` | **false** |
| `whnf(Eq.rec … h)` for an opaque `h` | stuck |
| a crafted `inductive` that proves `False` | **accepted** |

The second row is the sharpest. `2 + 3 = 5` is the first theorem anybody
writes, `rfl` proves it, and our kernel said no.

So the lesson of chapter 12 cuts both ways. **Real data covers the paths that
real data uses, and says nothing about the rest.** One real module exercised
δ, ι, projections and universe polymorphism. It never used a `Nat` literal, so
nothing about literals worked.

---

## 13.2 `Nat` literals: one choice, two obligations

`Expr::Lit(Literal::Nat(..))` exists for speed. In the theory, `3` is
`Nat.succ (Nat.succ (Nat.succ Nat.zero))`. Nobody wants a million nested
constructors, so the kernel stores the digits.

That choice buys speed and costs **two** obligations. A kernel that skips either
one is wrong.

### Obligation 1: a literal must act like a constructor

The ι rule needs a constructor application as its major premise. So a literal
has to turn into one, on demand and one level deep:

```rust
pub fn to_ctor(n: u128) -> Expr {
    if n == 0 {
        Expr::const_("Nat.zero", vec![])
    } else {
        Expr::const_("Nat.succ", vec![]).app(lit(n - 1))
    }
}
```

`iota_step` and `proj_step` each call it. Now `Nat.add n 3` fires the `Nat.succ`
rule, because `3` becomes `Nat.succ 2`.

### Obligation 2: a literal must equal the constructor chain

```rust
fn nat_lit_eq(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
    let (number, other) = match (nat_lit::value(a), nat_lit::value(b)) { /* … */ };
    match nat_lit::shape(other) {
        Some(NatShape::Zero) => Ok(number == 0),
        Some(NatShape::Succ(inner)) => {
            if number == 0 { return Ok(false); }
            self.is_def_eq(&nat_lit::lit(number - 1), inner)
        }
        None => Ok(false),
    }
}
```

The literal shrinks by one on each step, so the recursion ends.

One trap avoided. An earlier draft folded `Nat.succ 4` into `5` inside `whnf`.
That rule and `to_ctor` are inverse, so the two would have looped forever. The
cure is to keep the conversion inside the ι rule, where it is a one way step,
and never as a `whnf` rule.

### Direct arithmetic

Without it, `2 + 3` unfolds through `Nat.rec` once per unit. A real program
would exhaust the reduction budget on the first large number. So the kernel
computes:

| Group | Functions |
|---|---|
| arithmetic | `add`, `sub`, `mul`, `div`, `mod`, `pow`, `gcd` |
| bits | `land`, `lor`, `xor`, `shiftLeft`, `shiftRight` |
| comparison | `beq`, `ble` |

Three details that matter more than they look:

- **`sub` saturates.** A Lean `Nat` has no negative value, so `2 - 5` is `0`.
- **Division by zero gives zero.** Lean defines it that way so the function
  stays total.
- **An overflow refuses to answer.** This module uses `u128`, and the real
  kernel links a big number library. Past the limit the term stays **stuck**:

  ```rust
  let Some(out) = nat_lit::binop(name, a, b) else {
      // The answer does not fit in a `u128`. Stay stuck rather than lie.
      return Ok(None);
  };
  ```

  A stuck term is correct. A wrapped answer would be a false theorem.

---

## 13.3 K-like ι reduction

`Eq.rec` is the example. `Eq` has one constructor, `Eq.refl`, and that
constructor has **no field**. So a proof of `a = b` carries nothing beyond its
own existence, and the recursor may reduce even when the proof is an opaque
variable.

```rust
fn ctor_when_k(&mut self, rec: &RecursorVal, major: &Expr) -> TypeResult<Option<Expr>> {
    if !rec.k { return Ok(None); }
    // … already a constructor? nothing to do.
    let major_type = self.whnf(&self.infer_type(major)?)?;
    let (head, type_args) = major_type.unfold_apps();
    // … the head must be an inductive of this recursor's group
    // … the inductive must have exactly one constructor, with no field
    let ctor_app = /* the sole constructor, applied to the type's parameters */;
    // The result must have the same type, so an index mismatch cannot slip in.
    if self.is_def_eq(&self.infer_type(&ctor_app)?, &major_type)? {
        return Ok(Some(ctor_app));
    }
    Ok(None)
}
```

Note the shape of it. The rule reads the **type** of the major premise, not the
premise itself. That is why `whnf` had to be able to call `infer_type`, and why
chapter 11 put all three functions on one struct.

Note also the last check. Without it, a recursor could reduce at the wrong
index, and that is a soundness hole and not a missing feature.

Three guards keep it narrow, and each has a test:

- two constructors: there is no sole constructor to build
- one constructor with a field: the field value is unknown
- a major premise of the wrong type: the head is not this inductive

---

## 13.4 The quotient rules

`Quot` is a kernel primitive. You cannot build it from an `inductive`
declaration, so it needs its own rule. See Part I chapter 7, section 7.9.

```text
Quot.lift α r β f h (Quot.mk α r a)  ~>  f a
Quot.ind  α r β h   (Quot.mk α r a)  ~>  h a
```

The argument positions are fixed, and the code states them once:

```rust
let (function_index, major_index) = match quot.kind {
    QuotKind::Lift => (3usize, 5usize),
    QuotKind::Ind => (3usize, 4usize),
    QuotKind::Type | QuotKind::Ctor => return Ok(None),
};
```

`Quot` and `Quot.mk` are data, not rules. They never reduce.

Our fixture holds no `Quot`, so these rules have no ground truth yet. They have
tests, and the tests say plainly that they exercise the reduction and not the
types.

---

## 13.5 Strict positivity: the soundness check

An `inductive` declaration is the one place where a user hands the kernel a new
rule. Accept any shape and the user proves `False`:

```text
inductive Bad | mk : (Bad → False) → Bad
```

That says "a `Bad` is a function from `Bad` to `False`". Give it to itself and
you get `False`, with no axiom and no mistake anywhere else.

### The rule

Write the type of a constructor as a chain of binders:

```text
(p₁ : P₁) … (pₙ : Pₙ)   (f₁ : F₁) … (fₘ : Fₘ)   →   I p₁ … pₙ i₁ … i_k
 ^ the parameters         ^ the fields                ^ the result
```

Two conditions:

1. The result is the inductive type, applied to arguments.
2. The inductive type occurs **strictly positively** in every field type.

And strictly positive in a field type `F` means: write `F` as its own chain,
`(x₁ : A₁) → … → (x_j : A_j) → B`. Then

- no `A` may mention the name at all, which is the strict part, and
- `B` may mention it only as the head of an application.

So `Nat → I` is fine, and `I → Nat` is not.

### Where the check runs

At the **constructor**, not at the inductive type. The export format lists the
inductive type first, so when a constructor arrives its owner is already in the
environment. That fits the incremental harness of chapter 12 exactly.

### Two things a check must not do

A check that refuses correct code is worse than no check. Two tests guard
against that:

- `a_reflexive_inductive_is_still_accepted`: `(Nat → Good) → Good` is sound.
- `the_positivity_check_accepts_every_real_constructor`: all seven constructors
  that Lean wrote in the fixture pass.

And one limit is honest rather than hidden. A **nested** inductive, such as
`inductive Tree | node : List Tree → Tree`, is **skipped** and not rejected. The
export format records the depth in `num_nested`, and the check steps aside when
it is not zero.

---

## 13.6 Coverage as a tool

This chapter also measured test coverage, and the measurement did real work.

```sh
devbox run coverage
```

| Stage | Regions | Lines |
|---|---|---|
| start of the chapter | 77.96% | 79.24% |
| end of the chapter | **96.16%** | **98.57%** |

Nine of nineteen files reach 100% of lines. 337 tests.

### What it found, in order of value

**1. The driver could not be tested at all.** `main.rs` sat at 0%, and 447
regions of it were a third of everything uncovered. A binary's code is not
reachable from a test. The cure is a design change, not a test: the commands
moved into `crates/rean/src/lib.rs` and each one **returns a value** instead of
printing one. `main.rs` now does the printing and nothing else.

That split is worth more than the coverage number. A command that returns a
value can be asserted on. A command that prints cannot.

**2. One real module exercises only part of a reader.** The chapter 12 fixture
left the reader at 72%. It has no `letE`, no `mdata`, no literal, no `axiom`, no
`opaque`, and no `quot`, because one module did not need them. So ground truth
and unit tests are **complementary, not substitutes**: ground truth proves the
paths that real data takes, and only a written test reaches the rest.

**3. Two dead branches.** Coverage would not go green on two lines of
`level.rs`, and the reason turned out to be real:

```rust
Level::IMax(a, b) => {
    let a = a.normalize();
    let b = b.normalize();
    if b.is_zero() {        // unreachable
        return Level::Zero;
    }
```

If `b` normalizes to zero then `b` is semantically zero, so `b.to_nat()` gives
`Some(0)`, so the whole `imax` gives `Some(0)`, and the fast path at the top of
`normalize` already returned. The same holds for the `Level::Zero` arm of
`Display`. Both now carry a comment saying so, so that the next reader does not
spend an hour on them.

### The 51 lines that remain

They are not an oversight, and they fall into three groups.

| Group | Example |
|---|---|
| unreachable by design | the two `level.rs` branches above |
| a panic inside a test | `panic!("both terms are lambdas")` in a `let … else` |
| a branch no input can produce | `rean/src/lib.rs` reporting a declaration the reader lost |

So the target was never literally 100%. The target is **every branch that an
input can reach**, and that one is met.

---

## 13.7 Where the checker stands

| Rule | Status |
|---|---|
| β, ζ | chapter 10 |
| δ, ι, η, proof irrelevance, projections | chapter 11 |
| `Nat` literal arithmetic and conversion | **chapter 13** |
| K-like ι | **chapter 13** |
| the two quotient rules | **chapter 13** |
| the strict positivity check | **chapter 13** |

| Checkpoint | Score |
|---|---|
| level 1, our kernel checks Lean's terms | **32 of 32** |
| level 2, our pipeline inhabits Lean's types | 0 of 32, needs a parser |
| level 3, our term matches Lean's term | 0 of 32 |

## 13.8 What is still missing

| Missing | Why it matters |
|---|---|
| recursor re-derivation | we trust the recursor and the ι rules the file hands us |
| positivity for a nested inductive | skipped, not checked |
| big number arithmetic | a literal past `u128` stays stuck |
| a full level normal form | a hard pair of open levels can fail to match |
| `String` literal operations | the real kernel computes on them |
| a bigger fixture | one module is not the prelude |

**Recursor re-derivation is the last soundness gap.** A checker that believes
the recursor it reads is checking arithmetic, not soundness. Everything else on
that list makes the checker less useful. That one makes it less trustworthy.

---

## 13.9 Exercises

1. An early draft folded `Nat.succ 4` into `5` inside `whnf`. Say exactly what
   goes wrong, and why the ι rule is the right place for the conversion.
2. `nat_lit::binop` returns `None` on overflow. What would go wrong if it
   wrapped instead? Write the false theorem it would let through.
3. `ctor_when_k` checks that the built constructor has the same type as the
   major premise. Drop that check and describe the unsound reduction.
4. Why does the positivity check run at the constructor and not at the
   inductive type?
5. `Nat.sub` saturates and `Nat.div` by zero gives zero. Both keep a function
   total. Why does a dependent type theory care about totality?
6. Our checker reaches 32 of 32 and is still not trustworthy. Name the one
   remaining reason.

### Answers

1. `whnf` folding `Nat.succ (Lit n)` to `Lit (n+1)` is the inverse of
   `to_ctor`, which turns `Lit (n+1)` into `Nat.succ (Lit n)`. Put both in
   `whnf` and it alternates forever. The ι rule converts once, for its own
   major premise, and never calls `whnf` on the result, so there is no cycle.
2. `Nat.add` on two numbers near `u128::MAX` would give a small number. Then
   `huge + huge = 4` would hold by `rfl`, and from a false equation you can
   derive anything.
3. The constructor is built from the **parameters** of the major premise's
   type. Without the type check, a recursor at a mismatched **index** could
   reduce, so you could transport a proof about `a` to a claim about an
   unrelated `b`.
4. Because a constructor is where the new rule actually arrives, and because
   the inductive type is already in the environment when its constructors are.
   Checking at the inductive type would need its constructors, which come
   later.
5. Every function in the theory must be total, because the type checker
   evaluates functions while it checks. A partial function would let the
   checker diverge or fail on a well typed term.
6. We do not re-derive the recursor. The file hands us the recursor and the
   right hand side of every ι rule, and we believe them.

---

## 13.10 How other systems do it

Each of the four rules in this chapter is a place where a real system departs
from the clean theory, and each one departs in the same direction.

| Rule | Lean 4 | Rocq | Agda |
|---|---|---|---|
| a number | a literal in the kernel, with a big number library, and rules for `add`, `sub`, `mul`, `div`, `mod`, `pow`, `gcd`, the bit operations and the comparisons | `Int63` and a float, as kernel primitives beside the inductive `nat` | a `BUILTIN NATURAL`, which the backend maps to a machine number |
| K-like ι | in the kernel, for a type with one constructor and no field. Section 5.3. | the same effect, by the rules for a singleton `Prop` | **optional**. The flag `--without-K` turns it off. |
| a quotient | `Quot` is a kernel primitive, with the axiom `Quot.sound` | none. A user works with a setoid instead. | a higher inductive type, in cubical Agda |
| strict positivity | in the kernel, and a failure is an error | in the kernel, as part of the guard condition | in the kernel, and a flag can switch it off |

Three notes.

- **A literal is a trade, and the price is two obligations.** Section 5.2 names
  them. Lean's kernel pays the same two, in `reduce_nat` and in the comparison
  beside it, and it adds a guard that refuses to build a number too large to
  hold. Our version refuses at the limit of a `u128`, for the same reason.
- **Turning positivity off is not a small thing.** Agda has a flag for it, and
  with that flag a user can prove `False`. Section 5.5 builds the type that
  does it, so the test suite holds a real proof of the danger.
- **A quotient is where the three systems differ most.** Lean takes four
  constants and one axiom, and gets a quotient that computes. Rocq takes
  nothing and asks the user to carry an equivalence relation by hand.

## 13.11 References

**Our code**

- `crates/rean_kernel/src/nat_lit.rs` and `crates/rean_kernel/src/positivity.rs`
- `crates/rean_kernel/src/typeck.rs`, the `ctor_when_k` and `quot_step` methods
- `crates/rean_export/tests/completeness.rs`, the six probes as real tests
- `crates/rean/src/lib.rs`, the driver that returns values

**Lean's own source**

- `src/kernel/type_checker.cpp`. The `Nat` rules are `reduce_nat`,
  `reduce_bin_nat_op`, `reduce_pow` and `reduce_bin_nat_pred`, and the size
  guard beside them is `check_nat_size`.
- `src/kernel/inductive.cpp`. The positivity test is `check_positivity`, the
  K-like case is in the same file, and `nat_lit_to_constructor` is Lean's
  version of our `to_ctor`.
- `src/kernel/quot.cpp`, which adds the four `Quot` constants and computes one
  rule

**Read more**

- Paulin-Mohring, *Inductive definitions in the system Coq*, 1993, for the
  positivity condition as a rule.
  DOI [10.1007/BFb0037116](https://doi.org/10.1007/BFb0037116)
- Agda, `--without-K`, for K as a choice rather than a given.
  <https://agda.readthedocs.io/en/latest/language/without-k.html>
- Agda, termination checking, for the other way to make ι safe.
  <https://agda.readthedocs.io/en/latest/language/termination-checking.html>
- Rocq, inductive types, for the guard condition.
  <https://rocq-prover.org/doc/master/refman/language/core/inductive.html>
- Carneiro, *The Type Theory of Lean*, for the `Nat` rules and the quotient
  rules as the theory states them.
  <https://github.com/digama0/lean-type-theory>

---

**Next:** [What a checker must check](14-what-a-checker-must-check.md)
