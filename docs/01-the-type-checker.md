# Chapter 1 — The type checker

Chapter 0 described the rules. This chapter runs them.

At the end of chapter 0 the kernel held data and one reduction. It could not
check a single proof. Now it can check every proof of implicational logic.

Run it:

```sh
devbox run -- cargo run -p rean -- prove
devbox run -- cargo test -p rean_kernel --test typeck
```

Every claim here has a test in `crates/rean_kernel/tests/typeck.rs`.

---

## 1.1 The goal

One line. Does this proof prove this proposition?

```
fun (α : Prop) (h : α) => h        against        (α : Prop) → α → α
```

In words: "for every proposition `α`, if `α` holds then `α` holds". The proof is
the identity function.

The output of `rean prove`:

```
== the proof ==
de Bruijn : Lam { binder_name: `α, binder_type: Sort(Zero),
                  body: Lam { binder_name: `h, binder_type: BVar(0),
                              body: BVar(0), info: Default }, info: Default }
readable  : fun (α : Prop) => fun (h : α) => h

== infer_type ==
the proof has type : (α : Prop) → α → α

== check ==
accepted. The proposition holds.
the proposition lives in : Prop
```

Read the last line. The proposition itself lives in `Prop`, not in `Type`. That
is `imax 1 0 = 0` from chapter 0, section 0.10, and now a running program
computes it.

---

## 1.2 The four pieces

| Piece | File | Job |
|---|---|---|
| `alpha_eq` | `crates/rean_kernel/src/expr.rs` | compare two terms, and skip the binder name |
| `LocalContext` | `crates/rean_kernel/src/local.rs` | hold `Γ`, and open a binder |
| `whnf` and `is_def_eq` | `crates/rean_kernel/src/typeck.rs` | the relation `≡` |
| `infer_type` | `crates/rean_kernel/src/typeck.rs` | the judgment `Γ ⊢ e : A` |

Together they are 381 lines of code, inside 619 lines of file. That is the
whole trusted core of this chapter. My earlier estimate was 250 lines, and the
extra 130 are the error type and its messages.

---

## 1.3 `alpha_eq`: why `==` is not enough

Chapter 0, section 0.5 flagged this. `Expr::Lam` keeps a `binder_name` for the
printer, and `PartialEq` is derived, so `==` compares that field:

```rust
let with_x = Expr::lam("x", nat.clone(), Expr::bvar(0));
let with_y = Expr::lam("y", nat.clone(), Expr::bvar(0));
assert!(with_x != with_y);          // the derived ==
assert!(with_x.alpha_eq(&with_y));  // the right test
```

The de Bruijn index already carries the meaning. The name is decoration, so a
comparison must drop it.

`alpha_eq` also compares a universe level with `Level::is_equiv`, not with `==`,
so `max 1 4` equals `4`. The test is `is_def_eq_ignores_the_binder_name`.

One honest limit. `Level::is_equiv` compares two **open** levels by shape only.
So `max u 0` and `u` mean the same level and the method still returns `false`. A
real kernel normalizes a level expression first.

---

## 1.4 `LocalContext`: opening a binder

To check `fun (x : A) => b`, the checker must look inside `b`. But `b` holds a
loose `BVar 0` that points at the binder, and the binder is no longer there.

Two cures exist:

1. Walk `b` with a depth counter and renumber on every step.
2. Replace `BVar 0` with a fresh `FVar`, whose number never changes, and put its
   type into `Γ`.

Lean uses the second cure, and so does this code. A checker walks a term many
times, and a renumber on every walk costs too much.

```rust
ctx.with_binder(name, ty, |ctx, id| {
    let opened = body.instantiate(&Expr::FVar(id));   // open
    infer_type(ctx, &opened).map(|t| t.abstract_fvar(id))   // and close again
})
```

`instantiate` and `abstract_fvar` are the pair from chapter 0, section 0.5. This
is what they were for.

Two properties matter:

- **An identifier never repeats.** A push after a pop gives a new number. So a
  stale `FVarId` cannot silently match a live one. The test is
  `an_identifier_never_repeats`.
- **`with_binder` cannot leak.** It pops even when the closure returns an error.
  The test is `the_context_is_clean_after_an_error`.

---

## 1.5 `whnf`: reduce the head

The name is short for weak head normal form:

- **Weak** means the function does not look inside a binder.
- **Head** means it only reduces the outermost shape, and leaves the arguments
  alone.

This version uses two of the five equations of chapter 0, section 0.7:

```rust
pub fn whnf(e: &Expr) -> Expr {
    let mut current = e.clone();
    loop {
        // ζ: a `let` in the head position substitutes its value.
        let (head, args) = current.unfold_apps();
        if let Expr::Let { value, body, .. } = head {
            let reduced = body.instantiate(value);
            let args: Vec<Expr> = args.into_iter().cloned().collect();
            current = reduced.apps(args);
            continue;
        }
        // β: a lambda in the head position takes its first argument.
        if let Some(next) = current.beta_step() {
            current = next;
            continue;
        }
        return current;
    }
}
```

Note the ζ arm. It splits the application spine first, so
`(let f := fun x => x; f) Prop` reduces. The test is
`whnf_unfolds_a_let_under_an_application`.

There is no δ arm, because no constant has a value yet. The test
`whnf_does_not_unfold_a_constant` records that.

---

## 1.6 `is_def_eq`: the same by computation

```
cheap test  ->  reduce both sides  ->  compare the parts
```

```rust
pub fn is_def_eq(a: &Expr, b: &Expr) -> bool {
    if a.alpha_eq(b) { return true; }   // most calls stop here
    let a = whnf(a);
    let b = whnf(b);
    if a.alpha_eq(&b) { return true; }
    match (&a, &b) { /* spine, Lam, Forall */ }
}
```

The order matters for speed. `alpha_eq` is cheap, and most comparisons in a real
check succeed on it. Reduction is the slow path.

Two cases need the recursive step:

- **An application spine.** `f x y` matches `g a b` only when the heads match and
  every argument matches. The test is `is_def_eq_compares_an_application_spine`.
- **A binder.** Compare the binder types, then compare the bodies directly. No
  renumber is needed, because both bodies sit under one binder each, so the two
  index spaces already line up. That is a de Bruijn dividend.

---

## 1.7 `infer_type`: one arm per rule

Each arm of the `match` is one rule of chapter 0, section 0.6.

### The sort rule

```rust
Expr::Sort(level) => Ok(Expr::Sort(level.succ())),
```

One line. `Sort u : Sort (u+1)`.

### The variable rule

```rust
Expr::FVar(id) => ctx.type_of(*id).cloned().ok_or(TypeError::UnknownFVar(*id)),
Expr::BVar(index) => Err(TypeError::LooseBVar(*index)),
```

A `BVar` must never reach this function. The caller opens every binder first. If
one arrives, that is a bug in the caller, so the checker says so.

### The function type rule

```rust
Expr::Forall { binder_name, binder_type, body, .. } => {
    let u = infer_sort(ctx, binder_type)?;
    let v = ctx.with_binder(binder_name.clone(), (**binder_type).clone(),
        |ctx, id| {
            let opened = body.instantiate(&Expr::FVar(id));
            infer_sort(ctx, &opened)
        })?;
    Ok(Expr::Sort(u.imax(&v)))
}
```

This is the arm that makes `Prop` impredicative. Change `imax` to `max` and the
whole character of the logic changes. See exercise 8 of chapter 0.

### The function rule

```rust
Expr::Lam { binder_name, binder_type, body, info } => {
    infer_sort(ctx, binder_type)?;          // the binder type must be a type
    let body_type = ctx.with_binder(binder_name.clone(), (**binder_type).clone(),
        |ctx, id| {
            let opened = body.instantiate(&Expr::FVar(id));
            infer_type(ctx, &opened).map(|ty| ty.abstract_fvar(id))
        })?;
    Ok(Expr::Forall { binder_name: binder_name.clone(),
                      binder_type: binder_type.clone(),
                      body: Arc::new(body_type), info: *info })
}
```

A lambda gets a `Forall`. The shape goes in, and the same shape comes out one
level up. This is the Curry-Howard idea of chapter 0, section 0.2, written as
code.

### The application rule

```rust
Expr::App { fun, arg } => {
    let fun_type = infer_type(ctx, fun)?;
    let Expr::Forall { binder_type, body, .. } = whnf(&fun_type) else {
        return Err(TypeError::not_a_function(fun, fun_type));
    };
    let arg_type = infer_type(ctx, arg)?;
    if !is_def_eq(&arg_type, &binder_type) {
        return Err(TypeError::mismatch(arg, (*binder_type).clone(), arg_type));
    }
    Ok(body.instantiate(arg))      // the type depends on the argument VALUE
}
```

This arm does the most work, and it is the only one that substitutes a value
into a type. Note the `whnf` call. Without it, a function type that hides behind
a redex would look like a non function.

The last line is the heart of dependent types. The test
`the_result_type_depends_on_the_argument_value` shows it:

```
idProof a  :  a → a
idProof b  :  b → b
```

One function, two arguments, two different result types. A C compiler never does
this.

### The let rule

```rust
Expr::Let { binder_type, value, body, .. } => {
    infer_sort(ctx, binder_type)?;
    let value_type = infer_type(ctx, value)?;
    if !is_def_eq(&value_type, binder_type) { /* mismatch */ }
    let opened = body.instantiate(value);      // ζ
    infer_type(ctx, &opened)
}
```

### The helper

Three rules need to know that a term is a type:

```rust
pub fn infer_sort(ctx: &mut LocalContext, e: &Expr) -> TypeResult<Level> {
    let ty = infer_type(ctx, e)?;
    match whnf(&ty) {
        Expr::Sort(level) => Ok(level),
        got => Err(TypeError::NotAType { term: e.clone(), got }),
    }
}
```

### The entry point

```rust
pub fn check(ctx: &mut LocalContext, e: &Expr, expected: &Expr) -> TypeResult<()>
```

Give it a proof and a proposition. It answers yes or no. That is a proof
checker.

Note the first line of `check`. It calls `infer_sort` on the **expected** type
as well. A proof of something that is not a proposition means nothing.

### One note on the error type

`TypeError` carries each term in a `Box`. The reason is size, not style.
`infer_type` returns a `Result` for every node of the term, so the error sits in
the return value of the hot path. An `Expr` is about 64 bytes, and
`TypeMismatch` holds three of them. Without the boxes, every recursive call
would carry 200 bytes for a case that almost never happens.

Three private constructors keep the call sites readable:
`TypeError::not_a_type`, `not_a_function`, and `mismatch`.

---

## 1.8 The worked check, step by step

Target: does `fun (α : Prop) (h : α) => h` have the type `(α : Prop) → α → α`?

| Step | Term | Rule | Result |
|---|---|---|---|
| 1 | `fun (α : Prop) => ...` | function rule | `infer_sort(Prop)` gives `1`, so `Prop` is a type |
| 2 | | `with_binder` | push `α : Prop`, get `_f0` |
| 3 | `fun (h : _f0) => ...` | function rule | `infer_sort(_f0)` gives `0`, so `_f0` is a type |
| 4 | | `with_binder` | push `h : _f0`, get `_f1` |
| 5 | `_f1` | variable rule | the context gives `_f0` |
| 6 | | `abstract_fvar(_f1)` | the inner type becomes `Forall { h, _f0, BVar 1 }` |
| 7 | | `abstract_fvar(_f0)` | the outer type becomes `Forall { α, Prop, ... }` |
| 8 | | `is_def_eq` | compare with the target, up to binder names |

Step 3 is worth a pause. `infer_sort(_f0)` returns 0, because the context says
`α : Prop` and `Prop` is `Sort 0`. So `α` is a **type at level 0**. That is
chapter 0, section 0.9, and the checker now relies on it.

Step 8 is where `alpha_eq` earns its place. The inferred type and the target
agree in every field except the binder name, and `==` would reject it.

---

## 1.9 What the checker can prove now

Every theorem of implicational logic, with no environment and no inductive type.
Four tests record the headline cases.

| Name | Proof | Type |
|---|---|---|
| identity | `fun A h => h` | `(A : Prop) → A → A` |
| K | `fun A B a b => a` | `(A : Prop) → (B : Prop) → A → B → A` |
| composition | `fun A B C f g a => f (g a)` | `(A : Prop) → (B : Prop) → (C : Prop) → (B → C) → (A → B) → A → C` |
| S | `fun A B C f g a => f a (g a)` | `(A : Prop) → (B : Prop) → (C : Prop) → (A → B → C) → (A → B) → A → C` |

Each one is a real theorem. Composition is the proof that implication is
transitive. S is the proof of the distribution law.

Note what these have in common. Each type in the right column was **computed**
by `infer_type` and compared to a string in the test. Nobody wrote the type by
hand.

---

## 1.10 The errors

A checker is only as good as what it refuses. Eight tests cover the refusals.

| Error | When |
|---|---|
| `LooseBVar` | a bound variable reached `infer_type` |
| `UnknownFVar` | a free variable is not in `Γ` |
| `MetavariableLeft` | the elaborator left a hole |
| `NotAType` | a term stood where a type was wanted |
| `NotAFunction` | a term in the function position is not a function |
| `TypeMismatch` | a term has the wrong type for its place |
| `UnknownConstant` | no environment yet |
| `NeedsEnvironment` | a literal or a projection, so no environment yet |

The refusal in `rean prove`:

```
the proof  : fun (α : Prop) => fun (β : Prop) => fun (h : α) => h
the claim  : (α : Prop) → (β : Prop) → α → β
rejected:
  type mismatch for `fun (α : Prop) => fun (β : Prop) => fun (h : α) => h`
    expected: (α : Prop) → (β : Prop) → α → β
    got     : (α : Prop) → Prop → α → α
```

The term proves `α → α`. The claim asks for `α → β`. The checker says so and
shows both types.

Read the `got` line once more. The second binder prints as `Prop →` and not as
`(β : Prop) →`, because the inferred body never uses `β`. That is the arrow rule
of chapter 0, section 0.3 at work in the printer.

---

## 1.11 The gaps, and the test that records each one

Each gap is a test that asserts the **wrong** answer on purpose. When chapter 2
closes the gap, the test fails, and that is the reminder to flip it.

| Gap | Test | What it asserts today |
|---|---|---|
| the δ rule | `whnf_does_not_unfold_a_constant` | a constant does not reduce |
| proof irrelevance | `proof_irrelevance_is_missing` | two proofs of one `Prop` differ |
| the η rule | `eta_is_missing` | `fun x => f x` differs from `f` |
| constants | `a_constant_has_no_declaration_yet` | `Nat` has no type |
| literals | `a_literal_needs_an_environment` | `3` has no type |

This is the honest way to carry a gap. A comment goes stale in silence. A test
does not.

---

## 1.12 Why the printer needed the context

The first run of the test suite printed this:

```
_f0 → _f0
```

That was correct and useless. `Expr::pretty` has no local context, so it cannot
know that `_f0` is named `α`.

The cure splits the job. The term printer asks for the name, and the context
supplies it:

```rust
pub fn pretty_with(&self, fvar_name: &dyn Fn(FVarId) -> Option<String>) -> String
```

```rust
// on LocalContext
pub fn pretty(&self, e: &Expr) -> String {
    e.pretty_with(&|id| self.name_of(id).map(Name::to_string))
}
```

`TypeError::render(&ctx)` uses the same road. Use it and not `Display`, because a
message that says `_f0` helps nobody.

This is a small thing with a general lesson. The kernel holds no names, by
design. So the kernel cannot print a good message on its own. Whoever holds the
names must lend them back.

---

## 1.13 Exercises

1. `is_def_eq` calls `alpha_eq` before it calls `whnf`. Say why that order is
   faster, and name an input where the order makes no difference.
2. The `Lam` arm calls `infer_sort(binder_type)` and throws the level away. Why
   does it call it at all?
3. Remove the `whnf` call from the `App` arm. Which test fails, and why?
4. Write the de Bruijn form of the K combinator by hand, then compare with
   `the_k_combinator_checks`.
5. `is_def_eq` compares two `Forall` bodies directly, with no renumber. Say why
   that is correct.
6. `check` calls `infer_sort` on the expected type. Give a term that this call
   rejects and that `infer_type` alone would accept.
7. Why can the checker not type `3` yet, when `3` is just a number?

### Answers

1. `alpha_eq` is one structural walk and allocates nothing, while `whnf` clones
   and substitutes. In a real check most comparisons are between two terms that
   are already identical. For two terms that differ at the root, such as a
   `Sort` against a `Lam`, both orders fail at once.
2. To reject a binder whose type is not a type. `fun (x : hp) => x` where
   `hp : p` and `p : Prop` must fail. The test is
   `a_binder_whose_type_is_a_proof_fails`.
3. `the_result_type_depends_on_the_argument_value` still passes, but a function
   type that hides behind a redex breaks. For example apply `(fun x => x) f` to
   an argument. The `App` arm would see a `Lam` and not a `Forall`, so it would
   report `NotAFunction`.
4. `λ λ λ λ #1`, with binder types `Sort 0`, `Sort 0`, `#1`, `#1`.
5. Both bodies sit under exactly one binder, so index 0 means that binder in
   both terms and index `n+1` means the same outer binder in both. The index
   spaces are already aligned.
6. `check(ctx, hp, hp2)` where both are proofs. The expected type `hp2` is not a
   type, so `infer_sort` rejects it. `infer_type(hp)` alone succeeds.
7. `3` is `Expr::Lit`, and its type is the constant `Nat`. A constant needs a
   declaration, and a declaration needs an `Environment`. There is none yet.

---

## 1.14 What chapter 2 adds

| Piece | Unlocks |
|---|---|
| `Environment`, a map from `Name` to a declaration | the δ rule, and a type for every constant |
| `axiom`, `def`, and `theorem` declarations | named theorems that build on each other |
| `inductive` declarations and the recursor | the ι rule |
| the strict positivity check | soundness of an inductive declaration |
| level normalization | `max u 0` equals `u` |
| proof irrelevance and the η rule | the last two entries of section 1.11 |

With those, `∧`, `∨`, `∃`, `=`, `Nat`, and real mathematics become reachable.

---

## 1.15 References

- Chapter 0, sections 0.6 to 0.8 and 0.13, for the rules that this chapter runs.
- `crates/rean_kernel/src/typeck.rs`, `crates/rean_kernel/src/local.rs`.
- `crates/rean_kernel/tests/typeck.rs`, 27 tests.
- The Lean 4 source, `src/kernel/type_checker.cpp`.
