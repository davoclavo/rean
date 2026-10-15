# Chapter 10 — The type checker

> **Where you are.** Chapter 10 of 28, and the first of Part II in
> [the guide](README.md).
>
> **Before this.** [Part I](book/README.md), all eight chapters. This chapter
> is Part I chapters 6 and 8, turned into code.
>
> **After it you can** read `infer_type` one arm at a time, and name the rule
> each arm implements.

Part I wrote five rules on one page. This chapter turns them into four pieces
of code, and then checks a real proof with them.

The checker here needs no environment, no inductive type and no library. It
can already check every proof of implicational logic, which is every theorem
you can state with `→` and `∀` alone.

Run it:

```sh
devbox run -- cargo run -p rean -- prove
devbox run -- cargo test -p rean_kernel --test typeck
```

Every claim here has a test in `crates/rean_kernel/tests/typeck.rs`.

---

## 10.1 The goal

One line. Does this proof prove this proposition?

```
fun (α : Prop) (h : α) => h        against        (α : Prop) → α → α
```

In words: "for every proposition `α`, if `α` holds then `α` holds". The proof is
the identity function.

The output of `rean prove`:

```
== the proof ==
fun (α : Prop) => fun (h : α) => h

== the proposition ==
(α : Prop) → α → α

== infer_type ==
the proof has type : (α : Prop) → α → α

== check ==
accepted. The proposition holds.
the proposition lives in : Prop
```

Read the last line. The proposition itself lives in `Prop`, not in `Type`. That
is `imax 1 0 = 0` from Part I chapter 5, section 5.4, and now a running program
computes it.

---

## 10.2 The four pieces

| Piece | File | Job |
|---|---|---|
| [`alpha_eq`](GLOSSARY.md#alpha-equivalence) | `crates/rean_kernel/src/expr.rs` | compare two terms, and skip the binder name |
| [`LocalContext`](GLOSSARY.md#local-context) | `crates/rean_kernel/src/local.rs` | hold `Γ`, and open a binder |
| [`whnf`](GLOSSARY.md#whnf) and [`is_def_eq`](GLOSSARY.md#is-def-eq) | `crates/rean_kernel/src/typeck.rs` | the relation [`≡`](GLOSSARY.md#definitional-equality) |
| [`infer_type`](GLOSSARY.md#infer-type) | `crates/rean_kernel/src/typeck.rs` | the [judgment](GLOSSARY.md#judgment) `Γ ⊢ e : A` |

At the end of this chapter they **were** 381 lines of code, inside 619 lines of
file. That was the whole trusted core here. My earlier estimate was 250 lines,
and the extra 130 were the error type and its messages.

The past tense is the point. The finished kernel crate is **4,115 lines of code
inside 5,864 lines of file**, and every one of those lines is trusted. The rules
account for part of that growth and the cost accounts for the rest. A checker
that reads the whole Lean prelude is not a 250-line program, and anybody who
says otherwise has not read one.

---

## 10.3 `alpha_eq`: why `==` is not enough

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

## 10.4 `LocalContext`: opening a binder

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

`instantiate` and `abstract_fvar` are the pair from Part I chapter 3, section 3.6. This
is what they were for.

Two properties matter:

- **An identifier never repeats.** A push after a pop gives a new number. So a
  stale `FVarId` cannot silently match a live one. The test is
  `an_identifier_never_repeats`.
- **`with_binder` cannot leak.** It pops even when the closure returns an error.
  The test is `the_context_is_clean_after_an_error`.

---

## 10.5 `whnf`: reduce the head

The name is short for weak head normal form:

- **Weak** means the function does not look inside a binder.
- **Head** means it only reduces the outermost shape, and leaves the arguments
  alone.

This version uses two of the seven rules of Part I chapter 8, section 8.2:

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
`an_empty_environment_does_not_unfold_a_constant` records that, and it still
passes: δ needs an environment, and chapter 11 is where one arrives.

---

## 10.6 `is_def_eq`: the same by computation

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

## 10.7 `infer_type`: one arm per rule

Each arm of the `match` is one rule of Part I chapter 6, section 6.3.

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
level up. This is the Curry-Howard idea of Part I chapter 1, section 1.4, written as
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

## 10.8 The worked check, step by step

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
Part I chapter 5, section 5.3, and the checker now relies on it.

Step 8 is where `alpha_eq` earns its place. The inferred type and the target
agree in every field except the binder name, and `==` would reject it.

---

## 10.9 What the checker can prove now

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

## 10.10 The errors

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
of Part I chapter 4, section 4.3 at work in the printer.

---

## 10.11 The gaps, and the test that records each one

Each gap was a test that asserted the **wrong** answer on purpose. When chapter
2 closed the gap, the test failed, and that was the reminder to flip it.

| Gap | What chapter 11 closed it with |
|---|---|
| the δ rule | `a_definition_unfolds_to_its_value` |
| proof irrelevance | `proof_irrelevance_makes_two_proofs_equal` |
| the η rule | `eta_makes_a_wrapper_equal_to_the_function` |
| constants | `delta_substitutes_the_universe_arguments` |
| literals | `a_nat_literal_has_type_nat`, `a_string_literal_has_type_string` |

One gap of this chapter is still real, and its test still passes:
`an_empty_environment_does_not_unfold_a_constant`. δ needs an environment.

### A citation rots in silence, so a tool reads them

Here is the rule this chapter was written on:

> A comment goes stale in silence. A test does not.

True, and not enough. A test that records a gap is **deleted** when the gap
closes, which is the right thing to do with it. The table above went on naming
five deleted tests, and nothing noticed, because nothing checked that a
chapter's citation still resolves.

So a stale **citation** goes stale in silence, even when every test is live. The
rule needed a tool, and now it has one:

```sh
python3 tools/cite.py
```

It checks two kinds of citation, because both rot the same way and neither is
visible:

- a **name** in backticks must be a `fn` or a `def` somewhere in the code;
- a **section** a document points at, as "chapter 18, section 18.6" or as `§18.6`,
  must be a heading of that chapter.

`devbox run check` runs it, so a chapter that names a test nobody wrote, or a
section somebody renumbered, now fails the gate.

It found six stale citations the day it was written, in this chapter. Every
chapter you read after this one is held to the same gate, and so is Part I.

---

## 10.12 How other systems do it

The four pieces of section 10.2 are not our invention. Every checker for a
dependent type theory has them, under the same names or close ones.

| Our name | Lean's name, and where | What differs |
|---|---|---|
| `alpha_eq` | `src/kernel/expr_eq_fn.cpp` | Lean compares a pointer first, and caches the answer |
| `LocalContext` | `src/kernel/local_ctx.cpp` | the same idea: open a binder into a free variable |
| `whnf` | `whnf` and `whnf_core`, in `src/kernel/type_checker.cpp` | Lean separates the cheap core from the part that unfolds a definition |
| `is_def_eq` | `is_def_eq_core`, in the same file | Lean asks a cheap question first, and chapter 21 is us learning that |
| `infer_type` | `infer_type_core`, in the same file | Lean takes a flag, so it can skip a check it has already done |

Four notes for a reader who knows another language.

- **The shape of the algorithm is old.** Reduce the head, then compare the
  parts. Coquand wrote it down in 1996 and it has not changed much since.
- **Infer, or check against a type.** Our `check` infers and then compares.
  A larger elaborator does better: it pushes the expected type inward and uses
  it. The name for that is bidirectional typing.
- **Agda and Idris do not substitute.** They build a closure, which is a term
  plus an environment, and they reduce that. A later chapter,
  [what the others do](23-what-the-others-do.md), meets the same idea again, as
  normalisation by evaluation, in the fastest Lean checker in the arena.
- **Rust needs none of this.** A Rust type cannot hold a value, so `rustc`
  never reduces a function call to decide whether two types are equal. The
  nearest thing it has is the normalisation of a type alias and of an
  associated type. The conversion rule of Part I chapter 8, section 8.1 is what makes
  a dependent checker a different animal.

## 10.13 References

**Our code**

- `crates/rean_kernel/src/typeck.rs`, `expr.rs`, `local.rs`
- `crates/rean_kernel/tests/typeck.rs`, every claim of this chapter
- `tools/cite.py`, the gate that section 10.11 describes

**Lean's own source**

- `src/kernel/type_checker.cpp`, the same five functions, in 1,300 lines
- `src/kernel/local_ctx.cpp`, the local context
- `src/kernel/expr_eq_fn.cpp`, alpha equivalence with a cache

**Read more**

- Coquand, *An algorithm for type-checking dependent types*, 1996. The shape of
  section 10.6. DOI [10.1016/0167-6423(95)00021-6](https://doi.org/10.1016/0167-6423%2895%2900021-6)
- Abel, Öhman and Vezzosi, *Decidability of conversion for type theory in type
  theory*, 2018, for why the comparison ends.
  DOI [10.1145/3158111](https://doi.org/10.1145/3158111)
- Dunfield and Krishnaswami, *Bidirectional typing*, 2021, for the method this
  chapter does not use yet.
  DOI [10.1145/3450952](https://doi.org/10.1145/3450952)
- Carneiro, *The Type Theory of Lean*, for the rule behind each arm of
  section 10.7. <https://github.com/digama0/lean-type-theory>

---

**Next:** [The environment and the five equations](11-the-environment.md)
