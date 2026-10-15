# Chapter 14 — What a checker must check

> **Where you are.** Chapter 14 of 28, in Part IV of [the guide](README.md).
>
> **Before this.** Part III, both chapters, and Part I chapter
> [7](book/07-inductive-types.md) for the recursor.
>
> **After it you can** say why a recursor is not an axiom, and what a checker
> must verify before it believes one.

Chapter 13 asked whether the checker handles what a beginner writes. This
chapter asks a harder question.

**Can a crafted input make our checker accept a lie?**

```sh
devbox run -- cargo test -p rean_kernel --test soundness
```

---

## 14.1 The answer was yes

Five probes against the checker of chapter 13:

```
bogus recursor accepted?              true
PROOF OF FALSE accepted?              true
undeclared universe param accepted?   true
duplicate replaced silently?          true
structure eta works?                  false
```

Row two is the one that matters. **Our checker accepted a proof of `False`.**

The input was eleven lines of Rust. Declare an inductive type `U` with one
constructor, then declare a **recursor** whose type is a lie:

```rust
let liar = RecursorVal {
    name: "U.rec",
    ty: Expr::arrow(u(), Expr::const_("False", vec![])),   // U → False
    // ...
};
```

No real recursor could have that type. But chapter 13's `check_declaration` did
this to a recursor and no more:

```rust
self.infer_sort(decl.ty())?;
```

It asked "is `U → False` a type?". It is. So the recursor went into the
environment, and then `U.rec U.u` has type `False`, and `theorem oops : False`
checked.

The lesson has a name. A recursor is **not** an axiom. An axiom asks to be
trusted and `#print axioms` reports it. A recursor claims to be **derived from
its inductive declaration**, and the kernel is supposed to verify that claim.
Skip the check and a file can smuggle an untracked axiom in, disguised as a
recursor.

---

## 14.2 Checking a recursor

Full re-derivation builds the recursor from the inductive declaration and
compares. That is a lot of code and easy to get subtly wrong. There is a
cheaper check that closes the hole, and it rests on one idea:

> An ι rule must deliver the type that the recursor's own type promises.

That is the property that makes ι sound. A rule that delivers a different type
lets you move a term into a type it does not inhabit, and from there anything
follows.

So `check_recursor` has two halves.

### Half one: shape

| Condition | Why |
|---|---|
| at least one motive | a recursor with no motive is not a recursor |
| one rule per constructor, and no more | a missing rule is a hole, an extra rule is a lie |
| the parameter and index counts agree with the inductive | else the argument positions do not line up |
| enough binders in the declared type | the ι rule reads positions out of it |

The liar of section 14.1 dies on the first row.

### Half two: every rule is type correct

For each constructor:

1. Open the recursor's parameters, motive and minor premises into fresh free
   variables. Call them the **prefix**.
2. Build the constructor applied to those parameters plus a fresh variable per
   field. That is the term the ι rule rewrites.
3. Read the **indices** off the type of that term.
4. Walk the rest of the recursor type, filling the index binders and the major
   premise binder. What remains is the type the recursor **promises**.
5. Apply the rule's right hand side to the prefix and the fields. Infer its
   type. That is what the rule **delivers**.
6. The two must be definitionally equal.

```rust
let got = self.infer_type(&delivered)?;
if !self.is_def_eq(&got, &promised)? {
    return Err(bad(format!(
        "the rule for `{}` delivers `{}` and the type promises `{}`", …
    )));
}
```

### One obstacle worth naming

A recursor's rules **call the recursor**. The ι rule for `Nat.succ` rewrites to
a term that calls `Nat.rec` again. So checking `Nat.rec` needs the type of
`Nat.rec`, and the environment does not hold it yet, because a declaration only
goes in after it checks.

The first attempt reported `unknown constant Nat.rec` on the fixture.

The cure is a field on the checker:

```rust
pub struct TypeChecker<'e> {
    env: &'e Environment,
    lctx: LocalContext,
    /// The declaration under check, if it refers to itself.
    pending: Option<Declaration>,
}
```

And a lookup that sees it:

```rust
fn lookup(&self, name: &Name) -> Option<&Declaration> {
    if let Some(pending) = &self.pending
        && pending.name() == name
    {
        return Some(pending);
    }
    self.env.get(name)
}
```

That is not a loophole. It makes the check ask exactly the right question: **are
these rules consistent with the type that this declaration claims?** It never
assumes the rules are correct, only that the type is the one on offer.

---

## 14.3 Large elimination out of `Prop`

A second hole, and a subtler one. A recursor can be perfectly type correct and
still be unsound, if it eliminates a `Prop` into a larger universe.

`Prop` carries no information beyond the fact that it holds. Let a two
constructor `Prop` eliminate into `Type` and you can read **which** constructor
a proof used. That breaks proof irrelevance, which the kernel relies on.

Two shapes are the exception, and Lean permits both:

| Shape | Example |
|---|---|
| no constructor at all | `False` |
| one constructor whose every field is itself a proof | `Eq`, `And` |

Those are the subsingletons. They have at most one element, so nothing can leak.

```rust
if self.is_subsingleton(ind)? { return Ok(()); }
// … the motive must land in Prop
```

This check is why `Eq.rec` in the fixture still passes: `Eq` has one
constructor with no field, so it is a subsingleton, so eliminating into
`Sort v` is allowed. A check that refused it would have been worse than no
check, and the fixture says it does not.

---

## 14.4 Universe hygiene, and one name per declaration

Two small checks with no subtlety.

**Every universe parameter must be declared.** A parameter that a type or a
value uses and the declaration does not list is a free universe variable, and a
free universe variable has no meaning:

```rust
let mut used = Vec::new();
decl.ty().collect_level_params(&mut used);
if let Some(value) = declaration_value(decl) { value.collect_level_params(&mut used); }
for param in used {
    if !declared.contains(&param) { return Err(UndeclaredUniverse { … }); }
}
```

A declaration must also not list one parameter twice.

**One name, one declaration.** A second declaration under one name could
shadow the first, so a proof checked against one meaning would be used with the
other:

```rust
if self.env.contains(decl.name()) {
    return Err(TypeError::DuplicateDeclaration(decl.name().clone()));
}
```

---

## 14.5 Eta for a structure

Not a soundness hole. The opposite: without it the checker **refuses valid
Lean**.

A structure has one constructor and no index, so its fields determine it.
Therefore `S.mk p.1 p.2` and `p` are the same term. Lean calls this eta for
structures, and a real file relies on it.

```rust
for index in 0..ctor.num_fields {
    let field = &args[(ctor.num_params + index) as usize];
    let projected = Expr::Proj(Proj { structure: ctor.induct.clone(), index, value: … });
    if !self.is_def_eq(field, &projected)? { return Ok(false); }
}
Ok(true)
```

Three guards keep it honest: one constructor, no index, and the other side must
belong to that same structure, else a projection of it has no meaning.

---

## 14.6 A failed declaration must not enter the environment

Closing the recursor hole in the kernel was only half the protection. The
harness of chapter 12 did this:

```rust
// Add it either way, so one failure does not cascade.
known.add(decl.clone());
```

The comment was about report quality and the effect was unsound. A bogus
declaration in the environment proves anything that names it. So the liar was
refused and then added anyway, and the proof of `False` still checked.

A checker must not do that. The harness now adds **only** a declaration that
checks, and reports three verdicts rather than two:

| Verdict | Meaning |
|---|---|
| `ok` | the kernel accepted it |
| `FAIL` | the kernel refused it |
| `block` | it was not checked, because it names something that failed |

The third one keeps the report readable without softening the verdict. A
blocked declaration is **not** proven. It is only not separately interesting.

```
level 1: checked 31 of 32 declarations (1 failed, 0 blocked)
```

---

## 14.7 A cautionary tale

Adding `pending` meant replacing `self.env.get(` with `self.lookup(` across the
checker. A single search and replace did it, and it also rewrote the body of
`lookup` itself:

```rust
fn lookup(&self, name: &Name) -> Option<&Declaration> {
    if let Some(pending) = &self.pending && pending.name() == name {
        return Some(pending);
    }
    self.lookup(name)      // was self.env.get(name)
}
```

Every call stack overflowed. The test suite reported it as
`thread has overflowed its stack` with no line number, and the first guess was
that eta for structures was looping. It was not.

Two lessons. A search and replace over a function's own call sites will hit its
definition. And the fastest way to localize an overflow is to split the failing
test until the harness names the smallest case.

The same replace also missed two call sites, because `rustfmt` had split them
over four lines and the pattern was written for one. The fixture reported
`unknown constant Nat.rec` until both were found.

---

## 14.8 So does it have full coverage as a checker?

**No.** Here is the whole inventory, honestly.

### Done

| Job | Where |
|---|---|
| the 11 term formers and the 5 level formers | chapter 0 |
| the type rules and the conversion rule | chapter 10 |
| β, ζ, δ, ι, η, proof irrelevance, projection | chapters 10 and 11 |
| K-like ι, quotient rules, `Nat` literal arithmetic | chapter 13 |
| strict positivity, for a plain inductive | chapter 13 |
| recursor shape and ι rule type correctness | **chapter 14** |
| no large elimination out of a non subsingleton `Prop` | **chapter 14** |
| universe parameter hygiene | **chapter 14** |
| one name per declaration | **chapter 14** |
| eta for a structure | **chapter 14** |
| a failed declaration stays out of the environment | **chapter 14** |

### Still missing, and what each would take

**Soundness.** Each of these is a way a crafted file could still lie.

| Gap | What it would take |
|---|---|
| nested inductive positivity | understand the auxiliary form Lean compiles a nested inductive into, then check that. `num_nested` is skipped today. |
| mutual inductive and mutual recursor | the recursor check steps aside when there is more than one motive or more than one type in the group. Generalising it means one motive per type and a rule per constructor of each. |
| full recursor re-derivation | build the motive, the minor premise per constructor with its induction hypotheses, and the ι rules, from the inductive declaration. Then compare. This subsumes the shape check and removes the last thing we take on faith. |
| the inductive universe constraint | an inductive's own `Sort` must be large enough for every constructor field. Unchecked. |
| `Quot`'s four types | the kernel should know them, not read them. We read them. |
| `unsafe` and `partial` | a safe declaration must not use an unsafe one. Unchecked. |
| axiom tracking | report which axioms a theorem rests on, as `#print axioms` does. Not a soundness check, a trust report. |

**Completeness.** Each of these makes the checker refuse or fail on valid Lean.

| Gap | What it would take |
|---|---|
| big number arithmetic | a big integer type in place of `u128`. A literal past the limit stays stuck today, which is safe and incomplete. |
| `String` literal operations | the same treatment `Nat` got in chapter 13 |
| a full level normal form | sort and flatten nested `max`, and handle `imax` with an open right side |
| `MData` | a twelfth `Expr` variant. The reader drops the annotation today, which is sound. |

### The honest summary

The checker is now hard to lie to in the ways a plain file can lie. It is not
yet hard to lie to in the ways a **mutual or nested** declaration can lie, and
it still takes the recursor's shape on faith even while checking its rules.

Two numbers say it best:

```
level 1   32 of 32 declarations of a real Lean module
soundness 16 red team tests, every one of which once passed a lie
```

The second number is the one to grow.

---

## 14.9 Exercises

1. A recursor is not an axiom. Say precisely what the difference is, in terms
   of what the kernel must verify.
2. `pending` lets a declaration see itself. Explain why that is not a
   loophole, and give the question the check actually asks.
3. Why does the elimination universe check have to run before the ι rules are
   checked?
4. The harness used to add a failed declaration "so one failure does not
   cascade". Give the proof of `False` that comment allowed.
5. `is_subsingleton` returns `true` for an inductive with no constructor. Why
   is large elimination out of `False` sound?
6. Our recursor check verifies that each rule is type correct. Name a lie it
   still cannot catch.

### Answers

1. An axiom asks to be trusted, and a tool reports it. A recursor claims to
   follow from its inductive declaration, so the kernel must check that claim.
   An unchecked recursor is an axiom that no tool reports.
2. The check never assumes the rules are right. It assumes only the type that
   the declaration offers, and then asks: are these rules consistent with that
   type? A rule that disagrees is refused, so a lie in the rules cannot pass.
   A lie in the type is caught by the shape check and by the ι rule types.
3. Because a large eliminator can be perfectly type correct. Its rules will
   check out, so only a separate universe check can refuse it.
4. Declare a recursor whose type is `U → False`. It fails the check and gets
   added anyway. Then `theorem oops : False := U.rec U.u` checks, because
   `infer_type` reads the recursor's declared type out of the environment.
5. `False` has no element at all, so there is no proof to inspect and nothing
   to leak. Anything you build from a proof of `False` is unreachable.
6. A recursor for a **mutual** inductive group, or one for a nested inductive.
   The check steps aside for both. It also cannot catch a motive or minor
   premise shape that is type correct but not the one induction requires,
   because it does not re-derive them.

---

## 14.10 How other systems do it

This chapter exists because our environment comes from a **file**. The file
hands us a recursor and claims it follows from an inductive declaration, and
section 14.1 shows what happens when nobody checks the claim.

- **Lean's kernel never reads a recursor from anywhere.** It takes the
  inductive declaration and **derives** the recursor itself, in
  `src/kernel/inductive.cpp`. So the question of this chapter cannot come up
  there. Any checker that reads an export file has to answer it, and the
  cheapest sound answer is the one in section 14.2: every ι rule must deliver
  the type that the recursor promises.
- **Rocq has no recursor to check.** Its kernel checks a `match` and a `fix`,
  and a guard condition carries the weight that a recursor carries in Lean.
  Different rule, same job: make sure the recursion cannot run for ever.
- **Large elimination has another name.** Section 6.3 refuses to eliminate a
  `Prop` into a larger sort unless the type is a subsingleton. Rocq calls the
  permitted case singleton elimination, and the rule is the same shape.
- **A duplicate universe parameter is a real attack.** Section 6.4 is not a
  tidy-up. A name that appears twice in a level list lets a term be read two
  ways, and a checker that accepts it has no fixed meaning for the term.

## 14.11 References

**Our code**

- `crates/rean_kernel/src/typeck.rs`, the method `check_recursor`
- `crates/rean_kernel/tests/soundness.rs`, the red team, every probe a test
- `crates/rean_kernel/src/environment.rs`, which refuses a duplicate name

**Lean's own source**

- `src/kernel/inductive.cpp`, where Lean builds the recursor and its rules, and
  where the universe rules for elimination live
- `src/kernel/declaration.h`, which shows what a recursor carries

**Read more**

- Pfenning and Paulin-Mohring, *Inductively defined types in the Calculus of
  Constructions*, 1990, for what an ι rule must deliver.
  DOI [10.1007/BFb0040259](https://doi.org/10.1007/BFb0040259)
- Rocq, inductive types, for `match`, `fix` and the guard condition.
  <https://rocq-prover.org/doc/master/refman/language/core/inductive.html>
- Carneiro, *Lean4Lean*, 2024, for the recursor rules proved rather than
  tested. <https://arxiv.org/abs/2403.14064>
- The Lean Kernel Arena, which runs a suite of invalid proofs that every
  checker must refuse. <https://arena.lean-lang.org/>

---

**Next:** [What a theorem rests on](15-what-a-theorem-rests-on.md)
