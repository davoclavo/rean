# Chapter 2 — The environment and the five equations

Chapter 1 could check a term but it could not **name** one. Nothing had a type
unless the local context held it, so `Nat` was an error and `3` had no type.

This chapter adds the environment. That one addition unlocks four of the five
reduction equations, plus proof irrelevance and projections.

```sh
devbox run -- cargo test -p rean_kernel
```

---

## 2.1 Why the free functions became a struct

Chapter 1 had three free functions. Now they all need the environment, and they
call each other, so threading two parameters through every call would be noise.

```rust
pub struct TypeChecker<'e> {
    env: &'e Environment,
    lctx: LocalContext,
}
```

The real Lean kernel does the same thing, for the same reason.

```rust
let env = Environment::new();
let mut tc = TypeChecker::new(&env);
tc.infer_type(&proof)?;
```

Two signatures changed shape as well. `whnf` and `is_def_eq` now return a
`Result`, because proof irrelevance calls `infer_type`, and that can fail.

---

## 2.2 The environment

A map from [`Name`] to one of eight declarations.

| Kind | Carries | Gives the kernel |
|---|---|---|
| `Axiom` | a type | nothing. The kernel trusts it. |
| `Definition` | a type and a value | the δ rule |
| `Theorem` | the same, and the value is a proof | the δ rule |
| `Opaque` | a type and a value | **no** δ. That is the point of `opaque`. |
| `Quot` | a type and one of four kinds | the quotient rules, not written yet |
| `Inductive` | constructors, and the parameter counts | a type to case on |
| `Constructor` | its inductive, its index, its field count | a target for ι |
| `Recursor` | its rules, each with a right hand side | the ι rule |

Note `Opaque`. It has a value and `unfoldable_value` returns `None` for it. A
reader of the code should see that asymmetry and ask why, so the method says so.

The field names follow the `lean4export` format on purpose. Chapter 3 reads a
real Lean file straight into these structs with no translation layer.

---

## 2.3 δ: a definition unfolds

```rust
if let Some(decl) = self.env.get(name)
    && let Some(value) = decl.unfoldable_value()
{
    let value = value.instantiate_levels(decl.level_params(), levels);
    return Ok(Some(value.apps(args)));
}
```

The second line is the part that is easy to forget. A polymorphic definition
stores its value with a universe **parameter** in it:

```lean
def Alias.{u} : Sort (u+2) := Sort (u+1)
```

The call site writes `Alias.{0}`, so the stored value must take that `0` before
anybody uses it. `Expr::instantiate_levels` and `Level::substitute` do that.

Forget it and the checker reports a universe mismatch on every polymorphic
definition. The test is `delta_substitutes_the_universe_arguments`.

---

## 2.4 ι: a recursor meets a constructor

This is the largest new rule. It needs the argument layout to be exact:

```text
rec  <params>  <motives>  <minors>  <indices>  <major>
```

So the **major premise**, the term that the recursor takes apart, sits at

```rust
num_params + num_motives + num_minors + num_indices
```

Two real examples from the fixture:

| Recursor | params | motives | minors | indices | major at |
|---|---|---|---|---|---|
| `Nat.rec` | 0 | 1 | 2 | 0 | 3 |
| `Eq.rec` | 2 | 1 | 1 | 1 | 5 |

The algorithm:

1. The head must be a `Const` whose declaration is a `Recursor`.
2. There must be more arguments than `major_index`.
3. Reduce the major premise. Its head must be a `Const` that is a
   `Constructor`.
4. Find the rule for that constructor. No rule means no reduction.
5. Build the result in four steps.

Step 5 is where an error is silent and fatal, so here it is in full:

```rust
let mut out = rule.rhs.instantiate_levels(&rec.level_params, levels);
out = out.apps(args[..rec.num_prefix()].iter().cloned());        // params, motives, minors
out = out.apps(fields.iter().cloned());                          // the constructor fields
out = out.apps(args[major_index + 1..].iter().cloned());         // anything after the major
```

The fields are the **last** `num_fields` arguments of the constructor
application, not the first. The parameters come first in a constructor, and they
are not fields.

If the major premise is a free variable, no rule applies and the term stays
stuck. That is correct, and the test is `iota_waits_for_a_constructor`.

---

## 2.5 Projections

Two separate jobs, and both are needed.

### Reduce a projection

```rust
let slot = ctor.num_params as usize + proj.index as usize;
Ok(args.get(slot).map(|field| (*field).clone()))
```

Again the parameters come first, so the field index needs that offset.

### Infer the type of a projection

Harder, because a later field may mention an earlier one. The type of `.2` can
speak about `.1`. So:

1. Infer the type of the term, reduce it, and split off the parameters.
2. Take the single constructor of that inductive type.
3. Fill its parameters from the type of the term.
4. For each **earlier** field, substitute a projection of the same term.
5. The binder type that remains is the answer.

Step 4 is the trick. The code builds `Expr::Proj { index, value }` for each
earlier field and substitutes it in.

---

## 2.6 η

```rust
fn eta_eq(&mut self, lam: &Expr, other: &Expr) -> TypeResult<bool> {
    let Expr::Lam { binder_name, binder_type, body, .. } = lam else { return Ok(false) };
    if matches!(other, Expr::Lam { .. }) { return Ok(false) }
    // Open the binder, then compare `body` with `other x`.
    let id = self.lctx.push(binder_name.clone(), (**binder_type).clone());
    let opened = body.instantiate(&Expr::FVar(id));
    let applied = other.clone().app(Expr::FVar(id));
    let same = self.is_def_eq(&opened, &applied);
    self.lctx.pop();
    same
}
```

`fun x => f x` and `f` are the same function. `is_def_eq` tries it in both
directions, since either side may be the lambda.

### Why it opens the binder

The first version of this method stayed in de Bruijn:

```rust
let applied = other.lift(0, 1).app(Expr::bvar(0));
self.is_def_eq(body, &applied)
```

That is correct about the shapes, and it leaves **both sides open**. So nothing
inside the comparison can ask for a type, and proof irrelevance needs a type.

It cost a real theorem. `Option.pbind_join` of the Lean prelude is eta on a
dependent function whose second argument matches **only** because all proofs of
one proposition are equal. With both sides open, proof irrelevance declined and
a correct term was refused.

This is the third time the same lesson has come up in this project, and it is
worth saying once more. **A free variable is not only an optimisation. It is
what keeps a term closed, and a closed term is what lets a later step ask for
its type.** Section 2.7 found it first.

---

## 2.7 Proof irrelevance, and a bug it exposed

```rust
if a.has_loose_bvars() || b.has_loose_bvars() { return Ok(false) }
let type_a = self.infer_type(a)?;
let sort = self.infer_type(&type_a)?;
let Expr::Sort(level) = self.whnf(&sort)? else { return Ok(false) };
if !level.normalize().is_zero() { return Ok(false) }
let type_b = self.infer_type(b)?;
self.is_def_eq(&type_a, &type_b)
```

Note the **two** `infer_type` calls before the test. The type of `a` is a
proposition `P`, and the question is whether `P` itself lives in `Sort 0`.

### The bug

Chapter 1 compared two binder bodies directly:

```rust
// chapter 1, and wrong once proof irrelevance exists
if self.is_def_eq(t1, t2)? && self.is_def_eq(b1, b2)? { ... }
```

That works for a purely structural comparison. Both bodies sit under one binder
each, so the two index spaces line up with no renumber. Chapter 1 even called
that a de Bruijn dividend.

But each body still holds a **loose** bound variable. Proof irrelevance calls
`infer_type`, and a loose bound variable has no type. So the moment proof
irrelevance arrived, a test that had passed for a whole chapter started
reporting `the bound variable #2 points outside the term`.

The cure is to open both bodies with **one shared** free variable:

```rust
let id = self.lctx.push(name.clone(), (**left_type).clone());
let left = left_body.instantiate(&Expr::FVar(id));
let right = right_body.instantiate(&Expr::FVar(id));
let same = self.is_def_eq(&left, &right);
self.lctx.pop();
```

Now everything inside the comparison is closed, so anything inside it may infer
a type. The guard on `has_loose_bvars` stays as a second line of defence.

The lesson generalises. **A free variable is not only an optimisation.** It is
what makes a term closed, and a closed term is what lets any later stage ask
for its type.

---

## 2.8 Level normalization

`is_def_eq` compares two universe levels often, and two different shapes can
mean one level. `Level::normalize` applies three rules:

| Input | Output | Why |
|---|---|---|
| `max u u`, `max u 0`, `max 0 u` | `u` | `0` is the floor |
| `imax u 0` | `0` | the special case that makes `Prop` impredicative |
| `imax u (v+1)` | `max u (v+1)` | a successor is never `0` |

This is weaker than the real Lean normal form, and the doc comment says so. A
harder pair of open levels can still fail to match.

---

## 2.9 `check_declaration`

The entry point of a proof checker over a whole module:

```rust
pub fn check_declaration(&mut self, decl: &Declaration) -> TypeResult<()> {
    self.infer_sort(decl.ty())?;              // the type must be a type
    if let Some(value) = /* def, theorem, or opaque */ {
        let got = self.infer_type(value)?;
        if !self.is_def_eq(&got, decl.ty())? { /* mismatch */ }
    }
    Ok(())
}
```

Note that an `Opaque` value **is** checked here, even though δ will not unfold
it. Opacity hides a value from reduction. It does not excuse it from being
correct.

One rule for the caller. Build the environment **one declaration at a time**,
and check each one against only the declarations before it. Add everything first
and a circular definition could prove itself.

---

## 2.10 Where the five equations stand

| Rule | Status |
|---|---|
| β beta | done in chapter 1 |
| ζ zeta | done in chapter 1 |
| δ delta | **done** |
| ι iota | **done** |
| η eta | **done** |
| proof irrelevance | **done** |
| projection of a constructor | **done** |

Still missing, and each is honest in the module documentation:

| Missing | Effect |
|---|---|
| K-like ι reduction | `Eq.rec` reduces only when its major premise is already `Eq.refl` |
| the strict positivity check | a bad `inductive` is trusted, not rejected |
| recursor re-derivation | the recursor and its ι rules are trusted as given |
| a full level normal form | a hard pair of open levels can fail to match |
| the quotient rules | `Quot` is stored and never computed |

The last three are what separates a useful checker from a trustworthy one. See
chapter 3, section 3.8.

---

## 2.11 Exercises

1. `unfoldable_value` returns `None` for `Opaque`, but `check_declaration` still
   checks its value. Explain both.
2. Delete the `instantiate_levels` call in the δ rule. Which test fails?
3. In the ι rule, take the **first** `num_fields` arguments of the constructor
   instead of the last. Give an example that breaks.
4. Why does `proof_irrelevant` call `infer_type` twice?
5. `binders_eq` pushes one free variable and uses it for both bodies. What goes
   wrong with two different free variables?
6. `whnf` has a step budget. The theory says reduction terminates, so why?

### Answers

1. δ must not unfold an opaque value, because a caller asked for it to stay
   hidden. But the value still has to have the declared type, else the
   declaration is a lie.
2. `delta_substitutes_the_universe_arguments`.
3. A constructor takes its parameters first. `PProd.mk α β a b` has 2
   parameters and 2 fields, so the first two arguments are `α` and `β`, not the
   data.
4. The first call gives the type `P` of the term. The second asks where `P`
   lives. Proof irrelevance applies only when `P : Sort 0`.
5. The two bodies would then speak about two different variables, so a body that
   uses its binder could never match. One shared variable is what makes the
   comparison meaningful.
6. A corrupt input file does not have to obey the theory. The budget turns an
   infinite loop into an error message.
