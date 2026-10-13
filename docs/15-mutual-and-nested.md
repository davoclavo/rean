# Chapter 15 — Mutual and nested

> **Where you are.** Chapter 15 of 28, in Part IV of [the guide](README.md).
>
> **Before this.** The two chapters before it, and
> Part I chapter [6](book/06-inductive-types.md), section 6.8, which shows both
> shapes.
>
> **After it you can** check a group of inductive types that refer to each
> other, and say why a nested type gets a weaker rule.

Two shapes of inductive declaration step past every check so far: a **mutual**
group, and a **nested** type. Part I chapter 6, section 6.8 shows both of them.

This chapter checks them. It closes two gaps of three, and it finds one bug on
the way.

```sh
devbox run -- cargo test -p rean_kernel --test soundness
```

---

## 15.1 A mutual group has one motive per type

For a group declared together

```lean
mutual
  inductive A | mkA : B → A
  inductive B | mkB : A → B
end
```

each recursor takes **one motive per type in the group**, and **one minor
premise per constructor of every type**. The induction is simultaneous, so
`A.rec` needs to know what to do with a `B` as well.

```text
A.rec : {motiveA : A → Sort u} → {motiveB : B → Sort u}
      → ((b : B) → motiveB b → motiveA (A.mkA b))
      → ((a : A) → motiveA a → motiveB (B.mkB a))
      → (t : A) → motiveA t
```

Three counts follow, and the checker now wants all three:

| Count | Value |
|---|---|
| motives | the number of types in the group |
| minor premises | the constructors of **every** type in the group |
| ι rules | the constructors of the **one** type it takes apart |

That last row is the asymmetry. Only the target's constructors can be the major
premise, so only they have rules.

### Which type does it take apart?

`A.rec` eliminates `A`. The checker could read that off the name, and it does
not. It reads it off the **rules**:

```rust
let Some(Declaration::Constructor(owner)) = self.lookup(&first.ctor) else { … };
let target_name = owner.induct.clone();
let Some(index) = group.iter().position(|i| i.name == target_name) else {
    return Err(bad(format!(
        "its rules are for `{target_name}`, which is not in its own group"
    )));
};
```

No naming convention, and a recursor whose rules leave its own group is refused
rather than misread.

### The ordering matters, and only a derivation sees it

Give the two minor premises in the wrong order and each one is still perfectly
type correct on its own. The ι rule still delivers what the type promises. Every
check before chapter 14 passes.

The derived premise does not. It knows that the premise at slot 0 belongs to the
first constructor of the first type in the group, so a swap is a mismatch and
the message says what induction needed instead.

### One caveat, stated plainly

The fixture has no mutual inductive, so **this ordering is unvalidated against
real Lean**. It is our reading of the shape, written down and tested for self
consistency. A mutual fixture is the next thing to get. See
`fixtures/lean4export/PROVENANCE.md`.

---

## 15.2 A group must be checked together

Writing the mutual test found a real bug.

`A.rec`'s rule for `A.mkA` rewrites to a term that calls **`B.rec`**, because
the field it takes apart is a `B`. And `B.rec`'s rule calls `A.rec`. So neither
recursor is in the environment when the other is checked.

Chapter 13 solved the single case with a `pending` slot holding the declaration
under check. A mutual group needs more than one, so `pending` became a list:

```rust
pub fn with_group<R>(&mut self, group: &[Declaration], body: impl FnOnce(&mut Self) -> R) -> R
```

The group is visible to its own members and **is not** added to the
environment. A test holds that line:

```rust
assert!(inside, "a member of the group must be visible inside it");
assert!(outside.is_err(), "the group must not leak into the environment");
```

The export format already groups a mutual declaration onto one line, with its
types, its constructors and its recursors together. That is exactly why. So the
reader now records the grouping:

```rust
/// The declarations of each line, grouped.
pub groups: Vec<Vec<Name>>,
```

and the driver walks a group at a time.

### A second bug the same work found

Removing the single `pending` slot changed the order of the shape checks, and
three existing tests failed. Two were message changes. The third was real:

```rust
let Some(first) = rec.rules.first() else {
    return Ok(());          // a recursor with NO rules passed silently
};
```

A recursor with no rule computes nothing. That is honest only for a type with no
constructor, such as `False`. Now:

```rust
if !only.ctors.is_empty() {
    return Err(bad(format!(
        "it has no rules and `{}` has {} constructors", only.name, only.ctors.len()
    )));
}
```

A test suite that only ever goes green teaches you nothing. This one went red
and pointed at a hole.

---

## 15.3 A nested inductive gets a weaker rule, not a free pass

Chapter 12 **skipped** positivity for a nested declaration. A skip is a free
pass, and a free pass on positivity is a way to prove `False`.

The reason for the skip is real. A nested inductive puts its own type inside
another type constructor:

```lean
inductive Tree | node : List Tree → Tree
```

`Tree` is an **argument** of `List`, not the head, so the strict rule of
chapter 12 refuses it. Lean handles the case by compiling the declaration into an
auxiliary non nested one, and we do not do that.

So a nested declaration now gets a weaker rule instead of nothing:

```rust
pub fn no_negative_occurrence(e: &Expr, names: &[Name]) -> bool {
    // Read `e` as a chain of binders. No domain may mention the name.
    // The result may.
}
```

| Shape | Strict rule | Nested rule |
|---|---|---|
| `Nat → Tree` | accept | accept |
| `List Tree → Tree` | **refuse** | accept |
| `(Tree → False) → Tree` | refuse | **refuse** |

The third row is the one that matters. That is the shape that proves `False`
directly, and it is still refused.

### Two limits, named

1. The check reads the declaration as written. It does not understand the
   auxiliary form Lean builds, so it is weaker than Lean's.
2. An abbreviation can hide a negative occurrence. If `Bad X` unfolds to
   `X → False`, then `Bad Tree` looks clean and is not. The check is syntactic
   and does not unfold.

Both are in the module documentation, next to the code. A weaker rule that says
so beats a skip that does not.

---

## 15.4 A field must fit inside its own type

An inductive type declares a `Sort`. A constructor field has a `Sort` of its
own. If a field were larger, the type would hold something bigger than itself,
and that is the shape of Russell's paradox.

```lean
inductive Small : Type | mk : Type → Small     -- refused
```

`Type` lives in `Type 1`, and `Small` only reaches `Type 0`.

`Prop` is the exception, because `Prop` is impredicative. A proposition may
quantify over anything. That is Part I chapter 4, section 4.4, showing up as a check.

### The order on levels

Comparing two universe levels is only partly decidable, and a check that refused
what it did not understand would refuse correct Lean. So `Level::is_leq` returns
`Option<bool>`, and the caller accepts on `None`:

```rust
pub fn is_leq(&self, other: &Level) -> Option<bool>
```

| Rule | Example |
|---|---|
| two closed levels compare by value | `1 ≤ 2` |
| the same level | `u ≤ u` |
| `u+1 ≤ v+1` when `u ≤ v` | |
| one branch of a `max` on the right is enough | `u ≤ max u v` |
| every branch of a `max` on the left must fit | `max u v ≤ max u v` |
| room to spare on the right | `u ≤ u+1` |

It only ever answers `Some(false)` for two closed numbers. So it refuses a lie
it is certain about and never a program it does not follow.

### The evidence it is right

The fixture is the test. `PProd.{u,v} : Sort u → Sort v → Sort (max u v)` needs
`u ≤ max u v`. `HAdd` needs a successor pushed through a nested `max`. Both pass,
and the module still checks 32 of 32.

---

## 15.5 Where the checker stands

| Job | Status |
|---|---|
| every reduction rule | chapters 9, 10, 12 |
| strict positivity, plain inductive | chapter 12 |
| recursor shape and ι rule types | chapter 13 |
| large elimination, universe hygiene, duplicates, structure eta | chapter 13 |
| derived minor premises, axiom trust report, unsafe isolation | chapter 14 |
| **mutual groups: motives, premises, ordering, and group visibility** | **chapter 15** |
| **nested positivity, with a weaker rule** | **chapter 15** |
| **the inductive universe constraint** | **chapter 15** |

### Still missing

| Gap | Kind | What it would take |
|---|---|---|
| full recursor re-derivation | soundness | derive the motive and the recursor type as well, not only the premises |
| nested, as Lean does it | soundness | understand the auxiliary form, and unfold before checking positivity |
| `Quot`'s four types | soundness | the kernel should know them. We have no fixture with a `Quot`, and a hand written type we cannot validate is a liability. |
| a mutual fixture | **validation** | the ordering of chapter 15 is untested against real Lean |
| big number arithmetic | completeness | a big integer in place of `u128` |
| `String` literal operations | completeness | the same treatment `Nat` got |
| a full level normal form | completeness | sort and flatten nested `max` |
| `MData` | completeness | a twelfth `Expr` variant |

```
level 1   32 of 32 declarations of a real Lean module
soundness 38 red team tests, every one of which once accepted a lie
trust     every axiom reported, by name
```

The first number cannot grow without a bigger fixture. The second can always
grow, and it is the honest measure of a checker.

---

## 15.6 Exercises

1. `A.rec` has a minor premise for `B.mkB`, and no ι rule for it. Say why.
2. The checker reads the eliminated type off the rules and not off the name.
   Give a file where the two disagree.
3. Swap two minor premises of a mutual recursor. Every check before chapter 14
   passes. Say precisely which one refuses it and why the others cannot.
4. `with_group` makes a group visible without adding it to the environment.
   What breaks if it adds it?
5. `no_negative_occurrence` accepts `List Tree → Tree`. Give a declaration it
   accepts that Lean would refuse.
6. `Level::is_leq` returns `None` for `u ≤ v`. Why is accepting the right
   response, and what does it cost?

### Answers

1. A minor premise says what to do with a `B`, and `A.rec` needs that because
   the induction is simultaneous. An ι rule fires when the major premise is a
   constructor application, and the major premise of `A.rec` is an `A`. A
   `B.mkB` can never be in that position.
2. A file that declares `Foo.rec` whose rules are all for constructors of
   `Bar`. Reading the name gives `Foo` and reading the rules gives `Bar`. The
   checker refuses it when `Bar` is not in the group, and that is the right
   answer either way.
3. `check_minor_premises`, by deriving the premise that each constructor needs
   and comparing. The others cannot, because each premise is well formed, each
   ι rule still delivers the type the recursor promises, and the counts are
   unchanged. Nothing local is wrong. Only the correspondence is.
4. The duplicate check would fire, because the declaration under check would
   already be in the environment. Worse, a member that failed would stay in,
   and a bogus declaration in the environment proves anything that uses it.
5. `Bad Tree → Tree`, where `def Bad X := X → False`. The field has no
   syntactic occurrence of `Tree` in a domain, and after δ it has one. Our
   check does not unfold.
6. Because a checker that refuses what it does not understand refuses correct
   Lean, and a false refusal is as useless as a false acceptance. The cost is
   that a crafted declaration with two unrelated open levels can hide a field
   that is too large.

---

## 15.7 How other systems do it

A nested inductive type is the hard case, and the three systems answer it in
three ways.

- **Lean turns a nested type into a mutual one.** The frontend builds an
  auxiliary type for the nest, declares the group as a mutual group, and then
  derives the recursor for the group. The kernel refuses to let an auxiliary
  name leak out of that construction, in `check_no_nested_aux`. So by the time
  a declaration reaches a checker, the nest is already gone, which is why
  section 15.3 gives a nested type a weaker rule and not a new mechanism.
- **Rocq accepts a nest directly.** Its guard condition understands a
  constructor whose field mentions the type under another inductive type, and
  the recursion check follows the nest.
- **Agda asks for a termination proof instead.** A pattern match over a nested
  type is checked by the termination checker, and the checker can be told to
  stop checking. That flag is the same loaded gun as the positivity flag of
  chapter 12, section 12.10.

One honest limit, stated again. Section 7.1 reads the shape of a mutual
recursor from our own reasoning, because our fixture holds no mutual inductive
type from the real Lean. Chapter 11, section 11.9 says how to get one.

## 15.8 References

**Our code**

- `crates/rean_kernel/src/typeck.rs`, the method `with_group`
- `crates/rean_kernel/src/positivity.rs`, the nested case
- `crates/rean_kernel/tests/soundness.rs`
- `crates/rean_export/src/reader.rs`, which records the grouping of a line

**Lean's own source**

- `src/kernel/inductive.cpp`. The group arrives as one declaration, and
  `check_positivity`, `check_uniform_ind_occs` and `check_no_nested_aux` are
  the three tests this chapter mirrors.

**Read more**

- Dybjer, *Inductive families*, 1994, for a family declared at once.
  DOI [10.1007/BF01211308](https://doi.org/10.1007/BF01211308)
- Paulin-Mohring, *Inductive definitions in the system Coq*, 1993, for the
  positivity condition on a mutual group.
  DOI [10.1007/BFb0037116](https://doi.org/10.1007/BFb0037116)
- Rocq, inductive types, for a nest accepted directly.
  <https://rocq-prover.org/doc/master/refman/language/core/inductive.html>

---

**Next:** [The frontend](16-the-frontend.md)
