# Chapter 6 — What a theorem rests on

Chapter 5 closed the hole that let a recursor smuggle in an axiom. It left two
things on the table, and this chapter takes both.

```sh
devbox run -- cargo test -p rean_kernel --test soundness
devbox run -- cargo run -p rean -- check fixtures/lean4export/Nat.add_succ.ndjson
```

---

## 6.1 Type correct is not the same as correct

Chapter 5 checks that every ι rule delivers the type the recursor promises.
That is the property that makes ι sound, and it is not enough.

A recursor could offer minor premises of **some other shape**, keep its rules
type correct, and still not be an induction principle. Here is one:

```text
U.rec : {motive : U → Sort v} → ((x : U) → motive U.u) → (t : U) → motive t
```

`U` has one constructor with no field, so induction needs the premise
`motive U.u`. This asks for `(x : U) → motive U.u` instead. And the rule stays
type correct:

```text
fun motive minor => minor U.u        delivers motive U.u, exactly as promised
```

Every check of chapter 5 passes. What is left is not induction.

The sharper case drops an induction hypothesis. For `N.s : N → N`, induction
needs

```text
(k : N) → motive k → motive (N.s k)
```

Offer this instead:

```text
(k : N) → motive (N.s k)
```

and the rule `fun motive mz ms k => ms k` delivers `motive (N.s k)`, which is
what the type promises. Type correct, and no induction at all.

## 6.2 So derive the premises

The cure is to stop accepting and start deriving. For a constructor

```text
c : (params) → (f₁ : F₁) … (f_m : F_m) → I params idx
```

induction needs exactly

```text
(f₁ : F₁) … (f_m : F_m) → (one hypothesis per recursive field)
                        → motive idx (c params f₁ … f_m)
```

A field is **recursive** when its own result type is the inductive type again. A
field of type `(xs) → I params idx'` gives the hypothesis
`(xs) → motive idx' (field xs)`.

`check_minor_premises` builds that term for every constructor and compares it
with the one the file declared, through `is_def_eq`, so a binder name or a
harmless redex does not matter.

### The evidence that it is right

The fixture has six recursors, and Lean wrote all six:

| Recursor | What it tests |
|---|---|
| `Nat.rec` | a recursive field, so an induction hypothesis |
| `Eq.rec` | an index, and a K-like recursor |
| `HAdd.rec`, `Add.rec` | parameters, and a function valued field |
| `PProd.rec` | two parameters and two fields |
| `PUnit.rec` | no field at all |

All six still pass. A derivation that agreed with Lean on only some of them
would be worse than none, because it would refuse correct code.

---

## 6.3 The trust report

The De Bruijn criterion of chapter 0, section 0.16, says the kernel re-checks
everything, so no tactic and no elaborator can lie. There is one exception, and
it is deliberate: an **axiom** asks to be trusted.

So the only honest answer to "do you believe this theorem" is "yes, and here is
what it rests on". Lean spells that question `#print axioms`.

```rust
pub fn axioms_of(&self, name: &Name) -> Vec<Name>
```

It walks the dependency graph and collects every `Axiom` it reaches. Three
details matter:

- The walk follows the **type**, the **value**, and the right hand side of
  every **ι rule**. A recursor names itself, so the graph has a cycle, and the
  walk needs a seen set.
- The driver asks the **trusted** environment, the one holding only
  declarations that checked. So a refused axiom is never reported as something
  we rest on.
- It is sorted by name, so the report is stable.

`rean check` now ends with a trust line:

```
level 1: checked 32 of 32 declarations
trust: no accepted declaration rests on an axiom
```

That line is true, and it is the point. `Nat.add_succ` is proved by `rfl`, so
the whole module takes nothing on faith. A module that used `Classical.choice`
would say so, by name, on that line.

---

## 6.4 Unsafe may not reach into safe code

An `unsafe` or `partial` declaration may not terminate. The kernel evaluates a
term while it checks it, so a proof that rests on one could make the checker
diverge. Worse, a term that does not terminate can be given **any** type, and
that includes `False`.

```rust
pub fn check_safety(&mut self, decl: &Declaration) -> TypeResult<()> {
    if decl.is_unsafe() { return Ok(()); }
    // … no dependency may be unsafe
}
```

An unsafe declaration may use anything. That is what the word means.

Note the difference from an axiom. An axiom is **trusted**, so using one is
fine and the trust report names it. An unsafe declaration is **not trusted at
all**, so a safe declaration may not touch it.

---

## 6.5 Where the checker stands

| Job | Status |
|---|---|
| the reduction rules, all of them | chapters 1, 2, 4 |
| strict positivity, plain inductive | chapter 4 |
| recursor shape and ι rule types | chapter 5 |
| no large elimination out of a non subsingleton `Prop` | chapter 5 |
| universe hygiene, one name per declaration | chapter 5 |
| eta for a structure | chapter 5 |
| a failed declaration stays out of the environment | chapter 5 |
| **derived minor premises** | **chapter 6** |
| **the axiom trust report** | **chapter 6** |
| **unsafe isolation** | **chapter 6** |

### Still missing

| Gap | Kind | What it would take |
|---|---|---|
| mutual inductive and mutual recursor | soundness | the recursor check steps aside above one motive. Generalise it to one motive per type in the group. |
| nested inductive positivity | soundness | understand the auxiliary form Lean compiles a nested inductive into |
| the inductive universe constraint | soundness | an inductive's own `Sort` must be large enough for every constructor field. Needs an order on open levels. |
| `Quot`'s four types | soundness | the kernel should know them, not read them |
| big number arithmetic | completeness | a big integer in place of `u128` |
| `String` literal operations | completeness | the same treatment `Nat` got |
| a full level normal form | completeness | sort and flatten nested `max` |
| `MData` | completeness | a twelfth `Expr` variant |

The honest summary has not changed in shape, only in size. A **plain**
declaration is now hard to lie to. A **mutual** or **nested** one still steps
past three checks.

```
level 1   32 of 32 declarations of a real Lean module
soundness 24 red team tests, every one of which once accepted a lie
trust     every axiom reported, by name
```

---

## 6.6 Exercises

1. Give a recursor whose rules are type correct and which is still not an
   induction principle. Then say which check of chapter 6 refuses it.
2. Why does the dependency walk need a seen set?
3. The driver asks the trusted environment for axioms, not the full module.
   Give the wrong report that the other choice would produce.
4. An axiom may be used and an unsafe declaration may not. Both are things the
   kernel does not verify. What is the difference?
5. `PProd.rec` has two parameters and two fields, and neither field is
   recursive. Write its minor premise by hand, then check it against
   `derive_minor_premise`.
6. Our minor premise derivation puts every field before every induction
   hypothesis. What would break if it interleaved them?

### Answers

1. The one in section 6.1: ask for `(x : U) → motive U.u` where induction needs
   `motive U.u`. `check_minor_premises` refuses it, because the derived premise
   and the declared one are not definitionally equal.
2. A recursor's ι rules call the recursor, so the graph has a cycle and the
   walk would not stop.
3. A file could declare `axiom oops : False`, fail the check, and still be
   reported as an axiom that the module rests on. The report would name
   something we did not accept, which is noise, and it would hide that the
   real answer is that the module does not check at all.
4. An axiom is trusted on purpose, and a report names it so a reader can decide
   whether to accept it. An unsafe declaration may not terminate, and the
   kernel evaluates terms while checking, so there is no safe way to rest a
   proof on one. Trust is a choice. Divergence is not.
5. `(fst : α) → (snd : β) → motive (PProd.mk α β fst snd)`. The fixture checks
   it, because `PProd.rec` is one of the six.
6. Nothing in the comparison, because `is_def_eq` would simply report a
   mismatch. But every real Lean recursor would then be refused, and the
   fixture would drop from 32 of 32. The ordering is not a free choice. It has
   to match the one Lean uses.
