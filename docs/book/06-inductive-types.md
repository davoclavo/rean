# 6. Inductive types, and the I in CoIC

> **Where you are.** Chapter 6 of 8 in Part I.
>
> **Before this.** Chapter [5](05-the-calculus-of-constructions.md), and the
> limit it ends on. If you have not read section 5.6, read it now, because this
> chapter answers it.
>
> **This chapter adds** the one extension that turns CoC into CoIC. It is where
> numbers, lists, and every logical connective come from.
>
> **Do not skip ahead.** Chapter 7 computes with the rule this chapter
> introduces.

---

## 6.1 The question

Chapter 5 ended with a system that has functions and nothing else. No numbers,
no lists, no `and`, no `or`, no `=`.

The fix is one new kind of declaration. **Describe a type by the ways you can
build it**, and the kernel gives you back the way to use it.

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

Two ways to build a number. Nothing else is a number. The second one takes a
number, so the type is recursive.

If you have written a Rust enum or a TypeScript union, you have written this
shape before:

```rust
enum Nat { Zero, Succ(Box<Nat>) }
```

The difference is what happens next.

---

## 6.2 What the kernel hands back

For one declaration the kernel adds three kinds of thing to the environment.

| Thing | For `Nat` | What it is for |
|---|---|---|
| the type | `Nat` | to speak about |
| the constructors | `Nat.zero`, `Nat.succ` | to **build** a value |
| the **recursor** | `Nat.rec` | to **use** a value |

The recursor is the part with no counterpart in Rust. Ask Lean to print it:

```lean
#check Nat.rec
```

```text
Nat.rec.{u} {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) : motive t
```

Read it slowly, because three words from the chapters live in that signature.

- **motive**. What you want to get, as a function of the value. One per type.
- **minor premise**. What to do for one constructor. One per constructor, so
  `zero` and `succ` above.
- **major premise**. The value you take apart. It is `t`, and it comes last.

Read the `succ` line once more. It takes the number `n` **and** a `motive n`,
which is the answer for the smaller number. That extra argument is the
induction hypothesis. Nobody added it. It falls out of the shape of the
constructor.

---

## 6.3 One term, two readings

Here is the move that makes the whole system small. Look at `motive`. It returns
`Sort u`, so `u` may be any level, and chapter 4 told you what the levels are.

| Choose the motive in | And `Nat.rec` is | You call it |
|---|---|---|
| `Type` | a recursive function | recursion |
| `Prop` | a proof about every number | induction |

**Induction and recursion are the same term.** Proof by induction on `n` is a
recursive program whose output is a proof. That is chapter 1's dictionary, used
in earnest.

---

## 6.4 The rule that computes

A recursor is useless until it runs. One rule makes it run, and it is called
**ι**, iota.

```
Nat.rec z s (Nat.succ n)   ≡   s n (Nat.rec z s n)
```

In words: when the value you take apart is **built by a constructor**, replace
the recursor call with the minor premise for that constructor.

Two notes, and both matter later.

- The rule fires only on a constructor. If the major premise is a variable, the
  term is **stuck**, and stuck is the correct answer.
- The right hand side calls `Nat.rec` again, on the smaller number. So one ι
  step can make the term **bigger**. Hold on to that. It is why chapter 7 is
  hard, and it is why [Part V of the guide](../README.md) exists.

---

## 6.5 All of logic, declared

Now the payoff. Every connective from chapter 1's dictionary is an inductive
type. None of them is built into the kernel.

| Logic | Declared as | Constructors |
|---|---|---|
| `False` | inductive | **zero**. Nothing builds it. |
| `True` | inductive | one, with no argument |
| `A ∧ B` | inductive | one, which carries both proofs |
| `A ∨ B` | inductive | two, one per side |
| `∃ x, P x` | inductive | one, which carries a witness and a proof |
| `a = b` | inductive | one, named `rfl` |
| `¬ A` | not a declaration | it is `A → False` |

Lean will show you:

```lean
#check @Eq            -- {α : Sort u_1} → α → α → Prop
#check @Eq.refl       -- ∀ {α : Sort u_1} (a : α), a = a
#check @And.intro     -- ∀ {a b : Prop}, a → b → a ∧ b
#check @False.rec     -- (motive : False → Sort u_1) → (t : False) → motive t
```

Read `False.rec`. It takes a `False` and gives you **anything you asked for**.
That is safe for one reason only: no constructor builds a `False`, so nobody can
ever call it. "From a contradiction, anything follows" is not an axiom here. It
is a recursor with zero minor premises.

---

## 6.6 Parameter or index

One distinction, because the chapters on the kernel need it to be exact. Look at
`Eq` again.

```
Eq : {α : Sort u} → α → α → Prop
```

- `α` is a **parameter**. It is fixed across every constructor.
- the second `α` argument is an **index**. It varies. `rfl` forces the two sides
  to be the same, so the index is where the information lives.

A parameter comes first and a constructor shares it. An index is what makes a
family of types rather than one type. Chapter 2 of the implementation chapters
counts both, and one wrong count breaks every recursor.

---

## 6.7 The one rule that keeps it safe

Here is the scariest-looking rule in the book, and it is three words long:
**strict positivity**.

Try to declare this:

```lean
inductive Bad where
  | mk : (Bad → False) → Bad
```

Lean refuses it, and the message comes from the kernel itself:

```text
error: (kernel) arg #1 of 'Bad.mk' has a non positive occurrence
       of the datatypes being declared
```

Why refuse? Because that type proves `False`. The constructor holds a function
**from** `Bad`, so you can feed a `Bad` to itself, and from there you can build
a proof of anything.

The rule, in one line: in a constructor argument, the type being declared may
appear to the **right** of an arrow, and never to the **left**.

```lean
| succ : Nat → Nat                 -- fine. Nat is to the right.
| node : List Tree → Tree          -- fine. Nested, and still to the right.
| mk   : (Bad → False) → Bad       -- refused. Bad is to the left.
```

That is the whole gate, and it is the only thing standing between you and a
proof of `False`. Every system has it. Agda has a flag that turns it off, and
with that flag a user can prove anything.

---

## 6.8 Three more shapes you will meet

**A structure** is an inductive type with **one** constructor and no index. The
word names a shape, not a feature. Because there is one constructor, the kernel
adds a shortcut for reading a field, which chapter 2 of the implementation
chapters calls a projection.

**A mutual group** is two types declared together, each one mentioning the
other. Each recursor then takes one motive per type.

**A nested inductive** holds itself inside another type, as in
`node : List Tree → Tree`. Ask for its recursor and you can see how Lean
handles it:

```lean
inductive Tree where
  | leaf
  | node : List Tree → Tree

#check @Tree.rec
```

```text
@Tree.rec : {motive_1 : Tree → Sort u} → {motive_2 : List Tree → Sort u} → ...
```

**Two** motives, for one declared type. Lean turned the nest into a mutual group
behind your back, with `List Tree` as the second member.

---

## 6.9 Two things the kernel adds on top

CoIC is now complete, and a real kernel still holds two extras. Both are
honest and both are worth knowing early.

- **A number is stored as digits.** In the theory, `3` is
  `Nat.succ (Nat.succ (Nat.succ Nat.zero))`. No kernel wants a million nested
  constructors, so Lean stores the digits and computes with a big number
  library. That choice buys speed and owes two obligations, and chapter 4 of
  the implementation chapters pays them.
- **Quotients are primitive.** No inductive declaration can give you "these two
  values are now the same". Lean adds four constants, `Quot`, `Quot.mk`,
  `Quot.lift` and `Quot.ind`, and one computation rule. That is how the
  rationals are built from pairs of integers.

---

## 6.10 Three ways to see an inductive type

**As a grammar.** The constructors are the production rules. A value is a
sentence in that grammar, and the recursor is a reader for it.

**As a fold.** `Nat.rec` with a motive in `Type` is exactly `fold` over a list
of `succ` steps. You give the base case and the step, and it walks the value.

**As an enum with a match.** `Nat.rec` is the `match` that a Rust compiler
would generate, written as an ordinary function. The kernel needs it as a
function, because a function is a term, and a term is the only thing the five
rules of chapter 5 understand.

---

## 6.11 Try it

Our kernel checks a real inductive type, its constructors and its recursor, out
of a file that the real Lean wrote. Chapter 8, section 8.5 says what that file
is and why it exists. For now it is enough that Lean made it and that a second
program reads it.

```sh
devbox run -- cargo run -p rean -- check fixtures/lean4export/shapes.ndjson
```

```text
level 1: checked 63 of 63 declarations
trust: no accepted declaration rests on an axiom
```

That fixture holds a mutual group, a nested type, all four `Quot` constants, a
structure, and the theorem `2 + 3 = 5`. Chapter 7 is about the last one.

---

## 6.12 Check yourself

1. What three things does one `inductive` declaration add to the environment?
2. `False.rec` returns any type you ask for. Why is that safe?
3. Why does `inductive Bad | mk : (Bad → False) → Bad` have to be refused?

### Answers

1. The type, its constructors, and its recursor. Plus the ι rule for the
   recursor.
2. Because no constructor builds a `False`, so the function can never be
   called. There are zero minor premises to supply.
3. The declared type appears to the left of an arrow, so a value could be fed
   to itself, and that proves `False`. The rule is strict positivity.

---

## 6.13 References

- Pfenning and Paulin-Mohring, *Inductively defined types in the Calculus of
  Constructions*, 1990. The extension this chapter is about.
  DOI [10.1007/BFb0040259](https://doi.org/10.1007/BFb0040259)
- Paulin-Mohring, *Inductive definitions in the system Coq*, 1993, for the
  positivity condition as a rule.
  DOI [10.1007/BFb0037116](https://doi.org/10.1007/BFb0037116)
- Dybjer, *Inductive families*, 1994, for a parameter against an index.
  DOI [10.1007/BF01211308](https://doi.org/10.1007/BF01211308)
- Agda, termination and positivity, for the same gate in another system.
  <https://agda.readthedocs.io/en/latest/language/termination-checking.html>
- Lean's own source. `src/kernel/inductive.cpp` builds the recursor, and
  `check_positivity` in that file is section 6.7.
- Our code. `crates/rean_kernel/src/positivity.rs` is section 6.7, and
  `crates/rean_kernel/tests/soundness.rs` holds a real proof of `False` that
  the rule refuses.

---

**Next:** [7. Definitional equality](07-definitional-equality.md)
