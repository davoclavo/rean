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
> **The four beats.** The idea is section 6.1. Your language is section 6.2.
> The notation is section 6.3. Lean is in section 6.3 and in every section
> after it.
>
> **Do not skip ahead.** Chapter 7 computes with the rule this chapter
> introduces.

---

## 6.1 The idea

Chapter 5 ended with a system that has functions and nothing else. No numbers,
no lists, no `and`, no `or`, no `=`. It needs one more kind of declaration, and
the idea behind that declaration is a trade.

**You say how to build a thing. The system tells you how to use it.**

That is the trade, and both halves matter.

**Your half.** List the ways to build a value, and promise that there are no
others. "A number is either zero, or the successor of a number. Nothing else is
a number." That last sentence is the whole content of the promise, and it is
what you could never write with functions alone.

**The system's half.** Because nothing else is a number, the system can hand
you back a tool that covers every case. One case per way to build. The tool has
a name, a **[recursor](../GLOSSARY.md#recursor)**, and it is the gift.

Why is that a gift and not a formality? Because the recursor is **induction**.
"Nothing else is a number" is exactly what you need to argue "so this holds for
every number". The promise you made to get a data type is the same promise that
lets you prove things about it.

A picture. A declaration is a grammar, and a value is a sentence in it.

```
   the grammar        zero  |  succ <number>
   a sentence         succ (succ zero)
   the recursor       a reader for every sentence the grammar can make
```

One more thing, and it is the reason this chapter is the longest in Part I. The
promise can be abused. Write a constructor that takes a function **from** the
type you are declaring, and you can prove anything at all. Section 6.7 is the
gate that stops it, and it is two words long.

---

## 6.2 In your language

You write the first half of the trade every day.

```ts
type Nat = { tag: "zero" } | { tag: "succ"; n: Nat }
```

A discriminated union. Two ways to build a value, and nothing else is a `Nat`.
That is your half of section 6.1, in TypeScript, and `tsc` enforces the promise
for you. Miss a case and the value that reaches the default arm is not `never`,
so the assignment fails:

```ts
const depth = (t: Nat): number => {
  switch (t.tag) {
    case "zero": return 0
    // the "succ" arm is missing
    default: { const never: never = t; return never }
  }
}
```

```text
error TS2322: Type '{ tag: "succ"; n: Nat; }' is not assignable to type 'never'.
```

Read the message. `tsc` knows there are exactly two ways to build a `Nat`, so
it can name the one you forgot. That is "nothing else is a number", enforced.

**And you write the second half by hand.** Here is the recursor, in TypeScript,
with no library:

```ts
const natRec = <A,>(z: A, s: (n: Nat, ih: A) => A) =>
  (t: Nat): A => t.tag === "zero" ? z : s(t.n, natRec(z, s)(t.n))

const toNumber = natRec<number>(0, (_n, ih) => ih + 1)
```

Read the arguments of `natRec`. One value for `zero`. One function for `succ`,
and that function takes the smaller number **and** the answer for the smaller
number. You have written this shape as `fold` a hundred times.

**Effect gives you the same thing with a name.** `Data.TaggedEnum` declares the
type, and `$match` is the recursor:

```ts
import { Data } from "effect"

type Shape = Data.TaggedEnum<{
  Circle: { readonly radius: number }
  Square: { readonly side: number }
}>
const { $match, Circle, Square } = Data.taggedEnum<Shape>()

const area = $match({
  Circle: ({ radius }) => Math.PI * radius * radius,
  Square: ({ side }) => side * side,
})
```

One arm per constructor, and the compiler refuses an arm you forgot. **That is
the recursor of section 6.1.** Lean's version differs in exactly one way, and
that one way is the whole chapter. In Lean the result of `$match` may be a
**proof**. Then the same function is induction.

---

## 6.3 The notation, and the three things a declaration gives back

**The notation.** A declaration lists the constructors, and each constructor
carries its type.

```
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

Two ways to build a number. The second one takes a number, so the type is
recursive. That is section 6.2 with Lean's syntax on it.

For one declaration the kernel adds three kinds of thing to the environment.

| Thing | For `Nat` | What it is for |
|---|---|---|
| the type | `Nat` | to speak about |
| the constructors | `Nat.zero`, `Nat.succ` | to **build** a value |
| the **[recursor](../GLOSSARY.md#recursor)** | `Nat.rec` | to **use** a value |

**In Lean.** The third row is the one with no counterpart in your toolchain.
Ask Lean to print it:

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

- **[motive](../GLOSSARY.md#motive)**. What you want to get, as a function of
  the value. One per type. In section 6.2 the motive was the type parameter `A`
  of `natRec`, and it could not depend on the value. Here it can.
- **[minor premise](../GLOSSARY.md#minor-premise)**. What to do for one
  constructor. One per constructor, so `zero` and `succ` above. Those are the
  two arguments of `natRec`.
- **[major premise](../GLOSSARY.md#major-premise)**. The value you take apart.
  It is `t`, and it comes last.

Read the `succ` line once more. It takes the number `n` **and** a `motive n`,
which is the answer for the smaller number. That extra argument is the
[induction hypothesis](../GLOSSARY.md#induction-hypothesis). Nobody added it.
It falls out of the shape of the constructor.

---

## 6.4 ι, the rule that computes

A recursor is useless until it runs. One rule makes it run, and it is called
**[ι, iota](../GLOSSARY.md#iota)**.

```
Nat.rec z s (Nat.succ n)   ≡   s n (Nat.rec z s n)
```

In words: when the value you take apart is **built by a constructor**, replace
the recursor call with the minor premise for that constructor.

That is one line of `natRec` from section 6.2, written as an equation rather
than as code. The `t.tag === "zero"` test is the same test. The difference is
that the kernel is allowed to run this rule **while it checks a type**.

Two notes, and both matter later.

- The rule fires only on a constructor. If the major premise is a variable, the
  term is **[stuck](../GLOSSARY.md#stuck)**, and stuck is the correct answer.
- The right hand side calls `Nat.rec` again, on the smaller number. So one ι
  step can make the term **bigger**. Hold on to that. It is why chapter 7 is
  hard, and it is why [Part VI of the guide](../README.md) exists.

---

## 6.5 One term, two readings, and where logic comes from

**The idea.** Look at `motive` in section 6.3. It returns `Sort u`, so `u` may
be any level, and chapter 4 told you what the levels are. Point the motive at
`Type` and you get a program. Point it at `Prop` and you get a proof.

| Choose the motive in | And `Nat.rec` is | You call it |
|---|---|---|
| `Type` | a recursive function | recursion |
| `Prop` | a proof about every number | induction |

**Induction and recursion are the same term.** Proof by induction on `n` is a
recursive program whose output is a proof. That is chapter 1's dictionary, used
in earnest, and it is the reason section 6.2 ends where it does. Your `$match`
cannot land in `Prop`, because TypeScript has no `Prop`.

**Now the payoff.** Every connective from chapter 1's dictionary is an
inductive type. None of them is built into the kernel.

| Logic | Declared as | Constructors |
|---|---|---|
| `False` | inductive | **zero**. Nothing builds it. |
| `True` | inductive | one, with no argument |
| `A ∧ B` | inductive | one, which carries both proofs |
| `A ∨ B` | inductive | two, one per side |
| `∃ x, P x` | inductive | one, which carries a witness and a proof |
| `a = b` | inductive | one, named `rfl` |
| `¬ A` | not a declaration | it is `A → False` |

**In Lean.** Lean will show you:

```lean
#check @Eq            -- {α : Sort u_1} → α → α → Prop
#check @Eq.refl       -- ∀ {α : Sort u_1} (a : α), a = a
#check @And.intro     -- ∀ {a b : Prop}, a → b → a ∧ b
#check @False.rec     -- (motive : False → Sort u_1) → (t : False) → motive t
```

Read `False.rec`. It takes a `False` and gives you **anything you asked for**.
That is safe for one reason only: no constructor builds a `False`, so nobody
can ever call it. "From a contradiction, anything follows" is not an axiom here.
It is a recursor with zero minor premises.

---

## 6.6 Parameter or index

One distinction, because the chapters on the kernel need it to be exact. Look
at `Eq` again.

```
Eq : {α : Sort u} → α → α → Prop
```

- `α` is a **[parameter](../GLOSSARY.md#parameter)**. It is fixed across every
  constructor.
- the second `α` argument is an **[index](../GLOSSARY.md#index)**. It varies.
  `rfl` forces the two sides to be the same, so the index is where the
  information lives.

A parameter comes first and a constructor shares it. An index is what makes a
family of types rather than one type. That family is the shelf of boxes from
chapter 3, section 3.1. [The environment chapter](../10-the-environment.md)
counts both, and one wrong count breaks every recursor.

---

## 6.7 The one rule that keeps it safe

Here is the scariest-looking rule in the book, and it is two words long:
**[strict positivity](../GLOSSARY.md#strict-positivity)**.

**The idea.** A thing may contain smaller copies of itself. A thing must not be
able to consume itself. The first is a tree. The second is a loop, and a loop
in a logic proves everything.

**The notation, in one line.** In a constructor argument, the type being
declared may appear to the **right** of an arrow, and never to the **left**.

```lean
| succ : Nat → Nat                 -- fine. Nat is to the right.
| node : List Tree → Tree          -- fine. Nested, and still to the right.
| mk   : (Bad → False) → Bad       -- refused. Bad is to the left.
```

**In Lean.** Try to declare the third one:

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

That is the whole gate, and it is the only thing standing between you and a
proof of `False`. Every system has it. Agda has a flag that turns it off, and
with that flag a user can prove anything. The TypeScript section below writes
the same declaration in TypeScript, where it is accepted, and says why that is
correct there and fatal here.

---

## 6.8 Three more shapes you will meet

**A [structure](../GLOSSARY.md#structure)** is an inductive type with **one**
constructor and no index. The word names a shape, not a feature. Because there
is one constructor, the kernel adds a shortcut for reading a field. It is
called a projection, and [the environment chapter](../10-the-environment.md)
is where our code reads one.

**A [mutual group](../GLOSSARY.md#mutual-group)** is two types declared
together, each one mentioning the other. Each recursor then takes one motive
per type.

**A [nested inductive](../GLOSSARY.md#nested-inductive)** holds itself inside
another type, as in `node : List Tree → Tree`. Ask for its recursor and you can
see how Lean handles it:

```lean
inductive Tree where
  | leaf
  | node : List Tree → Tree

#check @Tree.rec
```

```text
@Tree.rec : {motive_1 : Tree → Sort u} → {motive_2 : List Tree → Sort u} → ...
```

**Two** motives, for one declared type. Lean turned the nest into a mutual
group behind your back, with `List Tree` as the second member.

---

## 6.9 Two things the kernel adds on top

CoIC is now complete, and a real kernel still holds two extras. Both are
honest and both are worth knowing early.

- **A number is stored as digits.** In the theory, `3` is
  `Nat.succ (Nat.succ (Nat.succ Nat.zero))`. No kernel wants a million nested
  constructors, so Lean stores the digits and computes with a big number
  library. That choice buys speed and owes two obligations, and
  [making it work](../12-making-it-work.md) pays them.
- **[Quotients](../GLOSSARY.md#quotient) are primitive.** No inductive
  declaration can give you "these two values are now the same". Lean adds four
  constants, `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`, and one computation
  rule. That is how the rationals are built from pairs of integers.

---

## 6.10 Three ways to see an inductive type

**As a grammar.** The constructors are the production rules. A value is a
sentence in that grammar, and the recursor is a reader for it.

**As a fold.** `Nat.rec` with a motive in `Type` is exactly `fold` over a list
of `succ` steps. You give the base case and the step, and it walks the value.
Section 6.2 wrote that fold in TypeScript.

**As a match, written as a function.** `Nat.rec` is the `switch` a compiler
would generate, handed to you as an ordinary function. The kernel needs it as a
function, because a function is a term, and a term is the only thing the five
rules of chapter 5 understand.

---

### If you write TypeScript

Two of the three pieces are the same. The third is the one worth your time, and
there is one rule you do not have.

**The constructors match.** A discriminated union, a Rust `enum`, and a Lean
`inductive` are all "a type described by the ways to build it". Section 6.2 put
the two declarations side by side.

**The recursor is your `$match`, or your `fold`.** `Nat.rec` with a motive in
`Type` is `natRec` from section 6.2. The arms are the minor premises. The
exhaustiveness check that `tsc` runs is the reason both are total.

**An index is the real meeting point, and TypeScript nearly has it.** A tag
that narrows a type parameter is an index in the sense of section 6.6:

```ts
type Expr<A> =
  | { tag: "int"; value: number }     // intended only when A is number
  | { tag: "bool"; value: boolean }   // intended only when A is boolean
```

Write that and `tsc` will not hold you to the pairing. TypeScript has no
general way to say "this constructor fixes `A` to `number`". A GADT does that,
and a Lean index does it for free. The nearest thing you can build is a
conditional type per case, and it falls over as soon as the cases grow.
Lean's version takes any **value** as an index, not only a type, so
`Vector α 3` and `Vector α 4` are different types in the same family.

**And one rule your language does not have, for a good reason.** Write the
forbidden type of section 6.7 in TypeScript:

```ts
type Bad = { f: (b: Bad) => never }   // TypeScript accepts this
```

`tsc` is **right** to accept it, because TypeScript is not a logic. As chapter
1 showed, `never` in TypeScript is inhabited by a term that never returns, so
that type promises nothing and costs nothing. Lean refuses the same
declaration, because in Lean every function is
[total](../GLOSSARY.md#total) and `False` really is empty. With those two facts
together, that one type proves everything.

| | the declaration | the eliminator | may land in a proof | positivity checked |
|---|---|---|---|---|
| TypeScript | a discriminated union | `switch`, with exhaustiveness | no | no, and it does not need to be |
| Effect | `Data.TaggedEnum` | `$match` | no | no |
| Lean | `inductive` | `Nat.rec`, a term | **yes**. That is induction. | **yes**, by the kernel |

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

Then watch the gate of section 6.7 do its job:

```sh
devbox run -- cargo test -p rean_kernel --test soundness
```

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
- Effect, `Data.TaggedEnum`, for the declaration and `$match` of section 6.2.
  <https://effect.website/docs/data-types/data/>
- TypeScript, narrowing, for the exhaustiveness check that makes a `switch`
  total. <https://www.typescriptlang.org/docs/handbook/2/narrowing.html>
- Agda, termination and positivity, for the same gate in another system.
  <https://agda.readthedocs.io/en/latest/language/termination-checking.html>
- Lean's own source. `src/kernel/inductive.cpp` builds the recursor, and
  `check_positivity` in that file is section 6.7.
- Our code. `crates/rean_kernel/src/positivity.rs` is section 6.7, and
  `crates/rean_kernel/tests/soundness.rs` holds a real proof of `False` that
  the rule refuses.

---

**Next:** [7. Definitional equality](07-definitional-equality.md)
