# 4. Types that depend on values

> **Where you are.** Chapter 4 of 9 in Part I.
>
> **Before this.** Chapters [1](01-a-proof-is-a-program.md) and
> [3](03-terms-and-binders.md). You need a term, a binder, and substitution.
>
> **This chapter adds** the function type that chapter 1 promised, the one that
> can speak about its own argument.
>
> **The four beats.** The idea is section 4.1. The data is sections 4.2 and
> 4.4. The rule is section 4.3. The code is section 4.6.
>
> **Do not skip ahead.** This is the step where Lean leaves every mainstream
> language behind. Chapter 8 exists because of this chapter.

---

## 4.1 The idea

A type is a promise. The question of this chapter is **how much** a promise may
say.

Start with the weakest useful promise. "This function takes a number and gives
back a number." It rules out a great deal. It cannot rule out the one thing you
usually care about, which is **the relation between what went in and what came
out**. A function that always returns zero keeps that promise.

Now the move. **Let the promise mention the argument.**

"This function takes a list and a number `n`, and gives back a list of length
`n`." The promise now speaks about a value that does not exist yet. When the
value arrives, the promise becomes a specific one.

That is a **dependent type**, and it is the whole chapter.

### Three ways to see it

Pick whichever one sticks. The second is the one to keep.

**A promise that does arithmetic.** A function that adds an item to a list does
not only return a list. It returns a list that is one longer than the one it
got. Put the arithmetic in the type, and the checker checks the arithmetic.

**A shelf of boxes.** Picture a shelf, with one box per length.

```
   length:      0        1        2        3        4     ...
            ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐
            │      │ │      │ │      │ │      │ │      │
            └──────┘ └──────┘ └──────┘ └──────┘ └──────┘
```

The shelf is a **family** of types. The number that picks a box is an
[index](../GLOSSARY.md#index). The item type, which is the same on the whole
shelf, is a [parameter](../GLOSSARY.md#parameter). A dependent function is one
that takes a value and picks a box with it.

**A contract filled in at the call.** A signature is a blank contract. The
argument writes a number into the blank, and the contract becomes a specific
one. No mainstream language lets a run-time value hold the pen.

So a type is no longer a fixed label. **A type is the result of a function from
values to types.** Hold on to that sentence. It is the source of everything
hard in this book, and of everything powerful.

---

## 4.2 The data, in your language

TypeScript gets closer to this than most people notice, and then stops at an
exact place. The place is worth knowing, because it tells you what the chapter
is really adding.

**A result type that depends on an argument.** This is ordinary TypeScript:

```ts
declare function get<O, K extends keyof O>(o: O, k: K): O[K]

const row = { a: 1, b: "x" }
const n: number = get(row, "a")      // the result type came from the argument
```

Read the signature. The result type `O[K]` is computed from `k`, which is an
argument. That is section 4.1, in your editor, today.

**And here is the stop.** `tsc` could only do that because it knew the key
while it checked. Hand it a key that arrives at run time:

```ts
declare const fromNetwork: string
const bad = get(row, fromNetwork)
```

```text
error TS2345: Argument of type 'string' is not assignable to parameter of
type '"a" | "b"'.
```

TypeScript lifted `"a"` into a **literal type** and then computed with the
type. It never computed with the value. A key that only exists while the
program runs is a `string`, and a `string` carries nothing the type system can
use.

**One more near miss.** A tuple carries its length in its type, and an array
does not:

```ts
type Len = (readonly ["a", "b", "c"])["length"]   // 3
```

So TypeScript can say "exactly three". It cannot say "as long as the number
this function returns".

| | can a type hold a run-time value? | where the limit is |
|---|---|---|
| TypeScript | no | a value must be known while `tsc` runs, as a literal type |
| Rust, with `[T; N]` | no | `N` must be known when the program is built |
| C++, with a template parameter | no | the same |
| Lean, with `Vector α n` | **yes** | nothing. `n` may arrive at run time. |

---

## 4.3 The rule

Write it like this.

```
(x : A) → B
```

Read it: "give me an `x` of type `A`, and I give you a `B`, and `B` may mention
`x`".

The name for this form is a **[Pi type](../GLOSSARY.md#pi-type)**. Two
spellings of it hide in plain sight.

- When `B` ignores `x`, people write `A → B`. The arrow is the short form.
- When `A` is a proposition, people write `∀ x : A, B`.

**Those are the same term form.** Not two forms that behave alike. One form.
Lean has one node for it, and so does every kernel of this kind. Every `→` you have ever
written in Lean is a Pi type whose body ignores its binder.

That single fact is why the language of chapter 3 stays so small. Chapter 3
listed three term forms. This chapter adds one, and it is the fourth of six.

The rule that makes it useful is the rule for a call, and it uses the one
operation of chapter 3:

```
if   f : (x : A) → B      and   a : A
then f a : B[x := a]
```

Read the last line. The type of `f a` is **`B` with the argument substituted
into it**. The [substitution](../GLOSSARY.md#substitution) of chapter 3,
section 3.3, now runs inside types. Section 4.5 says what that costs.

---

## 4.4 The shelf, as data

Section 4.3 gave the rule. Here is the shelf of section 4.1 as a tree, in the
types of [chapter 2](02-every-type-the-kernel-has.md).

This is the type of a function that adds one item to a vector of length `n`:

```
forall(α, sort(succ(zero)),
  forall(n, const(Nat),
    forall(v, app(app(const(Vector), bvar 1), bvar 0),
      forall(a, bvar 2,
        app(app(const(Vector), bvar 3),
            app(app(const(Nat.add), bvar 2), lit 1))))))
```

Four binders, in order: `α`, `n`, `v`, `a`. Now read the last two lines, which
are the **result** type. The `bvar 3` is `α`, three binders out. The `bvar 2` is
`n`.

That `bvar 2` is the whole chapter. It is the length, and the length arrives as
an **argument of the function**. So the result type is computed from a value
that nobody knows until the call happens. A type that holds a bound variable is
a type that speaks about a value.

Now the shelf itself. A family of types is an ordinary function whose results
are types, and nothing new is needed to write one:

```
lam(n, const(Nat),
  app(app(const(Vector), const(Nat)), bvar 0))
```

A lambda whose body is a type. Its own type is:

```
forall(n, const(Nat), sort(succ(zero)))
```

Read that as "from a number to a type". The last sentence of section 4.1, as
data. No new node, no new rule. The language of chapter 3 already allowed it,
and this chapter is about what that permission costs.

---

## 4.5 What it costs

A checker for dependent types has to do something that no C compiler ever does.
**It has to compute with values while it checks types.**

Ask whether `Vector α (2 + 1)` and `Vector α 3` are the same type. Somebody has
to add two and one. That somebody is the kernel.

```
   the question    Vector α (2 + 1)   ≟   Vector α 3
   the work        add 2 and 1
   the answer      yes
```

Chapter 8 is about exactly this, and
[Part VI of the guide](../README.md) is about what it costs in seconds. The
cause is the one line of section 4.3, `f a : B[x := a]`. Let a type hold a
value and a type checker becomes an evaluator.

---

### If you write TypeScript

This is the chapter where your language gets closest and still stops.

**You already write a dependent signature.** `get<O, K extends keyof O>(o, k):
O[K]` from section 4.2 is one. So is any overload set, and so is any
conditional return type. The result type depends on the argument.

**The limit is always the same.** The value has to be known while `tsc` runs.
TypeScript lifts a known value into a literal type and then computes in the
type world. That world is separate, with its own rules and its own budget. A
value from a network response never enters it. Chapter 8, section 8.4 is the
same budget in a kernel.

**Effect shows you why you want more.** `Effect<A, E, R>` tracks three facts
about a program in its type. The compiler checks every one of them where you
use it:

```ts
import { Effect } from "effect"

const ok: Effect.Effect<number, never, never> = Effect.succeed(1)
```

A dependent type is that move with no ceiling. The type may state **any** fact,
including a fact about a value, and the proof is the term that satisfies it.
Where Effect gives you three fixed channels, Lean gives you one type and lets
you write the fact yourself.

| | a type that depends on a value | type-level computation | the ceiling |
|---|---|---|---|
| TypeScript | a literal type only | conditional, mapped and template literal types | `TS2589`, a work budget |
| Effect | the same, with three named channels | the same | the same |
| Lean | **any** value, at run time | the same reduction the program uses | a fuel limit the checker reports. Chapter 8. |

---

## 4.6 Try it

TypeScript can go a surprising distance into this chapter, and then it stops.
The place where it stops is the lesson. Paste this into a playground.

```ts
// A vector that carries its length in its own type.
type Vec<A, N extends number, Acc extends A[] = []> =
  Acc["length"] extends N ? Acc : Vec<A, N, [A, ...Acc]>

type Three = Vec<string, 3>  // [string, string, string]

// "Adding one item makes it one longer" is a spread, and it is exact.
type Push<V extends unknown[], A> = [...V, A]
type Four = Push<Three, string>  // four of them

// So far, so dependent. Now ask for a length a person would pass at run time.
type Big = Vec<string, 5000>
//   Type instantiation is excessively deep and possibly infinite. ts(2589)
```

Raise that number until the compiler gives up, and note where it happens.

The failure is not a defect. `N` has to be a literal that the compiler already
holds, and the compiler reaches the length by building the tuple one item at a
time. A dependent type system takes `n` as an ordinary argument, computes with
it **during the check**, and has no ceiling of this kind.

What it pays for that freedom is section 4.5, and the price is the subject of
[chapter 8](08-definitional-equality.md).

---

## 4.7 Check yourself

1. `A → B` is the short form of what?
2. Why can a TypeScript lookup type not do what `Vector α n` does?
3. The type of `f a` is `B[x := a]`. Which chapter 3 operation is that?

### Answers

1. `(x : A) → B`, where `B` does not mention `x`. One term form, two spellings.
   `∀` is the third spelling.
2. Because `tsc` needs the key while it checks, as a literal type. A Lean `n`
   may be a value that only exists while the program runs.
3. Substitution, from section 3.3. The one operation. Now it runs in types as
   well as terms.

---

## 4.8 References

- *Theorem Proving in Lean 4*, on dependent function types.
  <https://lean-lang.org/theorem_proving_in_lean4/>
- *The Lean Language Reference*, the type system, for the official rules.
  <https://lean-lang.org/doc/reference/latest/The-Type-System/>
- TypeScript, indexed access types, for `O[K]` in section 4.2.
  <https://www.typescriptlang.org/docs/handbook/2/indexed-access-types.html>
- TypeScript, conditional types, for the type-level half of the idea.
  <https://www.typescriptlang.org/docs/handbook/2/conditional-types.html>
- Effect, the `Effect` type, for three facts in one type.
  <https://effect.website/docs/getting-started/the-effect-type/>
- Nederpelt and Geuvers, *Type Theory and Formal Proof*, chapter 7, for this
  axis of the cube on its own.
  <https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C>
- Dybjer, *Inductive families*, 1994, for the idea of a type indexed by a
  value. DOI [10.1007/BF01211308](https://doi.org/10.1007/BF01211308)
- Brady, *Idris 2: Quantitative Type Theory in Practice*, 2021, for another
  language built on this form.
  DOI [10.4230/LIPIcs.ECOOP.2021.9](https://doi.org/10.4230/LIPIcs.ECOOP.2021.9)

---

**Next:** [5. Prop, Type, and Sort](05-prop-type-and-sort.md)
