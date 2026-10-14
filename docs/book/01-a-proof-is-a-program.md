# 1. A proof is a program

> **Where you are.** Chapter 1 of 8 in Part I. This is the first one, so it
> assumes nothing.
>
> **This chapter adds** one idea: a proposition is a type, and a proof is a
> term of that type.
>
> **The four beats.** The idea is section 1.1. Your language is section 1.2.
> The notation is section 1.4. Lean arrives in section 1.5 and not before.
>
> **Do not skip ahead.** Every later chapter uses this idea. If a word here is
> new, that is normal. [The glossary](../GLOSSARY.md) holds every word.

---

## 1.1 The idea

Two words carry this whole part. A **claim**, and a **reason**.

A claim is a statement that may hold or may not hold. "Every list I sort comes
back sorted" is a claim. A reason is the thing that makes the claim hold. A
reason must be something a reader can follow, step by step. Nothing is left to
belief.

Now the move. **Keep the claim and the reason as two separate objects.** Then
treat one question, "does this reason support this claim", as a question about
their two shapes.

That is the whole idea. Nothing about computers yet, and nothing about Lean.

A picture for it. A claim is a room with a door, and the door has a shape cut
into it. A reason is a key. The key either fits the shape or it does not, and
one look at the two shapes settles it. Nobody has to open the door and argue
about what is inside.

Three things follow at once, and all three are the reason this idea matters.

- **A checker never searches.** It compares two shapes. A person or a program
  hands it the key.
- **A checker can be small.** The comparison of two shapes is a short
  algorithm, even when the claim is enormous.
- **A reason is an object.** You can store a key, mail it, and try it in the
  same door in ten years.

A [proof](../GLOSSARY.md#proof) is the reason. A
[proposition](../GLOSSARY.md#proposition) is the claim. A proof checker is the
program that compares the two shapes. It does not search for a proof, and it
does not help you write one. A person or a [tactic](../GLOSSARY.md#tactic)
writes the proof, and the checker only says yes or no.

That sounds like a hard job for a special program. It is not. **You already run
a program that compares shapes every day.** It is called a type checker.

---

## 1.2 In your language

Read this signature. The body is missing on purpose.

```ts
declare function id<A>(a: A): A
```

Answer a question before you read on. What can the body do?

It cannot look inside `a`, because it does not know what `A` is. It cannot
build an `A`, for the same reason. It can only give back the `a` it got.

**The type forced the behaviour.** Nobody ran the function to learn that. The
signature alone said it.

Now read the same signature as a sentence about a claim and a reason:

```
the claim   : for every A, if you give me an A, I give you an A
the reason  : the function body, which hands the A straight back
```

The signature is the shape cut into the door. The body is the key. And `tsc`
is the program that checks that the key fits. You have been doing section 1.1
since the first day you wrote a type.

One honest note, because it matters later. A TypeScript function may loop for
ever or throw, so a TypeScript type is a weaker promise than it looks. Every
Lean function is [total](../GLOSSARY.md#total), and
[chapter 6](06-inductive-types.md) is where that rule gets its teeth. Section
1.7 shows the exact hole.

---

## 1.3 Three ways to see it

Pick whichever one sticks. They are the same idea.

**As a recipe.** A proof is not a page of text. It is a recipe that the checker
can follow. "Give me a proof of `A`, and here is how I build a proof of `B`."

**As a room.** A proposition is a room. A proof is somebody standing in it. The
proposition is true when the room is not empty. The checker does not argue
about the room. It looks for a person in it.

**As a compiler.** You run a proof checker every time you build your project.
`tsc` already proves small theorems about your program, such as "this value is
not `null` here". Lean lets the theorems get as large as you like, and the
checking stays the same job.

---

## 1.4 The notation, which is a dictionary

The idea has a name, the [Curry-Howard](../GLOSSARY.md#curry-howard)
correspondence, and it gives you one piece of notation and one table.

The notation is a colon.

```
h : A
```

Read it two ways at once. "The term `h` has the type `A`." And "the proof `h`
supports the claim `A`." One line, two readings, and the checker only ever does
the first one.

The table is the dictionary. The left column is logic. The middle column is the
type theory. The right column is your editor.

| Logic | Type theory | In TypeScript |
|---|---|---|
| `A` holds | some term has type `A` | the type is **[inhabited](../GLOSSARY.md#inhabited)** |
| `A → B` | a function from `A` to `B` | `(a: A) => B` |
| `A ∧ B` | a pair that holds both | `[A, B]`, or `{ left: A; right: B }` |
| `A ∨ B` | a value that is one side or the other | a discriminated union |
| `True` | a [unit type](../GLOSSARY.md#unit-type), with one element | `undefined`, which has exactly one value |
| `False` | an [empty type](../GLOSSARY.md#empty-type), with **no** element | `never` |
| `¬ A` | `A → False` | `(a: A) => never` |
| `∀ x : A, P x` | a function that takes `x` and returns a proof of `P x` | a generic, and more. [Chapter 3](03-types-that-depend-on-values.md). |

Read the `False` row twice. A false proposition is not an error and not a
crash. It is a type that nothing inhabits. To prove `¬ A`, write a function
from `A` to a type that has no elements. If you ever get a value of `A`, you
can hand back something impossible, and that is exactly what "A is false"
means.

---

## 1.5 In Lean

Now the real syntax. Here is section 1.2, in Lean:

```lean
theorem id_thm (A : Prop) (h : A) : A := h
```

Four parts, and you have met all four.

| The part | What it is |
|---|---|
| `id_thm` | a name |
| `(A : Prop) (h : A)` | what goes in. `h` is a proof of `A`. |
| `: A` | the claim. The shape cut into the door. |
| `:= h` | the reason. The key. |

Same shape as the TypeScript. The type is the claim, the term is the proof, and
`Prop` is the word for "the collection of claims". Chapter 4 says what `Prop`
is.

Ask Lean to read a type back to you with `#check`. This is the one command you
will use in every chapter from here on:

```lean
#check @id_thm      -- ∀ (A : Prop), A → A
```

Read the output. `∀ (A : Prop), A → A`. That is row 8 and then row 2 of the
dictionary in section 1.4, in Lean's own notation.

---

## 1.6 What changes when you believe this

Three consequences, and all three shape the rest of the book.

1. **A proof checker is a type checker.** One program, one algorithm.
   [Chapter 5](05-the-calculus-of-constructions.md) writes down its rules.
2. **A proof is data.** You can print it, store it, send it to another program,
   and check it again. [Chapter 8](08-what-you-must-trust.md) is about why that
   matters so much.
3. **The checker must sometimes run your program.** A type can hold a value, so
   to compare two types the checker may have to compute.
   [Chapter 7](07-definitional-equality.md) is that story, and it is the reason
   a proof checker is not a weekend project.

---

### If you write TypeScript

You have met every piece of this already, under other names.

| In your editor | Here |
|---|---|
| `<A>(a: A) => A` | the proof of `A → A` from section 1.2 |
| `never` | the [empty type](../GLOSSARY.md#empty-type). To prove `¬ A`, write a function into it. |
| `undefined` as a type, which has one value | the [unit type](../GLOSSARY.md#unit-type), which is how `True` is built |
| a discriminated union | `A ∨ B`. One tag per side. |
| `Effect<A, never, never>`, which cannot fail and needs nothing | the same `never`, read as a promise. The error channel is empty, so no error value exists. |
| the `E` channel of `Effect<A, E, R>` | a type that records a fact about a program. You write propositions already. |

**Effect is the closest thing you use to this chapter.** `Effect<A, E, R>`
states three facts about a program in its type. The compiler checks every one
of them where you use it. Set `E` to `never` and you have said "this cannot
fail", in the type, with no test. That is a claim and a reason in your own
code.

```ts
import { Effect } from "effect"

const ok: Effect.Effect<number, never, never> = Effect.succeed(1)
```

One real difference, and it is the whole reason Lean works. In TypeScript,
`never` is **not** empty:

```ts
const loop = (): never => loop()      // TypeScript accepts this
```

That term never returns, and it inhabits the empty type. So a type in
TypeScript is a promise **if** the program stops. In Lean every function is
[total](../GLOSSARY.md#total), so the promise holds with no condition, and a
type may be read as a statement of logic.

| | `never` | is it empty? | so a type is |
|---|---|---|---|
| TypeScript | the bottom type | **no**. `loop` above inhabits it. | a promise, if the program stops |
| Lean | `False`, an inductive type with no constructor | **yes** | a promise, with no condition |

Hold on to that table. Chapter 6, section 6.7 is the rule that keeps the Lean
column honest.

---

## 1.7 Try it

The checker in this repository can already do the proof of section 1.2.

```sh
devbox run -- cargo run -p rean -- prove
```

```text
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

Read the third block. Nobody wrote that type in the test. The checker
**computed** it from the term, and then compared it with the claim. That is the
comparison of two shapes from section 1.1, done by a program you can read.

The last line is chapter 4. Leave it for now.

---

## 1.8 Check yourself

You are ready for chapter 2 when you can answer these three without scrolling
up.

1. What does it mean for a proposition to be false, in terms of types?
2. `fun h => h` proves `A → A`. What proves `A → (B → A)`?
3. Why is a proof checker allowed to be small?

### Answers

1. Its type has no elements. Nothing inhabits it.
2. `fun a => fun b => a`. It takes a proof of `A`, takes a proof of `B`, throws
   the second away, and returns the first.
3. Because it only **checks**. It never searches. The search happens in
   untrusted code, and the checker re-reads the answer.

---

## 1.9 References

- *Theorem Proving in Lean 4*, the chapter on propositions and proofs. The same
  idea, with Lean's own words.
  <https://lean-lang.org/theorem_proving_in_lean4/>
- *Functional Programming in Lean*, for Lean as a language you program in.
  <https://lean-lang.org/functional_programming_in_lean/>
- TypeScript, generics, for the signature of section 1.2.
  <https://www.typescriptlang.org/docs/handbook/2/generics.html>
- TypeScript, everyday types, for `never` and `unknown`.
  <https://www.typescriptlang.org/docs/handbook/2/everyday-types.html>
- Effect, the `Effect` type, for the three channels.
  <https://effect.website/docs/getting-started/the-effect-type/>
- Our code. `crates/rean_kernel/src/typeck.rs` holds the checker, and
  `crates/rean_kernel/tests/typeck.rs` holds the proof of section 1.2.
- Every source for Part I is in [the references](../REFERENCES.md).

---

**Next:** [2. Terms, binders, and names you do not need](02-terms-and-binders.md)
