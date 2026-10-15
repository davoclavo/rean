# Part I — How Lean 4 works, from the ground up

Nine short chapters. Read them in order. Each one adds exactly one idea, and
every chapter after it uses that idea.

No mathematics is assumed. **If you can read a TypeScript signature, you can
read this.** Part I holds no Lean syntax and no code of ours. Every idea arrives
as a type you can paste into a playground, and the formula that compresses it
comes afterwards.

---

## The four beats

This part has one method, and it repeats in every section. The order is always
the same, and it never starts with a formula.

```
  1. the idea      ──►  2. the data     ──►  3. the code     ──►  4. the rule
  words and a           the TypeScript       one short            the notation,
  picture               type that holds      function that        with every
                        the idea             walks it             symbol named
```

| Beat | What it gives you | How to read it |
|---|---|---|
| **1. The idea** | the concept, in plain words, with a picture or a metaphor | slowly. If this beat does not land, the next three will not. |
| **2. The data** | the type the idea lives in. You already read types. | fast. This is the beat that makes the idea concrete. |
| **3. The code** | one function over that type, short enough to hold in your head | once, line by line. It is the idea, made to run. |
| **4. The rule** | the rule or the equation, with every symbol named | once aloud. The symbols are short names for beat 1. |

Why this order. A type is a shape you can see. A formula is a compression of a
shape, so it only reads as a formula once you hold the shape. Start at the
compressed end and you memorise symbols. Start at the idea, read the type, run
the function, and the formula is then a summary of something you have watched
work.

**Why no Lean here.** Lean syntax is a third compression, on top of the formula,
and it arrives with a whole language attached. A reader who meets it in chapter
2 spends their attention on syntax rather than on the idea. So Part I stays in
one language, and [the ground truth](../12-the-ground-truth.md) is where real
Lean arrives, together with a real file that the real Lean wrote.

A beat carries a label where the text could be mistaken for the other kind.
Elsewhere the order alone carries it.

---

## The rule of this part

**One idea per chapter, and no chapter stands alone.**

```
1. a proof is a program
      │
      ▼
2. every type the kernel has ──► the map. Ten names, so that the other eight
      │                          chapters have something to point at.
      ▼
3. terms and binders ──────────► the language, and substitution
      │
      ▼
4. types that depend on values ─► the Pi type
      │
      ▼
5. Prop, Type, and Sort ───────► the universes, and imax
      │
      ▼
6. the Calculus of Constructions ─► all of the above, as five rules
      │
      ▼
7. inductive types ────────────► CoC becomes CoIC. Data, logic, induction.
      │
      ▼
8. definitional equality ──────► the rule that makes a checker an evaluator
      │
      ▼
9. what you must trust ────────► the whole machine, and the one hole in it
```

If a chapter feels hard, the chapter before it holds the missing piece. That is
the design, not an accident.

Chapter 2 is the one exception to "one idea per chapter". It is a map rather
than a lesson. It gives every type a name, and then it hands each name to a
later chapter. Read it once, go on, and come back to it.

Chapters 3, 4 and 5 each add one axis to the language, and chapter 6 names the
system that the three axes make. That staircase is not ours. Nederpelt and
Geuvers climb the same one, and the table below says where every part of this
method comes from.

---

## The chapters

| # | Chapter | It answers |
|---|---|---|
| 1 | [A proof is a program](01-a-proof-is-a-program.md) | why a type checker and a proof checker are one program |
| 2 | [Every type the kernel has](02-every-type-the-kernel-has.md) | what the whole job is made of, as five types |
| 3 | [Terms, binders, and names you do not need](03-terms-and-binders.md) | what a term is, and why a bound variable is a number |
| 4 | [Types that depend on values](04-types-that-depend-on-values.md) | how a type can speak about a value, and why no mainstream language does |
| 5 | [Prop, Type, and Sort](05-prop-type-and-sort.md) | what the type of a type is, and what makes `Prop` special |
| 6 | [The Calculus of Constructions](06-the-calculus-of-constructions.md) | the five rules, on one page, and what they cannot do |
| 7 | [Inductive types, and the I in CoIC](07-inductive-types.md) | where numbers, lists, `and`, `or` and `=` come from |
| 8 | [Definitional equality](08-definitional-equality.md) | when two terms are the same, and why a proof by reflexivity sometimes refuses |
| 9 | [What you must trust](09-what-you-must-trust.md) | the five stages, the axioms, and why a second kernel exists |

Each chapter ends with a **Check yourself** section, with answers. Those three
questions are the gate. If you can answer them, go on.

Each chapter also has an **If you write TypeScript** section. Beat 2 gives the
type. That section is the long form, and it holds the table of what your
language can do, what it cannot, and why. It names `never`, `unknown`, a
conditional type, a discriminated union, a lookup type, the `tsc` error
`TS2589`, and the three channels of `Effect<A, E, R>`.

Every mathematical term links to its definition in
[the glossary](../GLOSSARY.md), so the right word is used and the word is never
only a word.

---

## Where this method comes from

Seven books teach this material, and no two of them open the same way. We read
how each one is built and took one thing from each.

| Book | How it opens | What this part took |
|---|---|---|
| *Theorem Proving in Lean 4* | the type theory first, and the logic second | the order of the ideas |
| *Functional Programming in Lean* | a program that runs on page one. The proofs arrive as an interlude. | beat 3, which is a function you can run, in every section |
| *The Little Typer* | one tiny language, one question at a time, and the answer beside it | **Check yourself**, and the rule that a chapter adds one idea |
| *Software Foundations* | short chapters, and every claim in the text is machine-checked | `tools/cite.py`, which fails the build when a chapter names a test nobody wrote |
| Nederpelt and Geuvers, *Type Theory and Formal Proof* | one axis of the Barendregt cube per chapter, from the untyped calculus up | chapters 3, 4 and 5, which add one axis each, and chapter 6, which names the result |
| Harper, *Practical Foundations for Programming Languages* | a judgment and an inference rule, named as notation **before** any rule uses them | section 6.2, which teaches the fraction bar before section 6.3 writes five of them |
| Carneiro, *The Type Theory of Lean* | the rules, as rules, with no prose at all | the reference list at the end of each chapter. This is where a claim is settled. |

One thing none of them does, and this part does. **It asks you to learn no new
syntax in order to start.** The whole theory arrives in one language, and that
language is one you already read. A reader who finishes Part I has met no new
syntax at all, and holds every idea that Lean's kernel implements.

---

## How long it takes

| You have | Read |
|---|---|
| 20 minutes | chapters 1 and 2 |
| one evening | chapters 1 to 6. That is the Calculus of Constructions. |
| two evenings | all nine. That is CoIC, which is what Lean's kernel implements. |

---

## Then what

Part II builds the kernel of chapters 6 to 8 in Rust, and it begins at
[the type checker](../10-the-type-checker.md). [The guide](../README.md) holds
the whole order, part by part.

---

## Three pieces of advice, which this part follows

Three friends shaped this part. Their words, and what each one changed.

> "Aprende primero cómo funciona CoIC."
>
> Learn first how CoIC works.

So Part I is CoIC, in order, and no code of ours appears in it at all. The
theory comes first because every later decision quotes it.

> "¿Cómo funciona Lean4 con otros ejemplos de verlo?"
>
> How does Lean 4 work, with other ways of seeing it?

So each chapter shows its idea three ways, under a heading called **Three ways
to see it**. One metaphor, one analogy in a language you already use, and one
picture. If the first way does not land, the next one might. The four beats grew
out of this one sentence.

> "Se amable, porque siempre es bueno ser amable."
>
> Be kind, because it is always good to be kind.

So nothing here assumes you already know it. A hard part says that it is hard.
A question that catches everybody is answered rather than avoided, and
chapter 8, section 8.4 is the best example of that.
