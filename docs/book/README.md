# Part I — How Lean 4 works, from the ground up

Eight short chapters. Read them in order. Each one adds exactly one idea, and
every chapter after it uses that idea.

No mathematics is assumed. **If you can read a TypeScript signature, you can
read this.** The examples come from TypeScript, from Effect, and from Lean, and
every output shown is real output.

---

## The four beats

This part has one method, and it repeats in every section. The order is always
the same, and it never starts with a formula.

```
  1. the idea       ──►  2. in your language  ──►  3. the notation  ──►  4. in Lean
  words and a            TypeScript or             the rule,             real Lean,
  picture                Effect                    written down          real output
```

| Beat | What it gives you | How to read it |
|---|---|---|
| **1. The idea** | the concept, in plain words, with a picture or a metaphor | slowly. If this beat does not land, the next three will not. |
| **2. In your language** | the nearest thing you already use | fast. You know this one. |
| **3. The notation** | the rule or the equation, with every symbol named | once aloud. The symbols are short names for beat 1. |
| **4. In Lean** | the real syntax, and the output Lean prints | at the keyboard. Run it. |

Why this order. A formula is a compression of an idea, so it only reads as a
formula once you hold the idea. Lean syntax is a compression of the formula.
Start at the compressed end and you memorise shapes. Start at the idea and you
keep the whole chain.

A beat carries a label where the text could be mistaken for the other kind.
Elsewhere the order alone carries it.

---

## The rule of this part

**One idea per chapter, and no chapter stands alone.**

```
1. a proof is a program
      │
      ▼
2. terms and binders ──────────► the language, and substitution
      │
      ▼
3. types that depend on values ─► the Pi type
      │
      ▼
4. Prop, Type, and Sort ───────► the universes, and imax
      │
      ▼
5. the Calculus of Constructions ─► all of the above, as five rules
      │
      ▼
6. inductive types ────────────► CoC becomes CoIC. Data, logic, induction.
      │
      ▼
7. definitional equality ──────► the rule that makes a checker an evaluator
      │
      ▼
8. what you must trust ────────► the whole machine, and the one hole in it
```

If a chapter feels hard, the chapter before it holds the missing piece. That is
the design, not an accident.

Chapters 2, 3 and 4 each add one axis to the language, and chapter 5 names the
system that the three axes make. That staircase is not ours. Nederpelt and
Geuvers climb the same one, and the table below says where every part of this
method comes from.

---

## The chapters

| # | Chapter | It answers |
|---|---|---|
| 1 | [A proof is a program](01-a-proof-is-a-program.md) | why a type checker and a proof checker are one program |
| 2 | [Terms, binders, and names you do not need](02-terms-and-binders.md) | what a term is, and why a bound variable is a number |
| 3 | [Types that depend on values](03-types-that-depend-on-values.md) | how a type can speak about a value, and why no mainstream language does |
| 4 | [Prop, Type, and Sort](04-prop-type-and-sort.md) | what the type of a type is, and what makes `Prop` special |
| 5 | [The Calculus of Constructions](05-the-calculus-of-constructions.md) | the five rules, on one page, and what they cannot do |
| 6 | [Inductive types, and the I in CoIC](06-inductive-types.md) | where numbers, lists, `and`, `or` and `=` come from |
| 7 | [Definitional equality](07-definitional-equality.md) | when two terms are the same, and why `rfl` sometimes refuses |
| 8 | [What you must trust](08-what-you-must-trust.md) | the five stages, the axioms, and why a second kernel exists |

Each chapter ends with a **Check yourself** section, with answers. Those three
questions are the gate. If you can answer them, go on.

Each chapter also has an **If you write TypeScript** section. Beat 2 is the
short hook inside a section. That section is the long form, and it holds the
table of what your language can do, what it cannot, and why. It names `never`,
`unknown`, a conditional type, a discriminated union, a lookup type, the `tsc`
error `TS2589`, and the three channels of `Effect<A, E, R>`.

Every mathematical term links to its definition in
[the glossary](../GLOSSARY.md), so the right word is used and the word is never
only a word.

---

## Where this method comes from

Seven books teach this material, and no two of them open the same way. We read
how each one is built and took one thing from each.

| Book | How it opens | What this part took |
|---|---|---|
| *Theorem Proving in Lean 4* | the type theory first, and the logic second | the order of the ideas, and `#check` as the way to ask Lean a question |
| *Functional Programming in Lean* | a program that runs on page one. The proofs arrive as an interlude. | a `Try it` section in every chapter, with a command you can run |
| *The Little Typer* | one tiny language, one question at a time, and the answer beside it | **Check yourself**, and the rule that a chapter adds one idea |
| *Software Foundations* | short chapters, and every claim in the text is machine-checked | `tools/cite.py`, which fails the build when a chapter names a test nobody wrote |
| Nederpelt and Geuvers, *Type Theory and Formal Proof* | one axis of the Barendregt cube per chapter, from the untyped calculus up | chapters 2, 3 and 4, which add one axis each, and chapter 5, which names the result |
| Harper, *Practical Foundations for Programming Languages* | a judgment and an inference rule, named as notation **before** any rule uses them | section 5.2, which teaches the fraction bar before section 5.3 writes five of them |
| Carneiro, *The Type Theory of Lean* | the rules, as rules, with no prose at all | the reference list at the end of each chapter. This is where a claim is settled. |

One thing none of them does, and this part does. **Every chapter points at a
second implementation.** The `Try it` command runs our checker, in Rust, on the
same file that Lean wrote. An idea you have watched a second program agree with
is an idea you can trust.

---

## How long it takes

| You have | Read |
|---|---|
| 20 minutes | chapter 1, and run its `Try it` |
| one evening | chapters 1 to 5. That is the Calculus of Constructions. |
| two evenings | all eight. That is CoIC, which is what Lean's kernel implements. |

---

## Then what

Part II builds the kernel of chapters 5 to 7 in Rust, and it begins at
[the type checker](../09-the-type-checker.md). [The guide](../README.md) holds
the whole order, part by part.

---

## Three pieces of advice, which this part follows

Three friends shaped this part. Their words, and what each one changed.

> "Aprende primero cómo funciona CoIC."
>
> Learn first how CoIC works.

So Part I is CoIC, in order, and no code of ours appears until chapter 5 has
the rules. The theory comes first because every later decision quotes it.

> "¿Cómo funciona Lean4 con otros ejemplos de verlo?"
>
> How does Lean 4 work, with other ways of seeing it?

So each chapter shows its idea three ways, under a heading called **Three ways
to see it**. One metaphor, one analogy in a language you already use, and one
picture. If the first way does not land, the next one might. The four beats
grew out of this one sentence.

> "Se amable, porque siempre es bueno ser amable."
>
> Be kind, because it is always good to be kind.

So nothing here assumes you already know it. A hard part says that it is hard.
A question that catches everybody is answered rather than avoided, and
chapter 7, section 7.4 is the best example of that.
