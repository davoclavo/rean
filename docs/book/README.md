# Part I — How Lean 4 works, from the ground up

Eight short chapters. Read them in order. Each one adds exactly one idea, and
every chapter after it uses that idea.

No mathematics is assumed. If you can read a function signature, you can read
this. Where a chapter uses an example, the example is Lean, Rust, or
TypeScript, and the output shown is real output.

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

So each chapter has a **Three ways to see it** section. One metaphor, one
analogy in a language you already use, and one picture. If the first way does
not land, the next one might.

> "Se amable, porque siempre es bueno ser amable."
>
> Be kind, because it is always good to be kind.

So nothing here assumes you already know it. A hard part says that it is hard.
A question that catches everybody is answered rather than avoided, and
chapter 7, section 7.4 is the best example of that.
