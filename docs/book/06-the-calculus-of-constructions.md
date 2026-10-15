# 6. The Calculus of Constructions

> **Where you are.** Chapter 6 of 9 in Part I. This is the middle of the book
> and the centre of the theory.
>
> **Before this.** Chapters [1](01-a-proof-is-a-program.md) to
> [5](05-prop-type-and-sort.md). You need the term forms, substitution, the Pi
> type, and `Sort`.
>
> **This chapter adds** nothing new. It **assembles** the four chapters before
> it into a system with a name, and it shows you the whole system on one page.
>
> **The four beats.** The idea is section 6.1. The rule is sections 6.2 and
> 6.3, and this time the notation is the thing to learn. The code is section
> 6.7. Section 6.4 runs the rules by hand on the proof from chapter 1.
>
> **Do not skip ahead.** Chapter 7 extends this system. You cannot see what the
> extension buys until you have seen what the system lacks.

---

## 6.1 The idea

Four chapters have each added one piece. This chapter asks what the pieces add
up to, and the answer is a **specification**.

**The idea in one line.** A checker is a finite list of questions, and a
specification is the list of answers.

Here is what that means in practice. A checker walks a term. At every node it
asks one question: "what is the type of this?" The node is one of a handful of
shapes, so there is one answer per shape. Write the answers down and you are
done. There is no sixth answer hiding somewhere, and no appeal to judgment.

That list is the whole trusted part of a proof assistant. It fits on an index
card, and you are about to read it.

**Why it can be so short.** Count what the last four chapters gave you.

| From | You have |
|---|---|
| chapter 3 | a variable, a function, an application, and substitution |
| chapter 4 | the Pi type, `(x : A) → B` |
| chapter 5 | `Sort u`, and the `imax` rule |

That is four node shapes and one operation. Four shapes need four answers, and
one more answer ties the system to computation. Five rules.

Put a name on that collection. It is the **Calculus of Constructions**, CoC for
short. Coquand and Huet published it in 1988. Lean's kernel is this system plus
one extension, and chapter 7 is the extension.

---

## 6.2 The rule, as notation

This section teaches the notation and writes no rule. The next section writes
five.

**A judgment.** Everything a checker says has one shape, and the shape is
called a [judgment](../GLOSSARY.md#judgment).

```
Γ ⊢ e : A
```

Three parts, read right to left.

| The part | Say it | What it is in code |
|---|---|---|
| `e : A` | "the term `e` has the type `A`" | the question you are answering |
| `⊢` | "entails", or just "gives" | the body of your checker function |
| `Γ` | "gamma", the context | the argument that carries what you already know |

**A context.** `Γ` is a list of what is in scope.

```
Γ  =  x₁ : A₁,  x₂ : A₂,  ...,  xₙ : Aₙ
```

In logic, `Γ` is the list of hypotheses. In code, `Γ` is the
[local context](../GLOSSARY.md#local-context). They are the same list. You have
one in your editor right now, and your editor calls it the scope.

**An inference rule.** A rule is written as a fraction.

```
      the things that must hold
   ------------------------------
       the thing that follows
```

Read it: "if everything above the line holds, the thing below the line holds".
The line is not division. It is the word **therefore**.

In code a rule is one arm of a `match`. Above the line is what you recurse on.
Below the line is what you return.

```
   above the line  ─►  the recursive calls
   below the line  ─►  the value you return
```

**One worked reading, before any real rule.** Here is a rule about nothing, so
you can practise the shape:

```
   Γ ⊢ a : A      Γ ⊢ b : B
   ------------------------
      Γ ⊢ (a, b) : A × B
```

Say it aloud: "if `a` has type `A` in `Γ`, and `b` has type `B` in `Γ`, then the
pair has type `A × B` in `Γ`". Two recursive calls, one return. That is all a
rule ever is.

---

## 6.3 The five rules, on one page

This is the whole calculus. Read each one aloud once.

**A variable has the type that the context gives it.**

```
          x : A ∈ Γ
        -------------
          Γ ⊢ x : A
```

**A universe sits in the next universe up.**

```
        ----------------------------
          Γ ⊢ Sort u : Sort (u + 1)
```

**A function type is a type.**

```
   Γ ⊢ A : Sort u      Γ, x : A ⊢ B : Sort v
   -----------------------------------------
      Γ ⊢ (x : A) → B : Sort (imax u v)
```

**A function has a function type.**

```
    Γ ⊢ A : Sort u      Γ, x : A ⊢ b : B
    ------------------------------------
    Γ ⊢ fun (x : A) => b  :  (x : A) → B
```

**An application substitutes.**

```
   Γ ⊢ f : (x : A) → B      Γ ⊢ a : A
   ----------------------------------
         Γ ⊢ f a : B[x := a]
```

Five rules. That is the system that Lean's kernel is built on, and four of them
are one line of code each in a real checker.

Notice what each rule came from. Rule 1 is the context of section 6.2. Rule 2
is the tower of chapter 5, section 5.2. Rule 3 is `imax`, from chapter 5,
section 5.4. Rules 4 and 5 are the Pi type of chapter 4. Nothing is new.

### And one more, which chapter 8 earns

```
   Γ ⊢ e : A      A ≡ B      Γ ⊢ B : Sort u
   ----------------------------------------
                Γ ⊢ e : B
```

Read it: "a term keeps its type under computation". This is the
[conversion rule](../GLOSSARY.md#conversion-rule). The symbol `≡` means
[definitional equality](../GLOSSARY.md#definitional-equality), and chapter 8 is
entirely about it. Note the rule now, and do not worry about `≡` yet.

This sixth rule is the hinge of the whole design. It is the reason a proof
checker must hold an **evaluator** inside it.

---

## 6.4 A derivation, step by step

Take the proof from chapter 1 and check it with the five rules. The target:

```
fun (α : Prop) (h : α) => h        against        (α : Prop) → α → α
```

| Step | Rule | What it does |
|---|---|---|
| 1 | function | to check the outer `fun`, first check that `Prop` is a type |
| 2 | universe | `Prop` is `Sort 0`, so `Prop : Sort 1`. It is a type. |
| 3 | function | push `α : Prop` into `Γ`, and go into the body |
| 4 | variable | the body is the inner `fun`, so check that `α` is a type. `Γ` says `α : Prop`, which is `Sort 0`. |
| 5 | function | push `h : α` into `Γ`, and go into the body |
| 6 | variable | the body is `h`, and `Γ` says `h : α`. Done. |
| 7 | function | wrap up: the inner function has type `α → α` |
| 8 | function | wrap up again: the outer one has type `(α : Prop) → α → α` |
| 9 | — | compare with the target. They agree. |

Nine steps, and every one of them is one of the five rules. Nothing else
happened.

Read step 4 once more, because it is the quiet one. `α` is a **variable**, and
it is used as a **type**. That is legal here and nowhere in TypeScript. It is
legal because chapter 5 put `Prop` in a universe, so a variable may hold a type
the way a variable holds a number.

---

## 6.5 Three ways to see the calculus

**As a card.** Five rules fit on an index card. Carry the card, and you can
check any term of the core language by hand.

**As a tree.** Every accepted term has a
[derivation](../GLOSSARY.md#derivation) tree, like the table in section 6.4.
The checker builds that tree and throws it away. A proof of a proof, which
nobody needs to store.

**As a game.** One player writes a term. The other must justify every node with
a rule. There is no appeal to intuition and there is no "obviously". If no rule
applies, the term is refused.

---

## 6.6 What CoC cannot do

Here is the honest limit, and it is the reason chapter 7 exists.

The five rules give you `→` and `∀`. **That is all.** There is no `Nat`, no
`List`, no `Bool`, no `∧`, no `∨`, and no `=`.

You can get surprisingly far by encoding. The classical trick writes a number
as the function that repeats something that many times:

```
0  =  fun f x => x
1  =  fun f x => f x
2  =  fun f x => f (f x)
```

That works. It computes. And then it stops short in a way that matters: **you
cannot derive induction**. Nothing in the five rules lets you prove that every
number is either zero or a successor of a smaller one. Without induction, you
cannot prove that addition is commutative, and a proof assistant that cannot do
that is a toy.

So the system needs one extension. You declare a type by its constructors, and
the system hands you the induction principle. That extension turns CoC into
**CoIC**, the Calculus of Inductive Constructions, which is what Lean's kernel
actually implements.

---

### If you write TypeScript

**The five rules are a language specification that fits on a card.**
TypeScript has no such thing. The last published TypeScript specification is
version 1.8, dated January 2016, and Microsoft has not maintained it since. The
compiler is the definition, and the compiler is hundreds of thousands of lines.

That is not a complaint. It is a consequence of what `tsc` has to do: structural
subtyping, inference, overload resolution, declaration merging, control-flow
narrowing, and a type-level language of its own. None of that appears in the
five rules. Lean puts all of it in stage 3, the elaborator, which is
**untrusted**, and the kernel then reads the result with these five rules alone.

That split has a consequence you can feel:

| The job | In TypeScript | In Lean |
|---|---|---|
| decide that two types are equal | `tsc`, and you trust it | the kernel, with the rules of chapter 8 |
| infer an argument you did not write | `tsc`, and you trust it | the elaborator. The kernel re-checks the term it chose. |
| fill in a dependency, such as an Effect `Layer` | `tsc`, and you trust it | the elaborator. Same answer. |
| check generated code | `tsc` reads the generated file like any other | the same, and the kernel checks it again |

**Read the last row twice, because you already use the idea of this book.**
Generate TypeScript from an OpenAPI schema, or from a Prisma schema, or from a
GraphQL document. The generator may be wrong. You do not audit the generator.
You let `tsc` read its output, and a bad generator produces a file that fails
to compile. Lean takes that one step to the end of the road. Tactics, instance
search, implicit arguments, notation and macros are all allowed to be wrong.
The part that checks is small enough to read. Chapter 9 names that idea.

**A derivation is a trace you have seen.** `tsc` reports a deep type error and
prints the chain of positions that led to it. That chain is part of the tree of
section 6.4. Here the tree has five kinds of node, and nothing else.

---

## 6.7 Try it

The five rules are a function from a term to a type. Here are four of the five,
short enough to read in one sitting. Paste it into a TypeScript playground.

```ts
type E =
  | { k: "sort"; n: number }
  | { k: "fvar"; id: number }
  | { k: "app"; fun: E; arg: E }
  | { k: "lam"; id: number; ty: E; body: E }
  | { k: "forall"; id: number; ty: E; body: E }

type Ctx = Map<number, E>

const same = (a: E, b: E) => JSON.stringify(a) === JSON.stringify(b)

function infer(ctx: Ctx, e: E): E {
  switch (e.k) {
    // Rule one: a universe is a guest on the floor above.
    case "sort":
      return { k: "sort", n: e.n + 1 }
    // Rule two: a variable has the type the context gave it.
    case "fvar": {
      const ty = ctx.get(e.id)
      if (!ty) throw new Error(`variable ${e.id} is not in scope`)
      return ty
    }
    // Rule three: a function type is as high as its two halves.
    case "forall": {
      const u = infer(ctx, e.ty)
      const v = infer(new Map(ctx).set(e.id, e.ty), e.body)
      if (u.k !== "sort" || v.k !== "sort") throw new Error("not a type")
      // The `imax` of chapter 5 goes here. `max` is the predicative half.
      return { k: "sort", n: v.n === 0 ? 0 : Math.max(u.n, v.n) }
    }
    // Rule four: a function has a function type.
    case "lam": {
      const body = infer(new Map(ctx).set(e.id, e.ty), e.body)
      return { k: "forall", id: e.id, ty: e.ty, body }
    }
    // Rule five: an application needs the argument to fit.
    case "app": {
      const fn = infer(ctx, e.fun)
      if (fn.k !== "forall") throw new Error("this is not a function")
      const arg = infer(ctx, e.arg)
      if (!same(fn.ty, arg)) throw new Error("the argument does not fit")
      return fn.body
    }
  }
}
```

Now run section 6.4 through it. The proof of "A implies A" is a lambda whose
body is its own argument:

```ts
const prop: E = { k: "sort", n: 0 }
const a: E = { k: "fvar", id: 1 }
const proof: E = { k: "lam", id: 1, ty: prop, body: { k: "lam", id: 2, ty: a, body: { k: "fvar", id: 2 } } }
console.log(JSON.stringify(infer(new Map(), proof)))
```

Then break it. Change the inner body to `{ k: "fvar", id: 1 }` and the type
changes with it, so the claim and the proof no longer agree. Change `app` to
pass the wrong argument and rule five throws: "the argument does not fit". Rule
five is where every wrong proof dies.

**What this version leaves out, and it matters.** `same` compares two types as
data. The real rule five does not. It asks whether the two types are equal **by
computation**, which may mean running a program, and that is
[chapter 8](08-definitional-equality.md). Substitution is missing too, because
this version keeps a variable as an identifier rather than as an index. Those
two gaps are the difference between fifty lines and a kernel.

---

## 6.8 Check yourself

1. Name the five rules, from memory, by what each one is **about**.
2. Which rule needs substitution, and why?
3. Why is "declare a type by its constructors" not something you can build out
   of the five rules?

### Answers

1. A variable, a universe, a function type, a function, and an application.
2. The application rule. The type of the result mentions the argument, so the
   argument value has to go into the type. Chapter 4, section 4.3.
3. Because the five rules build only functions and function types. Induction is
   an extra principle, and nothing in the five rules proves it. Chapter 7 adds
   it as a declaration that the kernel understands.

---

## 6.9 References

- Coquand and Huet, *The Calculus of Constructions*, 1988. The system of this
  chapter. DOI [10.1016/0890-5401(88)90005-3](https://doi.org/10.1016/0890-5401%2888%2990005-3)
- Harper, *Practical Foundations for Programming Languages*, chapters 1 and 2,
  for a judgment and an inference rule taught as notation.
  <https://www.cs.cmu.edu/~rwh/pfpl.html>
- Nederpelt and Geuvers, *Type Theory and Formal Proof*, chapter 8, for λC,
  which is the system of this chapter.
  <https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C>
- Barendregt, *Introduction to generalized type systems*, 1991, for where CoC
  sits among the other typed calculi.
  DOI [10.1017/S0956796800020025](https://doi.org/10.1017/S0956796800020025)
- Coquand, *An algorithm for type-checking dependent types*, 1996, for the
  shape every real checker uses.
  DOI [10.1016/0167-6423(95)00021-6](https://doi.org/10.1016/0167-6423%2895%2900021-6)
- The TypeScript specification, version 1.8 of January 2016, and the open issue
  that asks what became of it.
  <https://github.com/microsoft/TypeScript/issues/21477>
- Carneiro, *The Type Theory of Lean*, for these rules as Lean states them.
  <https://github.com/digama0/lean-type-theory>

---

**Next:** [7. Inductive types, and the I in CoIC](07-inductive-types.md)
