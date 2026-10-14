# 5. The Calculus of Constructions

> **Where you are.** Chapter 5 of 8 in Part I. This is the middle of the book
> and the centre of the theory.
>
> **Before this.** Chapters [1](01-a-proof-is-a-program.md) to
> [4](04-prop-type-and-sort.md). You need the term forms, substitution, the Pi
> type, and `Sort`.
>
> **This chapter adds** nothing new. It **assembles** the four chapters before
> it into a system with a name, and it shows you the whole system on one page.
>
> **The four beats.** The idea is section 5.1. The notation is section 5.2,
> and this time the notation is the thing to learn. Section 5.3 is the five
> rules. Section 5.4 runs them on the proof from chapter 1.
>
> **Do not skip ahead.** Chapter 6 extends this system. You cannot see what the
> extension buys until you have seen what the system lacks.

---

## 5.1 The idea

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
| chapter 2 | a variable, a function, an application, and substitution |
| chapter 3 | the Pi type, `(x : A) → B` |
| chapter 4 | `Sort u`, and the `imax` rule |

That is four node shapes and one operation. Four shapes need four answers, and
one more answer ties the system to computation. Five rules.

Put a name on that collection. It is the **Calculus of Constructions**, CoC for
short. Coquand and Huet published it in 1988. Lean's kernel is this system plus
one extension, and chapter 6 is the extension.

---

## 5.2 The notation

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

## 5.3 The five rules, on one page

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

Notice what each rule came from. Rule 1 is the context of section 5.2. Rule 2
is the tower of chapter 4, section 4.2. Rule 3 is `imax`, from chapter 4,
section 4.4. Rules 4 and 5 are the Pi type of chapter 3. Nothing is new.

### And one more, which chapter 7 earns

```
   Γ ⊢ e : A      A ≡ B      Γ ⊢ B : Sort u
   ----------------------------------------
                Γ ⊢ e : B
```

Read it: "a term keeps its type under computation". This is the
[conversion rule](../GLOSSARY.md#conversion-rule). The symbol `≡` means
[definitional equality](../GLOSSARY.md#definitional-equality), and chapter 7 is
entirely about it. Note the rule now, and do not worry about `≡` yet.

This sixth rule is the hinge of the whole design. It is the reason a proof
checker must hold an **evaluator** inside it.

---

## 5.4 A derivation, step by step

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
legal because chapter 4 put `Prop` in a universe, so a variable may hold a type
the way a variable holds a number.

---

## 5.5 Three ways to see the calculus

**As a card.** Five rules fit on an index card. Carry the card, and you can
check any term of the core language by hand.

**As a tree.** Every accepted term has a
[derivation](../GLOSSARY.md#derivation) tree, like the table in section 5.4.
The checker builds that tree and throws it away. A proof of a proof, which
nobody needs to store.

**As a game.** One player writes a term. The other must justify every node with
a rule. There is no appeal to intuition and there is no "obviously". If no rule
applies, the term is refused.

---

## 5.6 What CoC cannot do

Here is the honest limit, and it is the reason chapter 6 exists.

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
| decide that two types are equal | `tsc`, and you trust it | the kernel, with the rules of chapter 7 |
| infer an argument you did not write | `tsc`, and you trust it | the elaborator. The kernel re-checks the term it chose. |
| fill in a dependency, such as an Effect `Layer` | `tsc`, and you trust it | the elaborator. Same answer. |
| check generated code | `tsc` reads the generated file like any other | the same, and the kernel checks it again |

**Read the last row twice, because you already use the idea of this book.**
Generate TypeScript from an OpenAPI schema, or from a Prisma schema, or from a
GraphQL document. The generator may be wrong. You do not audit the generator.
You let `tsc` read its output, and a bad generator produces a file that fails
to compile. Lean takes that one step to the end of the road. Tactics, instance
search, implicit arguments, notation and macros are all allowed to be wrong.
The part that checks is small enough to read. Chapter 8 names that idea.

**A derivation is a trace you have seen.** `tsc` reports a deep type error and
prints the chain of positions that led to it. That chain is part of the tree of
section 5.4. Here the tree has five kinds of node, and nothing else.

---

## 5.7 Try it

Run the proof of section 5.4 and read the output against the rules.

```sh
devbox run -- cargo run -p rean -- prove
devbox run -- cargo test -p rean_kernel --test typeck
```

Then try a wrong proof. The checker refuses it and prints both types:

```text
rejected:
  type mismatch for `fun (α : Prop) => fun (β : Prop) => fun (h : α) => h`
    expected: (α : Prop) → (β : Prop) → α → β
    got     : (α : Prop) → Prop → α → α
```

The term proves `α → α`. The claim asked for `α → β`. Rule five had nothing to
match, so the answer is no.

---

## 5.8 Check yourself

1. Name the five rules, from memory, by what each one is **about**.
2. Which rule needs substitution, and why?
3. Why is "declare a type by its constructors" not something you can build out
   of the five rules?

### Answers

1. A variable, a universe, a function type, a function, and an application.
2. The application rule. The type of the result mentions the argument, so the
   argument value has to go into the type. Chapter 3, section 3.3.
3. Because the five rules build only functions and function types. Induction is
   an extra principle, and nothing in the five rules proves it. Chapter 6 adds
   it as a declaration that the kernel understands.

---

## 5.9 References

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
- Our code. `crates/rean_kernel/src/typeck.rs` holds one arm per rule, and
  [the type checker chapter](../09-the-type-checker.md) walks through it line
  by line.

---

**Next:** [6. Inductive types, and the I in CoIC](06-inductive-types.md)
