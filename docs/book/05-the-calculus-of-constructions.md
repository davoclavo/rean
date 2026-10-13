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
> **Do not skip ahead.** Chapter 6 extends this system. You cannot see what the
> extension buys until you have seen what the system lacks.

---

## 5.1 What you already have

Count what the last four chapters gave you.

| From | You have |
|---|---|
| chapter 2 | a variable, a function, an application, and substitution |
| chapter 3 | the Pi type, `(x : A) → B` |
| chapter 4 | `Sort u`, and the `imax` rule |

Put a name on that collection. It is the **Calculus of Constructions**, CoC for
short. Coquand and Huet published it in 1988. Lean's kernel is this system plus
one extension, and chapter 6 is the extension.

---

## 5.2 How a rule is written

Everything a checker says has one shape.

```
Γ ⊢ e : A
```

Read it: "in the context `Γ`, the term `e` has the type `A`". The context is a
list of what you already know.

```
Γ  =  x₁ : A₁,  x₂ : A₂,  ...,  xₙ : Aₙ
```

In logic, `Γ` is the list of hypotheses. In code, `Γ` is the local context. They
are the same list.

A rule is a fraction. Read it as: "if everything above the line holds, the thing
below the line holds".

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

### And one more, which chapter 7 earns

```
   Γ ⊢ e : A      A ≡ B      Γ ⊢ B : Sort u
   ----------------------------------------
                Γ ⊢ e : B
```

Read it: "a term keeps its type under computation". The symbol `≡` means "the
same by computation", and chapter 7 is entirely about it. Note the rule now, and
do not worry about `≡` yet.

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
it is used as a **type**. That is legal here and nowhere in C or Rust. It is
legal because chapter 4 put `Prop` in a universe, so a variable may hold a type
the way a variable holds a number.

---

## 5.5 Three ways to see the calculus

**As a card.** Five rules fit on an index card. Carry the card, and you can
check any term of the core language by hand.

**As a tree.** Every accepted term has a derivation tree, like the table in
section 5.4. The checker builds that tree and throws it away. A proof of a
proof, which nobody needs to store.

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
   argument value has to go into the type. Chapter 3, section 3.4.
3. Because the five rules build only functions and function types. Induction is
   an extra principle, and nothing in the five rules proves it. Chapter 6 adds
   it as a declaration that the kernel understands.

---

## 5.9 References

- Coquand and Huet, *The Calculus of Constructions*, 1988. The system of this
  chapter. DOI [10.1016/0890-5401(88)90005-3](https://doi.org/10.1016/0890-5401%2888%2990005-3)
- Barendregt, *Introduction to generalized type systems*, 1991, for where CoC
  sits among the other typed calculi.
  DOI [10.1017/S0956796800020025](https://doi.org/10.1017/S0956796800020025)
- Coquand, *An algorithm for type-checking dependent types*, 1996, for the
  shape every real checker uses.
  DOI [10.1016/0167-6423(95)00021-6](https://doi.org/10.1016/0167-6423%2895%2900021-6)
- Carneiro, *The Type Theory of Lean*, for these rules as Lean states them.
  <https://github.com/digama0/lean-type-theory>
- Our code. `crates/rean_kernel/src/typeck.rs` holds one arm per rule, and
  [the type checker chapter](../09-the-type-checker.md) walks through it line
  by line.

---

**Next:** [6. Inductive types, and the I in CoIC](06-inductive-types.md)
