# 3. Types that depend on values

> **Where you are.** Chapter 3 of 8 in Part I.
>
> **Before this.** Chapters [1](01-a-proof-is-a-program.md) and
> [2](02-terms-and-binders.md). You need a term, a binder, and substitution.
>
> **This chapter adds** the function type that chapter 1 promised, the one that
> can speak about its own argument.
>
> **Do not skip ahead.** This is the step where Lean leaves every mainstream
> language behind. Chapter 7 exists because of this chapter.

---

## 3.1 The question

A normal function type says nothing about values.

```
Nat → Nat
```

It promises a number in and a number out. It cannot promise that the output is
larger than the input, or that a list keeps its length.

Now look at a real Lean signature. It is from the library, and this is the
output of `#check @Vector.push`:

```text
@Vector.push : {α : Type u_1} → {n : Nat} → Vector α n → α → Vector α (n + 1)
```

Read the end of it. The result type is `Vector α (n + 1)`, and `n` is an
**argument of the function**. The type of the result is computed from a value
that arrives at run time.

That is a dependent type. It is the whole chapter.

---

## 3.2 The new form

Write it like this.

```
(x : A) → B
```

Read it: "give me an `x` of type `A`, and I give you a `B`, and `B` may mention
`x`".

The name for this form is a **Pi type**. Two spellings of it hide in plain
sight.

- When `B` ignores `x`, people write `A → B`. The arrow is the short form.
- When `A` is a proposition, people write `∀ x : A, B`.

**Those are the same term form.** Not two forms that behave alike. One form.
Lean has one node for it, and so does our checker. Every `→` you have ever
written in Lean is a Pi type whose body ignores its binder.

That single fact is why the language of chapter 2 stays so small.

---

## 3.3 Three ways to see it

**As a promise that does arithmetic.** `push` does not only return a vector. It
returns a vector whose length is one more than the one it got. The type carries
the arithmetic, so the compiler checks the arithmetic.

**As a family.** Think of `Vector Nat` as a shelf of boxes, one per length.
`Vector Nat 3` is one box. A dependent function picks a box by the value you
give it. The type is a function from values to types, and Lean says so:

```text
#check fun (n : Nat) => Vector Nat n
fun n => Vector Nat n : Nat → Type
```

Read that output. `Nat → Type`. An ordinary function, and its results are
types.

**As the thing your language almost has.** Every mainstream language reaches for
this and stops short.

| Language | How far it gets | Where it stops |
|---|---|---|
| Rust | `[T; N]`, a length in the type | `N` must be known when the program is built |
| C++ | a template parameter | the same. No run-time value may enter a type. |
| TypeScript | a literal type, such as `"GET"` | types are erased and no arithmetic follows a value |
| Lean | `Vector α n`, for any `n` | nothing. `n` may arrive at run time. |

Keep the Rust row in mind. Rust can say "an array of 3". It cannot say "an array
whose length is the number this function returns".

---

## 3.4 What it costs

Here is the application rule, in words. You will see it again in chapter 5 as a
rule of the calculus.

```
if   f : (x : A) → B      and   a : A
then f a : B[x := a]
```

Look at the last line. The type of `f a` is **`B` with the argument
substituted into it**. The substitution of chapter 2, section 2.3, now runs
inside types.

So a checker for dependent types has to do something that no C compiler ever
does: it has to compute with values while it checks types. Ask whether
`Vector α (2 + 1)` and `Vector α 3` are the same type, and somebody has to add
two and one.

**That somebody is the kernel.** Chapter 7 is about exactly this, and
[Part V of the guide](../README.md) is about what it costs in seconds.

---

## 3.5 Try it

Each line below is real, and the output is what Lean prints.

```lean
#check @Vector.push
-- {α : Type u_1} → {n : Nat} → Vector α n → α → Vector α (n + 1)

def repeatN (α : Type) (a : α) : (n : Nat) → Vector α n
  | 0 => #v[]
  | n + 1 => (repeatN α a n).push a

#check @repeatN
-- (α : Type) → α → (n : Nat) → Vector α n
```

Read the type of `repeatN`. It takes a number and gives back a vector of that
length. The type checker already knows the length is right. There is no test to
write for it.

---

## 3.6 Check yourself

1. `A → B` is the short form of what?
2. Why can a Rust array length not do what `Vector α n` does?
3. The type of `f a` is `B[x := a]`. Which chapter 2 operation is that?

### Answers

1. `(x : A) → B`, where `B` does not mention `x`. One term form, two spellings.
   `∀` is the third spelling.
2. Because Rust needs the length when it builds the program. A Lean `n` may be
   a value that only exists while the program runs.
3. Substitution, from section 2.3. The one operation. Now it runs in types as
   well as terms.

---

## 3.7 References

- *Theorem Proving in Lean 4*, on dependent function types.
  <https://lean-lang.org/theorem_proving_in_lean4/>
- *The Lean Language Reference*, the type system, for the official rules.
  <https://lean-lang.org/doc/reference/latest/The-Type-System/>
- Dybjer, *Inductive families*, 1994, for the idea of a type indexed by a
  value. DOI [10.1007/BF01211308](https://doi.org/10.1007/BF01211308)
- Brady, *Idris 2: Quantitative Type Theory in Practice*, 2021, for another
  language built on this form.
  DOI [10.4230/LIPIcs.ECOOP.2021.9](https://doi.org/10.4230/LIPIcs.ECOOP.2021.9)
- Our code. `crates/rean_kernel/src/expr.rs` holds the one node, named
  `Forall`.

---

**Next:** [4. Prop, Type, and Sort](04-prop-type-and-sort.md)
