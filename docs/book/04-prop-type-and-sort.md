# 4. Prop, Type, and Sort

> **Where you are.** Chapter 4 of 8 in Part I.
>
> **Before this.** Chapter [3](03-types-that-depend-on-values.md). You need the
> Pi type, because the rule in section 4.4 is a rule about Pi types.
>
> **This chapter adds** the last term form of the core language, and the answer
> to "what is the type of a type".
>
> **Do not skip ahead.** Chapter 5 writes the rules of the calculus, and three
> of the five rules mention `Sort`.

---

## 4.1 The question

Every term has a type. So what is the type of `Nat`?

```lean
#check Nat        -- Nat : Type
#check Type       -- Type : Type 1
#check Type 1     -- Type 1 : Type 2
```

A type has a type, and that type has a type. The question is where it stops,
and the answer is that **it does not stop**. There is a tower, and it is
infinite.

It has to be infinite. If `Type : Type` held, you could prove `False`. That
result has a name, Girard's paradox, and the reference is at the end.

---

## 4.2 One former, two names

The kernel has **one** universe former, and it takes a number.

```
Sort u
```

`Prop` and `Type` are not in the kernel at all. They are names for two parts of
`Sort`, and the parser puts them in.

```
Prop     =  Sort 0
Type     =  Sort 1
Type n   =  Sort (n + 1)
```

Lean will tell you itself:

```lean
#check Sort 0     -- Prop : Type
#check Sort 1     -- Type : Type 1
```

Read the first line again. You asked about `Sort 0` and Lean answered about
`Prop`. They are one term, printed two ways.

Watch the step of one. `Type` is `Sort 1`, and not `Sort 0`. `Prop` took the
ground floor.

One rule builds the whole tower:

```
Sort u : Sort (u + 1)
```

---

## 4.3 There is no floor below `Prop`

Here is the question that catches everybody, and it is a good question.

`rfl` proves `2 = 2`. And `2 = 2 : Prop`, which is `Sort 0`. So does `rfl` live
at `Sort -1`?

No. Try the same reasoning somewhere familiar:

```
3 : Nat          and      Nat : Type
```

By the same step, `3 : Sort 0`. But `3` is plainly not a universe.

The hidden assumption is that every colon step drops one universe. It does not.
Only two kinds of term are a `Sort`. Everything else is an **element of** a
`Sort`, and an element gets no level of its own.

Count the rungs instead.

```
             Type  =  Sort 1                 read ↑ as "is an element of"
               ↑
      Prop            Nat
        ↑               ↑
 2 = 2   True        0   1   2
   ↑       ↑
  rfl   trivial       nothing
```

- `Nat` has **two** rungs. The type, then its elements.
- `Prop` has **three**. The universe, then propositions, then proofs.

`Prop` is the only small universe, and the third rung is the whole difference.
When a term confuses you, ask one question: **how many rungs are below it?**

---

## 4.4 Why `Prop` is special, in three ways

The numbers are not the real difference. These three are.

### 1. `Prop` is impredicative

The rule for a Pi type does not use `max`. It uses `imax`.

```
   A : Sort u      B : Sort v
   -------------------------------
   (x : A) → B  :  Sort (imax u v)
```

And `imax` has one special case.

```
imax u 0  =  0
imax u v  =  max u v      when v is not 0
```

So if the **result** is a proposition, the whole function type is a
proposition, whatever the size of the domain is. Lean agrees:

```lean
#check ∀ (p : Prop), p → p      -- ∀ (p : Prop), p → p : Prop
#check ∀ (α : Type 9), α = α    -- ∀ (α : Type 9), α = α : Prop
```

Read the first line once more. The term speaks about **every** proposition, and
the term is itself a proposition. So it speaks about a collection that holds
it. The word for that self-reference is **impredicative**.

One trap, and Lean prints the trap for you:

```lean
#check ∀ (α : Type 9), α → α    -- (α : Type 9) → α → α : Type 10
```

That one is **not** a `Prop`. The body `α → α` sits at level 10, not at 0, so
`imax` has nothing to collapse. A large domain alone proves nothing. The body
is what matters.

`Type` works the other way. A Pi type over `Type u` lands in `Type (max u v)`,
so the level grows. `Type` is **predicative**.

One warning for a reader who knows Rocq. Lean has **no cumulativity**. `Type 0`
is not a subtype of `Type 1`. Lean uses universe polymorphism instead, which
chapter 6 meets as the level arguments on a constant.

### 2. All proofs of one proposition are equal

If `P : Prop` and `h₁ : P` and `h₂ : P`, then the kernel treats `h₁` and `h₂`
as the same term. The name is **proof irrelevance**, and you can watch it work:

```lean
example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl
```

That is accepted. The same line with `Nat` in place of `p` is refused, and it
should be. `0` and `1` are different numbers.

Why the rule exists: you care **that** a proposition holds, never **how**.

### 3. A proof cannot give data back

An inductive type in `Prop` may only eliminate into `Prop`. A narrow exception
exists for a type with at most one element.

Why the rule exists: it lets the compiler **erase** every proof. A proof costs
nothing when the program runs.

```lean
def firstOr0 (xs : List Nat) (h : xs ≠ []) : Nat := ...
```

Two arguments go in. In the compiled program only `xs` exists. The proof is
gone, and nothing is lost, because of rule 2.

### The summary

| | `Prop` | `Type u` |
|---|---|---|
| is | `Sort 0` | `Sort (u+1)` |
| holds | propositions | data |
| the Pi rule | `imax`, so it stays at 0 | `max`, so it grows |
| all elements equal | yes | no |
| may give data back | no | yes |
| survives at run time | no | yes |

---

## 4.5 Prop is not Bool

This is the most common confusion, and it is worth one section.

```lean
#reduce Not False      -- ¬False
```

`Not` is not a truth table. It is a function that **builds** a proposition:

```
Not  =  fun (p : Prop) => p → False
```

So `Not False` is the proposition `False → False`. Is it true? It is true when
something inhabits it, and something does:

```lean
example : False → False := fun h => h
```

So `Not False` is a **true proposition**, and it is **not the term `True`**.
Both statements hold at once, and nothing is wrong.

| | `Bool` | `Prop` |
|---|---|---|
| what it is | an inductive type with two constructors | `Sort 0`, a kernel primitive |
| how many elements | 2 | infinitely many |
| pattern match on it | yes | no. There are no constructors. |
| `not false` or `Not False` | computes to `true` | stays a proposition |

The road from one to the other is `Decidable`, which has type `Prop → Type`. It
is data that somebody wrote, and `decide` uses it:

```lean
#eval decide (2 = 2)      -- true
```

---

## 4.6 Try it

```sh
devbox run -- cargo run -p rean -- prove
devbox run -- cargo test -p rean_kernel --test universes
```

The `prove` output ends with a line that is this chapter in one number:

```text
the proposition lives in : Prop
```

The checker computed `imax 1 0`, got `0`, and printed the name for `Sort 0`.

---

## 4.7 Check yourself

1. Why must the tower of universes be infinite?
2. `∀ (α : Type 9), α = α` is a `Prop`. `∀ (α : Type 9), α → α` is not. Why?
3. A compiled Lean program never carries a proof. Which of the three
   differences makes that safe?

### Answers

1. Because `Sort u : Sort u` lets you prove `False`. Girard's paradox.
2. `imax` collapses only when the **body** is at level 0. In the first, the body
   `α = α` is a `Prop`. In the second, the body `α → α` sits at level 10.
3. Rule 2, proof irrelevance. All proofs of one proposition are equal, so a
   proof carries no information that anybody could lose.

---

## 4.8 References

- Girard's paradox, for why `Type : Type` is fatal. Carneiro, *The Type Theory
  of Lean*, states the rules Lean uses to avoid it.
  <https://github.com/digama0/lean-type-theory>
- Harper and Pollack, *Type checking with universes*, 1991, for levels as
  variables. DOI [10.1016/0304-3975(90)90108-T](https://doi.org/10.1016/0304-3975%2890%2990108-T)
- Gilbert, Cockx, Sozeau and Tabareau, *Definitional proof-irrelevance without
  K*, 2019, for what rule 2 costs a checker.
  DOI [10.1145/3290316](https://doi.org/10.1145/3290316)
- Rocq, `SProp`, for a system that keeps proof irrelevance in a separate sort.
  <https://rocq-prover.org/doc/master/refman/addendum/sprop.html>
- Our code. `crates/rean_kernel/src/level.rs` holds the five level formers, and
  `crates/rean_kernel/tests/universes.rs` holds this chapter as tests.

---

**Next:** [5. The Calculus of Constructions](05-the-calculus-of-constructions.md)
