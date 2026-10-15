# 5. Prop, Type, and Sort

> **Where you are.** Chapter 5 of 9 in Part I.
>
> **Before this.** Chapter [4](04-types-that-depend-on-values.md). You need the
> Pi type, because the rule in section 5.4 is a rule about Pi types.
>
> **This chapter adds** the last term form of the core language, and the answer
> to "what is the type of a type".
>
> **The four beats.** The idea is section 5.1. The rule is section 5.2, and the
> data is at the end of it. The code is section 5.6. Sections 5.3 to 5.5 are
> the three hard parts, and each one takes the same beats again.
>
> **Do not skip ahead.** Chapter 6 writes the rules of the calculus, and three
> of the five rules mention `Sort`.

---

## 5.1 The idea

Chapter 4 ended on one sentence. **A type is the result of a function from
values to types.**

Read it again and a question falls out. If a type can be the **result** of a
function, a type is a value. And every value has a type. So what is the type of
a type?

**The idea in one line.** Put types and values in **one** world, and then stop
that world from eating itself.

That is the whole chapter. The first half is the reason Lean is powerful. The
second half is the reason Lean needs a tower.

**Why one world.** In your editor there are two worlds. `const x = 1` lives in
the value world. `type X = number` lives in the type world. They never meet,
and `tsc` deletes the second world before the program runs. Chapter 4 broke the
wall down. A Lean type may hold a value, so a Lean type **is** a value, and
there is one world.

**Why a tower.** One world has a danger in it. If every type is a value, and
every value has a type, then something has to be the type of everything,
including itself. A collection that holds itself is where paradoxes live. The
cure is to refuse the self-reference and stack the levels instead.

```
   ...                 floor 3
    ↑
   a type of types     floor 2
    ↑
   a type              floor 1
    ↑
   a value             the ground
```

### Three ways to see it

**A hotel with no top floor.** Every guest lives on a floor, and every floor is
itself a guest on the floor above. There is no penthouse, because a penthouse
would have to be a guest in itself.

**A rule against self-reference.** The tower has to be infinite. A top floor
would be a type of all types, including itself, and from that you can prove
anything. That result has a name, Girard's paradox, and the reference is at the
end.

**A kind system with numbers in it.** You know a kind already. In TypeScript a
type lives in one layer and a value in another, and the layers are fixed. Lean
has the same idea with no ceiling. The layer is a number, the number is a
parameter you can write, and a declaration may be
[polymorphic](../GLOSSARY.md#universe-polymorphism) in it.

---

## 5.2 The rule, which is one former with two names

The kernel has **one** universe former, [`Sort u`](../GLOSSARY.md#sort), and it
takes a number. The number is a
[universe level](../GLOSSARY.md#universe-level), and it is the floor.

```
Sort u
```

One rule builds the whole tower.

```
Sort u : Sort (u + 1)
```

Read it: "floor `u` is a guest on floor `u + 1`". That is the picture of
section 5.1 as one line.

`Prop` and `Type` are not in the kernel at all. They are names for two parts of
`Sort`, and the parser puts them in.

```
Prop     =  Sort 0
Type     =  Sort 1
Type n   =  Sort (n + 1)
```

Watch the step of one. `Type` is `Sort 1`, and not `Sort 0`. `Prop` took the
ground floor, and section 5.3 is why that matters.

**The data.** In the types of [chapter 2](02-every-type-the-kernel-has.md)
there is one node, `sort`, and it carries a `Level`. So the whole tower is four
terms:

| the term | its type | the name a person writes |
|---|---|---|
| `const(Nat)` | `sort(succ(zero))` | `Nat : Type` |
| `sort(zero)` | `sort(succ(zero))` | `Prop : Type` |
| `sort(succ(zero))` | `sort(succ(succ(zero)))` | `Type : Type 1` |
| `sort(succ(succ(zero)))` | `sort(succ(succ(succ(zero))))` | `Type 1 : Type 2` |

Read rows two and three together. `Prop` and `Type` are not two kinds of thing.
They are `sort(zero)` and `sort(succ(zero))`, one node with a different number
inside, and the names belong to the person rather than to the kernel.

---

## 5.3 There is no floor below `Prop`

Here is the question that catches everybody, and it is a good question.

`rfl` proves `2 = 2`. And `2 = 2 : Prop`, which is `Sort 0`. So does `rfl` live
at `Sort -1`?

No. Try the same reasoning somewhere familiar:

```
3 : Nat          and      Nat : Type
```

By the same step, `3 : Sort 0`. But `3` is plainly not a universe.

The hidden assumption is that every colon step drops one floor. It does not.
Only two kinds of term are a `Sort`. Everything else is an **element of** a
`Sort`, and an element gets no floor of its own.

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

## 5.4 Why `Prop` is special, in three ways

The floor numbers are not the real difference. These three are.

### 1. `Prop` is impredicative

**The idea.** A proposition may speak about every proposition, including
itself, and still be a proposition. Nothing grows.

**The rule.** The rule for a [Pi type](../GLOSSARY.md#pi-type) does not use
`max`. It uses [`imax`](../GLOSSARY.md#imax).

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
proposition, whatever the size of the domain is.

**The computation.** Run the rule by hand on two cases. In both of them the
domain is huge, and only one of them lands on the ground floor.

"for every proposition `p`, `p` implies `p`". The domain is `sort(zero)`, whose
own type is `sort(succ(zero))`, so `u` is 1. The body is a proposition, so `v`
is 0.

```
imax 1 0  =  0            so Sort 0, which is Prop
```

"for every type `α` on floor 9, `α` implies `α`". The domain is `sort 10`, whose
own type is `sort 11`, so `u` is 11. The body `α → α` sits on floor 10, so `v`
is 10.

```
imax 11 10  =  max 11 10  =  11      so Sort 11, which is Type 10
```

The first term speaks about **every** proposition, and it is itself a
proposition, so it speaks about a collection that holds it. The word for that
self-reference is **[impredicative](../GLOSSARY.md#impredicative)**.

The second one is **not** a `Prop`, and the reason is in the second number, not
the first. A large domain alone proves nothing. `imax` reads `v`, so the
**body** is what decides.

`Type` works the other way. A Pi type over `Type u` lands in `Type (max u v)`,
so the level grows. `Type` is **[predicative](../GLOSSARY.md#predicative)**.

One warning for a reader who knows Rocq. Lean has **no
[cumulativity](../GLOSSARY.md#cumulativity)** and no subtyping at all. `Type 0`
is not a subtype of `Type 1`. Lean uses
[universe polymorphism](../GLOSSARY.md#universe-polymorphism) instead, which
chapter 7 meets as the level arguments on a constant.

### 2. All proofs of one proposition are equal

**The idea.** You care **that** a claim holds. You never care **how**. So two
reasons for one claim may be treated as one object.

**The rule.** If `P : Prop` and `h₁ : P` and `h₂ : P`, then `h₁ ≡ h₂`. The
name is **[proof irrelevance](../GLOSSARY.md#proof-irrelevance)**.

**What it means for the checker.** Asked whether two terms are equal, the
checker first asks what their type is. If that type is a proposition, the answer
is yes, and neither term is ever looked at. Swap the proposition for a number
and the rule does not apply, as it should not. `0` and `1` are different
numbers. [Chapter 8](08-definitional-equality.md) puts this rule beside the six
others and says where in the order it is asked.

### 3. A proof cannot give data back

**The idea.** A proof must not be able to smuggle a value out. If it could, a
program would depend on which proof you wrote, and rule 2 would be a lie.

**The rule.** An inductive type in `Prop` may only eliminate into `Prop`. A
narrow exception exists for a [subsingleton](../GLOSSARY.md#subsingleton), which
is a type with at most one element.

**What it buys.** The compiler can **[erase](../GLOSSARY.md#erasure)** every
proof, so a proof costs nothing when the program runs.

Picture a function that takes a list and a proof that the list is not empty, and
gives back the first item. Two arguments go in. In the compiled program only the
list exists. The proof is gone, and nothing is lost, because of rule 2: there
was never anything to learn from which proof arrived.

You already rely on the same trade. A type parameter of a TypeScript generic is
gone in the emitted JavaScript, and the `erasableSyntaxOnly` option exists to
make a compiler refuse any syntax that would break that promise.

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

## 5.5 Prop is not Bool

This is the most common confusion, and it is worth one section.

**The idea.** `Bool` is an answer. `Prop` is a question. An answer is one of
two values you can branch on. A question is a claim that may or may not have a
reason.

**The rule.** `Not` is not a truth table. It is a function that **builds** a
proposition:

```
Not  =  fun (p : Prop) => p → False
```

So `Not False` is the proposition `False → False`.

**The data.** `Not` is a lambda, and its body builds a function type:

```
lam(p, sort(zero),
  forall(_, bvar 0, const(False)))
```

So "not false" is one application, and one β step is the whole reduction:

```
app(const(Not), const(False))
  ──β──►  forall(_, const(False), const(False))
```

The reduction **stops** there. The result is a function type, which is a claim,
and a claim is not an answer. No rule turns it into a `true`.

Is the claim true? A claim is true when something inhabits it, and something
does:

```
lam(h, const(False), bvar 0)
```

So "not false" is a **true proposition**, and it is **not the term for "true"**.
Both statements hold at once, and nothing is wrong.

| | `Bool` | `Prop` |
|---|---|---|
| what it is | an inductive type with two constructors | `Sort 0`, a kernel primitive |
| how many elements | 2 | infinitely many |
| pattern match on it | yes | no. There are no constructors. |
| `not false` or `Not False` | computes to `true` | stays a proposition |

The road from one to the other is `Decidable`, which has type `Prop → Type`. It
is data that somebody wrote: for a given proposition, a term of `Decidable`
carries a `Bool` **and** a proof that the `Bool` is the right answer. A function
called `decide` reads that term and returns the `Bool`. So the road exists, it
runs in one direction, and somebody has to build each piece of it.

---

### If you write TypeScript

Three mappings, and one of them is exact.

**Your two worlds are Lean's one world.** TypeScript keeps types and values
apart on purpose, and `tsc` deletes the type world before the program runs. The
TypeScript 5.8 option `erasableSyntaxOnly` turns that wall into a rule the
compiler enforces. It refuses any TypeScript syntax that would still need code
at run time. Lean has one world, so it needs the tower of section 5.1 instead
of a wall.

**A universe is not `unknown` and not a top type.** TypeScript has `unknown` at
the top, `never` at the bottom, and structural subtyping between them. Lean has
none of that. It has floors, and **no subtyping**: a term of `Type 0` is not a
term of `Type 1`, and no coercion happens behind your back. Where you would
reach for a bound and variance, Lean takes the level as a parameter.

**Erasure is the exact match.** `tsc` erases every type, and it is safe because
a type can never change what the program computes. Lean erases every proof, and
it is safe for a reason it can **prove**, which is rule 2 of section 5.4. Same
outcome, and Lean owes an argument where TypeScript owes none.

**`Prop` against `Type` is a distinction you already make by hand.** A value in
the `E` channel of `Effect<A, E, R>` is data you may read and branch on. A
proof is a fact you may only **use**. You keep that difference in your head
today. Lean puts it in the type system, so the kernel treats two proofs of one
proposition as equal and the compiler drops them both.

| | top type | bottom type | subtyping | what gets erased |
|---|---|---|---|---|
| TypeScript | `unknown` | `never` | structural | every type |
| Lean | none. A tower of `Sort u`. | none | **no** | every proof |

---

## 5.6 Try it

This is the chapter in one function. Paste it into a TypeScript playground.

```ts
type Level =
  | { k: "zero" }
  | { k: "succ"; of: Level }
  | { k: "max"; a: Level; b: Level }
  | { k: "imax"; a: Level; b: Level }

const zero: Level = { k: "zero" }
const lvl = (n: number): Level =>
  n === 0 ? zero : { k: "succ", of: lvl(n - 1) }

function toNat(l: Level): number {
  switch (l.k) {
    case "zero": return 0
    case "succ": return toNat(l.of) + 1
    case "max": return Math.max(toNat(l.a), toNat(l.b))
    case "imax": {
      const b = toNat(l.b)
      return b === 0 ? 0 : Math.max(toNat(l.a), b)
    }
  }
}

// "for every proposition p, p implies p"
console.log(toNat({ k: "imax", a: lvl(1), b: lvl(0) }))    // 0, so Prop
// "for every type on floor 9, that type implies itself"
console.log(toNat({ k: "imax", a: lvl(11), b: lvl(10) }))  // 11, so Type 10
// and the same two with `max` instead of `imax`
console.log(toNat({ k: "max", a: lvl(1), b: lvl(0) }))     // 1, so Type
```

Four lines of output, and the first and the last are the chapter. The same two
levels give `0` under `imax` and `1` under `max`. One rule keeps a statement
about every proposition on the ground floor. The other does not.

Then change `b` to `lvl(1)` in the first call and watch the answer leave the
ground floor. One step in the body is all it takes.

---

## 5.7 Check yourself

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

## 5.8 References

- Girard's paradox, for why `Type : Type` is fatal. Carneiro, *The Type Theory
  of Lean*, states the rules Lean uses to avoid it.
  <https://github.com/digama0/lean-type-theory>
- Harper and Pollack, *Type checking with universes*, 1991, for levels as
  variables. DOI [10.1016/0304-3975(90)90108-T](https://doi.org/10.1016/0304-3975%2890%2990108-T)
- Gilbert, Cockx, Sozeau and Tabareau, *Definitional proof-irrelevance without
  K*, 2019, for what rule 2 costs a checker.
  DOI [10.1145/3290316](https://doi.org/10.1145/3290316)
- TypeScript, `erasableSyntaxOnly`, for erasure as a rule a compiler enforces.
  <https://www.typescriptlang.org/tsconfig/#erasableSyntaxOnly>
- TypeScript, everyday types, for `unknown` and `never` at the two ends.
  <https://www.typescriptlang.org/docs/handbook/2/everyday-types.html>
- Rocq, `SProp`, for a system that keeps proof irrelevance in a separate sort.
  <https://rocq-prover.org/doc/master/refman/addendum/sprop.html>

---

**Next:** [6. The Calculus of Constructions](06-the-calculus-of-constructions.md)
