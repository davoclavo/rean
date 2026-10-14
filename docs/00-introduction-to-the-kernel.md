# Chapter 0 — The foundations, in one file

> **This is the appendix, and not the first read.**
> [Part I of the book](book/README.md) is this same material in eight short
> chapters, with more examples, a `Try it` section each, and three questions at
> the end of each one. A first-time reader should start there and be kind to
> themselves.
>
> **Read this file when** you want every rule in one place, or when a later
> chapter points at a section of it.
>
> **A new word?** Read [the glossary](GLOSSARY.md). **A source?** Read
> [the references](REFERENCES.md). **Lost?** Read [the guide](README.md).

This chapter answers one question: **what is the smallest thing that can check a
proof?**

You need no background in logic. You need to know what a function is.

Every claim here has a test in `crates/rean_kernel/tests/universes.rs`. Run it:

```sh
devbox run -- cargo test -p rean_kernel --test universes
```

---

## 0.1 What a proof checker does

A proof checker reads a file and answers one question per theorem: yes or no.

It does not search for a proof. It does not help you. A human or a tactic writes
the proof, and the checker only says whether the proof is correct.

That job turns out to be an algebra:

- One **operation**: substitution, written `b[x := a]`.
- One **relation**: definitional equality, written `a ≡ b`.
- One **bridge**: the type judgment, written `Γ ⊢ e : A`.

The rest of this chapter unpacks those three lines.

---

## 0.2 The one big idea: a proof is a term

A **proof is a term**. A **proposition is a type**.

| Logic | Type theory |
|---|---|
| `A` is true | some term has type `A` |
| a proof of `A → B` | a function from `A` to `B` |
| a proof of `∀ x, P x` | a function that takes `x` and returns a proof of `P x` |

So "check this proof" becomes "check this type". The name for this idea is the
Curry-Howard correspondence.

An example. The proposition "if `A` then `A`" is the type `A → A`. The proof is
the identity function `fun h => h`. Give it a proof of `A`, and it gives a proof
of `A` back.

This is the reason that a proof checker and a type checker are the same program.

---

## 0.3 The alphabet: six term forms

The language of terms is tiny. This is all of it:

```
e ::= x                      a variable
    | c                      a constant from the environment
    | Sort u                 a universe
    | e₁ e₂                  application
    | fun (x : A) => e       a function
    | (x : A) → B            a function type
```

Two notes:

- `(x : A) → B` is a **function type where `B` can mention `x`**. The name for it
  is a Pi type. When `B` ignores `x`, you write `A → B`. When `A` is a
  proposition, you read the same term as `∀ x : A, B`.
- `Sort` needs a number, because a type cannot hold itself. Section 0.9 explains
  the number.

So `∀` and `→` are **the same term form**. That single fact is why the language
stays this small. The test `an_arrow_is_a_forall_whose_body_ignores_the_binder`
shows it in the code.

---

## 0.4 The judgment

Everything a checker says has one shape:

```
Γ ⊢ e : A
```

Read it: "in the context `Γ`, the term `e` has the type `A`".

`Γ` is a list of what you already know:

```
Γ  =  x₁ : A₁,  x₂ : A₂,  ...,  xₙ : Aₙ
```

In logic, `Γ` is the list of hypotheses. In code, `Γ` is the local context.

---

## 0.5 The one operation: substitution

```
b[x := a]
```

Read it: "`b`, but every free `x` becomes `a`".

This is the only operation in the algebra. It is also the one place where a
naive implementation breaks. The problem is **capture**:

```
(fun y => x)[x := y]      must NOT become   fun y => y
```

The outer `y` and the inner `y` are different variables that share a name. Two
cures exist, and Lean uses the second:

1. Rename the inner binder. This is slow, and it is easy to get wrong.
2. Delete the names. A bound variable becomes a **number**.

### de Bruijn indices

The number is the count of binders between the use and its own binder:

```
fun x => fun y => x        becomes   λ λ #1
fun x => fun y => y        becomes   λ λ #0
```

Now two proofs that differ only in variable names are **the same data**, so `==`
works. Substitution becomes arithmetic on the numbers.

Three functions do the arithmetic. They live in
`crates/rean_kernel/src/expr.rs`:

| Function | Job |
|---|---|
| `lift(cutoff, amount)` | add to every loose index. A term that moves under a new binder needs it. |
| `instantiate(value)` | replace index 0 with a term. One beta step is one call. |
| `abstract_fvar(id)` | the reverse. It closes a binder again. |

The test `de_bruijn_erases_the_binder_name_from_the_body` shows that the body of
`fun x => x` and the body of `fun y => y` are equal data.

One warning about our code. `Expr::Lam` still keeps a `binder_name` field, and
`PartialEq` is derived. So `==` compares that name:

```rust
Expr::lam("x", nat(), Expr::bvar(0)) != Expr::lam("y", nat(), Expr::bvar(0))
```

The name exists only for the printer. A real `is_def_eq` must skip it. Chapter 9
adds `alpha_eq` for that job.

---

## 0.6 The type rules

Read each rule as: "if everything above the line holds, then the thing below the
line holds".

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

That last rule is where section 0.5 earns its place. The type of the result
**depends on the argument value**. A C compiler never does this. A proof checker
does it on every step.

---

## 0.7 The one relation: definitional equality

The checker must accept `2 + 2` where a rule asks for `4`. So it needs a notion
of "the same by computation". That relation is `≡`, and five equations generate
it:

| Name | Equation | In words |
|---|---|---|
| β beta | `(fun (x : A) => b) a ≡ b[x := a]` | call a function |
| δ delta | `c ≡ v` when the environment holds `def c := v` | unfold a definition |
| ζ zeta | `let x := v; b ≡ b[x := v]` | unfold a local definition |
| ι iota | `Nat.rec z s (Nat.succ n) ≡ s n (Nat.rec z s n)` | run a recursor |
| η eta | `fun x => f x ≡ f` | a wrapper is the thing |

`≡` is the smallest relation that holds these equations and that works under
every term form. Lean adds one more rule: if `P : Prop` and `h₁ : P` and
`h₂ : P`, then `h₁ ≡ h₂`. All proofs of one proposition are equal. The name is
proof irrelevance.

### Two equalities, and this confuses everybody

| | `a ≡ b` | `a = b` |
|---|---|---|
| What it is | a judgment of the checker | a proposition, the inductive type `Eq` |
| Who decides | the kernel, by computation | you, with a proof term |
| Can you state it | no, it is not a term | yes, it is a type |

`rfl` is the bridge. `rfl : a = b` type checks exactly when `a ≡ b`.

Keep this table close. Section 0.11 shows a puzzle that only this table solves.

---

## 0.8 The hinge: the conversion rule

One more rule joins sections 0.6 and 0.7:

```
   Γ ⊢ e : A      A ≡ B      Γ ⊢ B : Sort u
   ----------------------------------------
                Γ ⊢ e : B
```

Read it: "a term keeps its type under computation".

This rule is the hinge of the whole design. It is the reason a proof checker must
hold an **evaluator** inside it. To check a proof, the kernel must sometimes run
a program. No other kind of checker needs that.

---

## 0.9 `Sort`, `Prop`, and `Type` are one thing

**`Sort` is the primitive. `Prop` and `Type` are names for two parts of it.**

```
Prop      :=  Sort 0
Type      :=  Sort 1
Type n    :=  Sort (n + 1)
```

`Prop` and `Type` do not exist in the kernel at all. The parser turns them into
`Sort`. The printer turns `Sort` back, so that the output reads well. No
declaration for either name lives in the environment.

Our code holds one variant and not three:

```rust
pub fn prop() -> Expr {
    Expr::Sort(Level::Zero)              // Sort 0
}

pub fn type_(n: u32) -> Expr {
    Expr::Sort(Level::of_nat(n + 1))     // Sort (n+1)
}
```

The test `prop_and_type_are_both_just_sort` checks it.

Watch the off-by-one. `Type` is `Sort 1`, not `Sort 0`. `Prop` took slot 0.

### The ladder

One rule builds the whole tower:

```
Sort u : Sort (u + 1)
```

Put numbers in it:

```
   Prop    :  Type      because   Sort 0  :  Sort 1
   Type    :  Type 1    because   Sort 1  :  Sort 2
   Type 1  :  Type 2    because   Sort 2  :  Sort 3
   ...
```

There is no top. The tower must be infinite, else `Sort u : Sort u` would hold,
and that lets you prove `False`.

### There is no `Sort -1`

A natural first guess goes like this. `rfl : 2 = 2`, and `2 = 2 : Sort 0`, so
`rfl` must sit at `Sort -1`.

Test the same reasoning on `Nat`:

```
3 : Nat          and      Nat : Sort 1
```

By that rule, `3 : Sort 0`. But `3` is clearly not a universe.

The error is a hidden assumption: that **every colon step drops one `Sort`
number**. It does not. Only two kinds of term are a `Sort` at all:

```
Prop     =  Sort 0
Type n   =  Sort (n + 1)
```

Everything else is an **element of** a `Sort`.

A type `T` has **level `u`** when `T : Sort u`. A level belongs to a type, never
to an element:

| Level | The universe | Types at that level | Elements of those types |
|---|---|---|---|
| 2 | `Type 1` = `Sort 2` | `Type`, `Prop → Type` | `Nat`, `Prop`, `Decidable` |
| 1 | `Type` = `Sort 1` | `Nat`, `Bool`, `Prop` | `3`, `true`, `2 = 2` |
| 0 | `Prop` = `Sort 0` | `True`, `False`, `2 = 2` | `trivial`, none, `rfl` |

Read the bottom row. `2 = 2` is a type **at level 0**. It is one of the many
elements of `Sort 0`. It is not `Sort (-1)`.

Then `rfl` is an element of a level 0 type. `rfl` is not a type, so it gets no
level. **The chain stops.**

It must stop, because `Level` has no way down:

```rust
pub enum Level {
    Zero,                       // the floor
    Succ(Arc<Level>),           // the only way up
    Max(Arc<Level>, Arc<Level>),
    IMax(Arc<Level>, Arc<Level>),
    Param(Name),
}
```

There is no `Pred`. `Sort -1` is not a term that the kernel rejects. It is a term
that nobody can write. The test is `there_is_no_level_below_zero`.

So the building has a floor, and proofs are the floor:

```
Prop            a universe
  ↑
2 = 2           a proposition, and a type
  ↑
rfl             a proof. Nothing is an element of rfl.
```

Three rungs for `Prop`. Two rungs for `Nat`.

---

## 0.10 Why `Prop` and `Type` differ

The numbers are not the real difference. Three real differences exist.

### 1. `Prop` is impredicative

The rule for a function type uses `imax`, not `max`:

```
   A : Sort u      B : Sort v
   --------------------------------
   (x : A) → B  :  Sort (imax u v)
```

And `imax` has one special case:

```
imax u 0  =  0
imax u v  =  max u v      when v is not 0
```

Our code:

```rust
Level::IMax(a, b) => {
    let b = b.to_nat()?;
    if b == 0 { Some(0) } else { Some(a.to_nat()?.max(b)) }
}
```

Read what that buys. If the result `B` is a proposition, then the whole function
type is a proposition, **whatever the size of `A` is**. So both of these are a
`Prop`:

```lean
#check ∀ (p : Prop), p → p        -- ∀ (p : Prop), p → p : Prop
#check ∀ (α : Type 9), α = α      -- ∀ (α : Type 9), α = α : Prop
```

Walk the first one. The domain is `Prop`, and `Prop : Sort 1`, so `u` is 1. The
body is `p → p`, and `p : Sort 0`, so the body sits at `imax 0 0 = 0`, which
makes `v` equal to 0. The whole term is then `imax 1 0 = 0`. It is a `Prop`.

Look at what just happened. The term quantifies over **every** proposition, and
the result is itself a proposition. So the term quantifies over a collection that
holds the term. That self-reference is what the word impredicative means.

Walk the second one, and count carefully. The domain is `Type 9`, which is
`Sort 10`, and `Sort 10 : Sort 11`, so `u` is 11. The body `α = α` is a `Prop`,
so `v` is 0. The whole term is `imax 11 0 = 0`. A huge domain, and the term
stays at level 0. The test is `a_function_into_prop_stays_in_prop`.

One trap, and Lean prints it for you:

```lean
#check ∀ (α : Type 9), α → α      -- (α : Type 9) → α → α : Type 10
```

That one is **not** a `Prop`. Here `u` is 11 again, and the body `α → α` sits
at `imax 10 10 = 10`, so `v` is 10. The whole term is `imax 11 10 = 11`, which
is `Sort 11`, which prints as `Type 10`. The body must land at level 0 for
`imax` to collapse. A large domain alone is not enough.

`Type` does not work this way. A function type over `Type u` lands in
`Type (max u v)`. The level grows. `Type` is predicative.

One warning. Lean 4 has **no cumulativity**. `Type 0` is not a subtype of
`Type 1`. Coq has that rule and Lean does not. Lean uses universe polymorphism
instead, which is the `levels` field on `Expr::Const`.

### 2. `Prop` has proof irrelevance

If `P : Prop` and `h₁ : P` and `h₂ : P`, then `h₁ ≡ h₂`. The kernel treats all
proofs of one proposition as the same.

This is false in `Type`. `0 : Nat` and `1 : Nat` are not the same.

Why it matters: you only care **that** a proposition holds, never **how**. So the
content of a proof can go away.

### 3. `Prop` cannot give data back

An inductive type in `Prop` can only eliminate into `Prop`. A small exception
exists for types with at most one element. So you cannot open a proof and pull a
number out of it.

Why it matters: the compiler can **erase** every proof. A proof costs nothing at
run time. That is sound only because of this rule.

### Summary

| | `Prop` | `Type u` |
|---|---|---|
| Is | `Sort 0` | `Sort (u+1)` |
| Holds | propositions | data |
| Function type rule | `imax`, so it stays at 0 | `max`, so it grows |
| All elements equal | yes | no |
| Can give data back | no | yes |
| Survives at run time | no, the compiler erases it | yes |

---

## 0.11 Worked examples

### Three lines that contain the whole idea

```lean
def n : Nat  := 3        -- an element of Nat
def p : Prop := 2 = 2    -- an element of Prop
theorem h : p := rfl     -- an element of p
```

Line 1 and line 2 are **exactly parallel**. One writes a number into a `Nat`
slot. The other writes a proposition into a `Prop` slot. So you make elements of
`Prop` the same way you make elements of `Nat`.

Line 3 is the part that has no parallel:

```lean
def q : n := ...     -- rejected. `n` is 3, and 3 is not a type.
```

`p` is an element of `Prop` **and** a type in its own right. `n` is an element of
`Nat` and nothing more.

### The rule behind that rejection

You can write `x : T` only when `T` is a `Sort`.

```lean
(h : P)      -- legal.   P : Prop,  and Prop IS Sort 0.
(h : 3)      -- rejected. 3 : Nat,  and Nat is not a Sort.
```

### Elements of `Prop` are ordinary things

```lean
def p1 : Prop := True
def p2 : Prop := False
def p3 : Prop := 2 + 2 = 4
def p4 : Prop := 2 + 2 = 5
def p5 : Prop := ∀ n : Nat, n + 0 = n
def p6 : Prop := ∃ n : Nat, n > 5
```

All six are legal. Note `p4`. A **false** proposition is still a good element of
`Prop`. It is not an error.

So where does truth live? One level down:

| Element of `Prop` | Does it have an element? | The element |
|---|---|---|
| `True` | yes | `trivial` |
| `2 + 2 = 4` | yes | `rfl` |
| `2 + 2 = 5` | no | none exists |
| `False` | no | none exists |

**A proposition is true exactly when it has an element.** That element is the
proof.

No element of `Nat` ever has elements. `3` is not a type, so the question does
not even make sense.

### `Prop` and `Nat` share a universe

```
Prop : Type        and        Nat : Type
```

Both are elements of `Sort 1`. So you can treat them alike wherever a `Type` is
wanted:

```lean
#check [1, 2, 3]                 -- List Nat
#check [True, False, 2 = 2]      -- List Prop
#check [Nat, Prop, Bool]         -- List Type
```

The third line is the direct demonstration. `Nat` and `Prop` sit in one list,
because they are elements of one universe. The test is
`prop_and_nat_fit_the_same_container`.

But universe membership answers only one question: how big is this thing? It
says nothing about what the thing does.

### `Nat` is flat, `Prop` is a universe

Count the levels:

```
                  Type  =  Sort 1
                    ↑                    read ↑ as "is an element of"
          Prop                Nat
            ↑                  ↑
   True   False   2 = 2      0  1  2
            ↑                  ↑
 trivial    -     rfl        nothing
```

- `Nat` has **two** levels. `Nat`, then its elements.
- `Prop` has **three** levels. `Prop`, then propositions, then proofs.

Here is the asymmetry in one line:

```
Prop   : Type 0        a universe that IS an element of the first universe
Type 0 : Type 1        a universe that is NOT an element of the first universe
```

`Prop` is the only small universe. That is the same fact as its impredicativity.

### `Not` is data. `¬P` is a proposition.

Our kernel prints:

```
Not             = fun (p : Prop) => p → False
type of Not     = Prop → Prop
```

Put it next to something familiar:

| | input | output |
|---|---|---|
| `Nat.succ : Nat → Nat` | `3` | `4`, an element of `Nat` |
| `Not : Prop → Prop` | `True` | `True → False`, an element of `Prop` |

`Not` is to `Prop` what `Nat.succ` is to `Nat`. It is a **function**, so it is
data. Its **result** is a proposition.

The function lives at `Type`, because `imax 1 1 = 1`. The result lives at `Prop`,
because `imax 0 0 = 0`. Same rule, two inputs, two answers.

### A function from data to propositions

```lean
def double : Nat → Nat    -- double 4  is  8
def Even   : Nat → Prop   -- Even 4    is  a proposition
```

- `Even 4` is a proposition. It has an element, so it is true.
- `Even 5` is a proposition. It has no element, so it is false.
- `Even` itself is data.

### A function from propositions to data

```
Decidable  :  Prop → Type
```

`Decidable P` is a **type with two elements**:

```lean
inductive Decidable (p : Prop) where
  | isFalse (h : ¬p)
  | isTrue  (h : p)
```

So `Decidable P` is real data that you can pattern match on. This is how
`if P then a else b` runs in compiled code.

`Decidable` could not exist if `Prop` were not an element of a universe. It takes
`Prop` as an argument the same way `List` takes `Nat` as an argument.

### The puzzle: `Not False` is not `True`

Here is the real output of our kernel:

```
Not False        -> False → False           equals True?   false
Not True         -> True → False            equals False?  false
Not (Not False)  -> (False → False) → False equals False?  false
```

`Not False` really does give `False → False`.

The idea to swap in: **`Prop` is not `Bool`. `Not` is not a truth table.**

`Not` does not compute a truth value. It **builds a proposition**:

```
Not  =  fun (p : Prop) => p → False
```

Now split two things that intuition joins:

| | Meaning |
|---|---|
| the **term** `True` | one particular proposition, with one proof `trivial` |
| the **property** "is true" | this proposition has at least one proof |

`Not False` is `False → False`. Does it have a proof?

```lean
example : False → False := fun h => h
```

Yes. So **`Not False` is a true proposition**, and it is **not the term `True`**.
Both statements hold at once.

Check the others:

| Term | Reduces to | Has a proof? | So |
|---|---|---|---|
| `Not False` | `False → False` | yes, `fun h => h` | true |
| `Not True` | `True → False` | no | false |
| `Not (Not False)` | `(False → False) → False` | no | false |

Every answer matches logical intuition. Only the **terms** look unfamiliar.

### Why the kernel refuses to simplify

**`Bool` does compute:**

```lean
inductive Bool where
  | false
  | true

def not : Bool → Bool
  | true  => false
  | false => true

#eval not false     -- true.  It really reduces, by the ι rule.
```

**`Prop` does not:**

```lean
def f (p : Prop) : Bool :=
  match p with
  | True  => true
  | False => false
```

Rejected, for two separate reasons:

1. `Prop` has **no constructors**. It is `Expr::Sort(Level::Zero)`, a kernel
   primitive. There is nothing to match on.
2. Even with constructors, `2 + 2 = 4` would match neither case. `Prop` has
   **infinitely many** elements, not two.

| | `Bool` | `Prop` |
|---|---|---|
| What it is | an inductive declaration | `Sort 0`, a kernel primitive |
| Number of elements | 2 | infinitely many |
| Constructors | `true`, `false` | none |
| Pattern match on it | yes | no |
| `not false` / `Not False` | reduces to `true` | reduces to `False → False` |

There is no truth table, so there is nothing to look up.

### How you do get from `Not False` to `True`

You prove it. You do not compute it.

```lean
theorem notFalse : ¬False ↔ True :=
  Iff.intro (fun _ => trivial) (fun _ h => h)
```

And if you want a real `=`, you pay one axiom:

```lean
theorem notFalseEq : (¬False) = True := propext notFalse
```

Even after this theorem, the **kernel** still does not treat the two terms as
definitionally equal. You must apply the theorem by hand.

Back to the table of section 0.7:

| Statement | Which equality | Who does the work |
|---|---|---|
| `Not False ≡ False → False` | definitional | the kernel, by β. Free. |
| `(Not False) = True` | propositional | you, with a proof plus `propext` |

The question "should it not give `True`" assumes the first kind. The answer lives
in the second kind.

### The bridge, when you want a real boolean

```lean
#eval decide (2 = 2)      -- true
#eval decide (2 = 3)      -- false
```

`decide` turns a proposition into a `Bool`, but only when a `Decidable` instance
exists. That instance is **data** that someone wrote. The kernel does not find it
for you.

That is why `Decidable : Prop → Type` has to exist. It is the only road from
logic to computation.

### Where the difference bites: erasure

```lean
def firstOr0 (xs : List Nat) (h : xs ≠ []) : Nat := ...
```

Two arguments go in. In the compiled program, **only `xs` exists**. The argument
`h` is gone.

Why it is safe: `xs ≠ []` is a `Prop`, so all its proofs are equal, so there is
no information in `h` to lose. That is proof irrelevance at work.

You could never erase a `Nat` argument. `3` and `4` are different.

### The full map

| Term | Its type | The type of that |
|---|---|---|
| `3` | `Nat` | `Type` |
| `rfl` | `2 = 2` | `Prop` |
| `trivial` | `True` | `Prop` |
| `Nat` | `Type` | `Type 1` |
| `Prop` | `Type` | `Type 1` |
| `Not` | `Prop → Prop` | `Type` |
| `Even` | `Nat → Prop` | `Type` |
| `Decidable` | `Prop → Type` | `Type 1` |
| `Type` | `Type 1` | `Type 2` |

Nothing in the table is special-cased. Every type in the middle column comes from
the `imax` rule, and `Prop` is `Sort 0`.

### The one question to ask

When a term confuses you, ask: **how many rungs are below it?**

```
Nat   rung 2        Prop        rung 2
 3    rung 1        2 = 2       rung 1
 -                  rfl         rung 0
```

`Nat` and `Prop` share rung 2. That is the shared universe. The difference is
that the `Prop` column has a rung 0 and the `Nat` column does not.

---

## 0.12 Where the rest of logic comes from

Sections 0.3 to 0.8 give you `→` and `∀` only. Everything else is an **inductive
type**. You declare a type by its constructors, and you get a recursor for free.

| Logic | Declaration | Constructors |
|---|---|---|
| `False` | inductive | zero |
| `True` | inductive | one, with no argument |
| `A ∧ B` | inductive | one, which carries a proof of `A` and a proof of `B` |
| `A ∨ B` | inductive | two, one per side |
| `∃ x, P x` | inductive | one, which carries a witness and a proof |
| `a = b` | inductive | one, named `rfl` |
| `¬ A` | not new | it is `A → False` |

To **build** a proof of `A ∧ B`, you call the constructor. To **use** a proof of
`A ∨ B`, you call the recursor, and the ι rule makes it compute.

So a full kernel needs one more large piece: a check that an inductive
declaration is sound. The main condition is **strict positivity**. Without it you
can declare a type that proves `False`.

---

## 0.13 The two algorithms

A kernel is two functions that call each other:

```
infer_type(Γ, e)   -> A        the rules of section 0.6
is_def_eq(Γ, a, b) -> bool     the relation of section 0.7
```

Each needs a third helper:

```
whnf(Γ, e) -> e'               reduce until the head is stable
```

Why each needs the others:

- `infer_type` needs `whnf`, because the application rule wants a function type,
  and it may find a constant that unfolds to one.
- `infer_type` needs `is_def_eq`, to accept an argument whose type only matches
  after computation.
- `is_def_eq` needs `whnf`, because you cannot compare `2 + 2` with `4` without a
  reduction.
- `is_def_eq` needs `infer_type`, because proof irrelevance first asks whether
  the type is a `Prop`.

Those three functions are the proof checker. Everything else serves them.

One note on the `whnf` in that list. Our `Expr::beta` reduces **the head only**.
It does not go under a binder, so it does not give a full normal form. The test
`head_beta_leaves_an_inner_redex_alone` shows the limit.

---

## 0.14 The ultimate primitives

Nothing below this is defined in terms of anything else.

### Layer 0: five level formers

```
zero          0
succ u        u + 1
max u v       the larger
imax u v      0 if v is 0, else max u v
param n       a universe variable, such as the u of List.{u}
```

`imax` is not derivable from `max`. It is a primitive, and `Prop` is the reason.

### Layer 1: the term formers

Our `Expr` has eleven. Lean has twelve, and it adds `MData` for annotations.

```
BVar i                        a bound variable, by de Bruijn index
Sort u                        a universe
Const name levels             a name from the environment
App f a                       application
Lam name ty body info         a function
Forall name ty body info      a function type
Let name ty val body          a local definition
FVar id                       a free variable, for the local context
MVar id                       a hole, for the elaborator only
Lit n                         a Nat or a String literal
Proj struct i e               a field of a structure
```

Six are the true theoretical core:

```
BVar   Sort   Const   App   Lam   Forall
```

The other five are there for a reason, not for theory:

- `FVar` and `MVar` serve the elaborator. A finished proof holds neither.
- `Let` is `App` plus `Lam` in theory, but it keeps the term small.
- `Lit` is `Nat.succ (Nat.succ ...)` in theory. A literal makes arithmetic fast.
- `Proj` is a call to the recursor in theory. A projection makes a structure
  fast.

### Layer 2: the rules

- The type rules of section 0.6, plus the conversion rule of section 0.8.
- The five reduction equations of section 0.7.
- Proof irrelevance.

### Layer 3: four kinds of declaration

The environment is a map from `Name` to one of these:

| Kind | Holds | Gives you |
|---|---|---|
| `axiom` | a name and a type | nothing. The kernel trusts it blindly. |
| `def` | a name, a type, and a value | the δ rule |
| `theorem` | the same as `def`, but the value is a proof | the same |
| `inductive` | constructors | a type, the constructors, a recursor, and the ι rule |

Lean adds one more primitive that you cannot build from the list above:
**quotient types**. The kernel knows four constants, `Quot`, `Quot.mk`,
`Quot.lift` and `Quot.ind`, and a computation rule for each of the last two.
`Quot` lets you build the rationals out of pairs of integers.

### Layer 4: the trusted axioms

These are not kernel primitives. They are `axiom` declarations in the library.
They are still where real trust sits, because an axiom is the one thing the
kernel does not check.

Three are the mathematical ones:

- `propext` — if two propositions imply each other, they are equal.
- `Quot.sound` — two equivalent elements have the same quotient.
- `Classical.choice` — you can pick an element out of a non-empty type. This is
  what gives Lean the law of the excluded middle.

And the real Lean prelude holds four more. This chapter said "three" until we
ran the checker over the prelude and the trust report printed them all:

```
trust: 7 axiom(s): Classical.choice, Lean.ofReduceBool, Lean.ofReduceNat,
                   Lean.trustCompiler, Quot.sound, propext, sorryAx
```

- `sorryAx` — what `sorry` becomes. A proof that reaches it is not a proof, and
  this is why a report that names the axioms matters.
- `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` — these trust
  the compiler's own evaluation rather than the kernel's. `native_decide` uses
  them, and a proof that rests on one asks you to trust the compiler too.

`#print axioms myTheorem` lists which ones a theorem uses. Chapter 14 adds the
same report here, as `Environment::axioms_of`.

---

## 0.15 What is not primitive

Almost everything you will write:

| Thing | What it really is |
|---|---|
| `A → B` | `Forall` whose body ignores the binder |
| `∀ x : A, P x` | `Forall`. The same term form as `→`. |
| `Prop` | `Sort 0` |
| `Type u` | `Sort (u+1)` |
| `¬ A` | `A → False` |
| `False` | an inductive type with zero constructors |
| `True`, `∧`, `∨`, `∃`, `=` | inductive types |
| `Nat`, `List`, `Bool` | inductive types |
| `rfl` | the one constructor of `Eq` |
| `0`, `1`, `2` | `Nat.zero` and `Nat.succ`, or a `Lit` |
| every tactic | a program that builds an `Expr`. Untrusted. |
| `simp`, `rw`, `induction` | the same |

---

## 0.16 What you must trust

Lean has a parser, a macro system, an elaborator, a unifier, and hundreds of
tactics. **None of them is trusted.**

Each one only produces a candidate `Expr`. The kernel then re-checks that `Expr`
from nothing, with the rules of sections 0.6 to 0.12. A tactic with a bug
produces a term that the kernel rejects. It cannot produce a false theorem.

So the trusted part is: `infer_type`, `is_def_eq`, `whnf`, and the inductive
soundness check. That is a few thousand lines. The rule is called the De Bruijn
criterion, and it is the reason the design splits the way it does.

---

## 0.17 Where this repository stands

| Layer | Status |
|---|---|
| 0, levels | done. All five formers, with a canonical normal form. |
| 1, term formers | done. All eleven. |
| 2, the type rules | done. See `infer_type`. |
| 2, the equations | β, ζ, δ, ι, η, plus proof irrelevance and projection |
| 3, declarations | done. All eight kinds, and `Quot` computes. |
| 4, axioms | reported, by name, for every declaration |

`Level::IMax` is live. `infer_type` calls it on every `Forall`, so the
impredicativity of section 0.10 is a running computation and not only a claim.

The kernel also checks what a kernel must check, and not only what a term is:
strict positivity, the recursor shape with derived minor premises, the
restriction on eliminating out of `Prop`, universe hygiene, one name per
declaration, and that no safe declaration rests on an unsafe one.

### The scoreboard

```sh
devbox run -- cargo run -p rean -- check fixtures/lean4export/shapes.ndjson
```

```
level 1: checked 63 of 63 declarations
trust: no accepted declaration rests on an axiom
```

Two fixtures, 95 declarations of real Lean, every one checked. See
[the roadmap](ROADMAP.md) for what is still missing, and
[chapter 15](15-mutual-and-nested.md) section 15.5 for the inventory.

### Where to read next

| If you want | Go to |
|---|---|
| this material slowly, with examples and exercises | [Part I of the book](book/README.md) |
| the whole reading order, part by part | [the guide](README.md) |
| the code that runs these rules | [the type checker](09-the-type-checker.md) |
| every rule the environment adds | [the environment](10-the-environment.md) |
| the first stage of the pipeline, which needs none of this | [the frontend](16-the-frontend.md) |

---

## 0.18 Exercises

1. Write `fun x => fun y => y x` with de Bruijn indices.
2. `Expr::arrow(from, to)` calls `to.lift(0, 1)`. Say why. What breaks without
   the lift?
3. At which level does `Nat → Prop` sit? At which level does `Prop → Nat` sit?
   Use the `imax` equation, then check with `pi_level` in the test file.
4. Is `(2 = 2) : Prop` a type? Is `rfl` a type? Give the reason for each.
5. `Not (Not True)` reduces to what term? Does that term have a proof?
6. Why can a tactic have a bug and still never prove a false theorem?
7. Our `==` on `Expr` compares `binder_name`. Give a pair of terms where that
   makes `==` return `false` when `alpha_eq` should return `true`.
8. `imax u 0 = 0`. Change it to `max u 0 = u` and `Prop` becomes predicative.
   Which example in section 0.10 stops working?

### Answers

1. `λ λ (#0 #1)`.
2. The body moves under one new binder, so every loose index must count one
   binder more. Without the lift, `Expr::arrow(nat, bvar(0))` would make the
   `bvar(0)` point at the new binder instead of at the outer one.
3. `Nat : Sort 1` and `Prop : Sort 1`, so `Nat → Prop` is `imax 1 1 = 1`, which
   is `Type`. `Prop → Nat` is also `imax 1 1 = 1`, which is `Type`. Both are
   data.
4. `2 = 2` is a type, because `2 = 2 : Sort 0` and `Sort 0` is a universe. `rfl`
   is not a type, because its type `2 = 2` is not a `Sort`.
5. `Not True` is `True → False`, so `Not (Not True)` is
   `(True → False) → False`. It **does** have a proof:
   `fun k => k trivial`. From `k : True → False` and `trivial : True` you get
   `k trivial : False`. So `¬¬True` is true, which agrees with `True` being
   true.
6. Because the kernel re-checks the tactic output from nothing. The tactic is
   only a search procedure. Its result must pass `infer_type` and `is_def_eq`.
7. `Expr::lam("x", nat, bvar(0))` and `Expr::lam("y", nat, bvar(0))`. The bodies
   are equal data, and only the stored name differs.
8. `∀ (p : Prop), p → p` stops being a `Prop`. With `max` it becomes
   `max 1 0 = 1`, which is `Type`. Every proposition that quantifies over a type
   would then climb the tower, and proof irrelevance and erasure would no longer
   apply to it. `Prop` would lose its self-reference, so it would no longer be
   impredicative.

---

## 0.19 How other systems do it

Lean is one point in a space, and the other points are the fastest way to see
what Lean chose.

| System | The home of a proposition | How it decides sameness | The part you must trust |
|---|---|---|---|
| **Lean 4** | `Prop`, which is `Sort 0`. It is impredicative, and the kernel treats two proofs of one proposition as equal. | β δ ι ζ η, proof irrelevance, and rules for `Nat` | `src/kernel`, about 6,000 lines of C++ |
| **Rocq**, formerly Coq | `Prop`, impredicative. `SProp` is the sort with proof irrelevance. | the same Greek letters, and **cumulativity** as well | its own kernel. The tool `coqchk` re-checks a whole library. |
| **Agda** | `Set u` for data, and an optional `Prop` with irrelevance | β δ ι η, by normalisation by evaluation | the type checker itself. There is **no** small kernel. |
| **Isabelle/HOL** | a formula of higher order logic. There are no dependent types. | rewriting, inside a proof, not a conversion rule | an LCF kernel. A theorem is a value that only an inference rule can build. |
| **Metamath Zero** | a formula of a chosen axiom system | nothing. A proof names every step, so the checker never computes. | a verifier of a few thousand lines |

Four differences are worth a sentence each.

- **Cumulativity.** In Rocq, `Type 0` is a subtype of `Type 1`. In Lean it is
  not, and a declaration takes its universe levels as parameters instead.
  Section 0.9 is where that choice shows.
- **Proof irrelevance.** Lean puts it in the kernel, for `Prop` itself. Rocq
  gives it to a second sort, `SProp`, because adding it to `Prop` breaks other
  things that Rocq wants. Chapter 10, section 10.7 implements the rule and finds
  the bug it exposes.
- **A solver in place of a kernel.** A tool such as Dafny or F★ sends the hard
  part to an SMT solver. That is powerful, and it ends the De Bruijn criterion:
  you must then trust a large program that was not written to be read.
- **The nearest thing in an ordinary compiler.** GHC can re-check its own
  intermediate language with the flag `-dcore-lint`. The idea is the same as a
  kernel, and the status is not. It is a debugging aid, and nobody ships a
  proof that rests on it.

One last likeness. TypeScript, Rust and Haskell erase every type before the
program runs, because nothing computes with a type. Lean erases a proof for the
same reason, and Lean can **prove** the reason. Chapter 27 is where that
matters.

## 0.20 References

**Our code**

- `crates/rean_kernel/src/level.rs`, `expr.rs`, and
  `crates/rean_kernel/tests/universes.rs`

**Lean's own source**

- `src/kernel/expr.h`, the eleven term formers
- `src/kernel/level.h`, a universe level
- `src/kernel/type_checker.cpp`, the two algorithms of section 0.13
- `src/Init/Prelude.lean`, which declares `Quot.sound`, `sorryAx` and
  `Classical.choice` as axioms

**Read more**

- Carneiro, *The Type Theory of Lean*, for the rules as rules.
  <https://github.com/digama0/lean-type-theory>
- *The Lean Language Reference*, the type system.
  <https://lean-lang.org/doc/reference/latest/The-Type-System/>
- *Theorem Proving in Lean 4*, for propositions as types with Lean's own words.
  <https://lean-lang.org/theorem_proving_in_lean4/>
- de Bruijn, *Lambda calculus notation with nameless dummies*, 1972, for
  section 0.5. DOI [10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258%2872%2990034-0)
- Coquand and Huet, *The Calculus of Constructions*, 1988, for the theory Lean
  extends. DOI [10.1016/0890-5401(88)90005-3](https://doi.org/10.1016/0890-5401%2888%2990005-3)
- Harper and Pollack, *Type checking with universes*, 1991, for section 0.9.
  DOI [10.1016/0304-3975(90)90108-T](https://doi.org/10.1016/0304-3975%2890%2990108-T)
- Barendregt and Barendsen, *Autarkic computations in formal proofs*, 2002, for
  the De Bruijn criterion of section 0.16.
  DOI [10.1023/A:1015761529444](https://doi.org/10.1023/A:1015761529444)
- Carneiro, *Metamath Zero*, 2019, for how small a trusted checker can get.
  <https://arxiv.org/abs/1910.10703>
- Every source in one list: [the references](REFERENCES.md).
