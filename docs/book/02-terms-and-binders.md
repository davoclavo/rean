# 2. Terms, binders, and names you do not need

> **Where you are.** Chapter 2 of 8 in Part I.
>
> **Before this.** [Chapter 1](01-a-proof-is-a-program.md). You need one idea
> from it: a proof is a term.
>
> **This chapter adds** the language that terms are written in, and the one
> operation on them.
>
> **The four beats.** The idea is section 2.1. Your language is section 2.2.
> The notation is sections 2.3 and 2.4. The code arrives in section 2.6.
>
> **Do not skip ahead.** Chapter 3 adds types to this language. If you skip the
> binder, nothing after it will make sense.

---

## 2.1 The idea

Chapter 1 said a proof is a term. So what is a term?

**A term is a tree with holes in it, and a way to say which hole is which.**

That is the whole idea, and it has three parts.

- A **tree**, because a program is built out of smaller programs.
- A **hole**, because a function does not know its argument yet. The hole is
  where the argument will go.
- A **way to say which hole is which**, because a tree may have several, one
  inside another.

The thing that makes a hole is called a **binder**. The thing that fills a hole
is called **substitution**, and it is the only operation in this chapter.

Now the part that surprises people. **The name of a hole is not part of the
meaning.** A form that asks for "your first name" and a form that asks for
"given name" collect the same thing. The label is for the reader. What matters
is which box the answer lands in.

A picture. Think of a term as a set of nested envelopes, and a binder as an
envelope that is still open.

```
  fun x => fun y => x
  └──────────────────┘   two open envelopes, and the body reaches into the outer one
```

So a term language needs exactly two decisions.

1. How do you write a tree, a binder, and a call?
2. How do you fill a hole without filling the wrong one?

Section 2.3 answers the first. Section 2.4 answers the second, and the answer
is to throw the names away.

---

## 2.2 In your language

Three things you have already relied on, and you may not have noticed any of
them.

**A minifier renames every local variable in your bundle, and nothing breaks.**
`esbuild` turns `function greet(userName)` into `function a(b)`. Your
application still runs. The names were never the meaning.

**A closure captures a slot, not a name.** This is plain JavaScript:

```ts
const makeCounter = () => { let n = 0; return () => ++n }
```

The inner function finds `n` by where it sits, and the minifier proves it. A
compiled program does the same thing with an offset from a stack pointer.

**A code generator has to solve the hole problem, and it is a real bug.** Write
a Babel plugin that wraps an expression in a temporary variable. Name the
temporary `t` and you have a bug the first time a user already has a `t` in
scope. The cure in Babel is `path.scope.generateUidIdentifier`, which invents a
name nobody else owns. Lean solves the same bug with a macro scope. Section 2.3
is the bug, with no plugin around it.

---

## 2.3 The notation

**The whole language, in three lines.** A term is one of three things.

```
e ::= x            a variable
    | fun x => e   a function, which binds x
    | e₁ e₂        an application, which calls e₁ with e₂
```

That is the untyped lambda calculus, and it is all of the language for now.
Chapters 3 and 4 add two more forms, and chapter 6 adds the last one. Nothing
else ever arrives.

Three examples:

```
fun x => x                  the identity
fun x => fun y => x         take two things, return the first
(fun x => x) y              a call, ready to happen
```

One operation computes. A function meets an argument, and the argument goes
into the body.

```
(fun x => x) y   ⟶   y
```

The name for that step is **[β reduction](../GLOSSARY.md#beta)**.

**Bound and free.** In `fun x => x y`, the two variables are not alike.

- `x` is **bound**. The `fun x =>` in front of it says what it means.
- `y` is **free**. Its meaning comes from outside the term.

A bound variable has a name only for your eyes. These two terms do the same
thing, for every input:

```
fun x => x
fun y => y
```

They are **[alpha equivalent](../GLOSSARY.md#alpha-equivalence)**, which means
equal up to the names of bound variables. A checker must treat them as one
term. That is section 2.1 as a definition. Hold on to the word. It is about to
do real work.

**Substitution, and the trap in it.** Write
[substitution](../GLOSSARY.md#substitution) like this.

```
b[x := a]
```

Read it: "the term `b`, but every free `x` in it becomes `a`".

Now the trap. Substitute `y` for `x` in `fun y => x`.

```
(fun y => x)[x := y]
```

A careless answer is `fun y => y`. That is **wrong**. The `y` that arrived from
outside has nothing to do with the `y` that the binder owns. The careless
answer turned a function that ignores its argument into the identity function.

The name for the bug is **[capture](../GLOSSARY.md#capture)**, and it is the
Babel bug of section 2.2 with no plugin around it. Two cures exist.

1. Rename the binder before you substitute. This works, and it is slow, and it
   is easy to get subtly wrong.
2. **Delete the names.** Lean does this, and so does our checker.

---

## 2.4 de Bruijn indices

Replace the name of a bound variable with a number, and the name for that
number is a [de Bruijn index](../GLOSSARY.md#de-bruijn-index). It is the count
of binders between the use and the binder that owns it.

```
fun x => fun y => x        becomes   λ λ #1
fun x => fun y => y        becomes   λ λ #0
```

Count from the use, outward, starting at zero. In the first term, `x` sits
under two binders. Its own binder is one step out, past `fun y =>`. So the
index is 1.

Three things get better at once.

- **Alpha equivalence becomes equality.** `fun x => x` and `fun y => y` are
  both `λ #0`. The same data. A comparison is now a comparison of numbers.
- **Capture cannot happen.** There is no name to capture.
- **Substitution becomes arithmetic.** The numbers shift, and nothing is
  renamed.

---

## 2.5 Three ways to see an index

**As street directions.** A name is "the house of the Hernández family". An
index is "two blocks back". The second one does not care who lives there, and
it stays correct when you copy the directions into another neighbourhood.

**As a stack.** Each binder pushes a frame. `#0` is the top frame, `#1` is the
one under it. This is how a compiled program finds a local variable already, as
an offset from a stack pointer.

**As a minified bundle.** `esbuild` renamed every local in your application and
nothing broke. A de Bruijn index is the end of that road. Do not pick a shorter
name. Pick no name.

---

## 2.6 The three operations, in code

A kernel needs exactly three operations on indices. Our code holds them in
`crates/rean_kernel/src/expr.rs`.

| Operation | What it does | When |
|---|---|---|
| `lift` | add to every loose index | a term moves under a new binder |
| `instantiate` | replace index 0 with a term | one β step is one call |
| `abstract_fvar` | the reverse. Turn a variable back into an index. | a binder closes again |

One more word, because the chapters use it. An index is
**[loose](../GLOSSARY.md#loose-bound-variable)** when it points outside the
term it sits in. In `λ #3`, the index 3 is loose. A finished term has no loose
index, and a term with none is **[closed](../GLOSSARY.md#closed)**.

That word earns its place twice over later. A closed term has a type. A term
with a loose index does not, because the thing it points at is not there.

Lean does the same three operations, in `src/kernel/instantiate.cpp`. Two
kernels, two languages, three functions.

---

### If you write TypeScript

**Your toolchain already deletes the names.** Section 2.2 named three places,
and here is what each one maps onto.

| In your toolchain | Here |
|---|---|
| a minifier renames every local | [alpha equivalence](../GLOSSARY.md#alpha-equivalence), section 2.3 |
| `path.scope.generateUidIdentifier` in a Babel plugin | the cure for [capture](../GLOSSARY.md#capture), section 2.3, cure 1 |
| a closure that finds a variable by its slot | a [de Bruijn index](../GLOSSARY.md#de-bruijn-index), section 2.4 |
| a source map, which puts the names back for a human | our pretty printer, which keeps a name in a field the comparison skips |

**A generator in `Effect.gen` is a chain of binders.** Read this:

```ts
import { Effect } from "effect"

const program = Effect.gen(function* () {
  const a = yield* Effect.succeed(1)
  const b = yield* Effect.succeed(a + 1)
  return a + b
})
```

Each `yield*` becomes a function that takes the value and returns the rest of
the program. So `const b = ...` is a binder, and the `return` line reaches back
into two of them. `Effect` hides the lambda, and the lambda is still what runs.
The three-line language of section 2.3 is what your generator compiles into.

**One difference worth naming.** A minifier may rename a variable, because it
only has to keep the program's meaning. A proof checker compares two terms
thousands of times per declaration, so it does not rename. It removes the
names, which turns the comparison into a comparison of numbers.
[The type checker chapter](../09-the-type-checker.md) holds that comparison,
and it is called `alpha_eq`.

---

## 2.7 Try it

No command prints a de Bruijn index, because nobody reads one by choice. The
code builds one, and a test holds it:

```sh
devbox run -- cargo test -p rean_kernel --test universes
```

```rust
let with_x = Expr::lam("x", nat(), Expr::bvar(0));
let with_y = Expr::lam("y", nat(), Expr::bvar(0));
// The bodies are the same data. Only the printer keeps the name.
let (Expr::Lam { body: a, .. }, Expr::Lam { body: b, .. }) = (&with_x, &with_y) else {
    panic!("both terms are lambdas");
};
assert_eq!(a, b);
```

That is the test `de_bruijn_erases_the_binder_name_from_the_body`, and it is
section 2.3 as an assertion. Two terms, two names, one body.

Then watch a substitution run. The `demo` command does one β step and reports
whether the result is closed:

```sh
devbox run -- cargo run -p rean -- demo
```

```text
== stage 3: kernel term ==
pretty   : fun (f : Nat → Nat) => fun (x : Nat) => f (f x)
type     : (Nat → Nat) → Nat → Nat
closed   : true

== stage 4: one beta step ==
before   : (fun (f : Nat → Nat) => fun (x : Nat) => f (f x)) Nat.succ
after    : fun (x : Nat) => Nat.succ (Nat.succ x)
```

The `after` line is one `instantiate` call. The printer puts the names back, so
you can read it. Inside, the argument went to index 0 and every other index
moved.

## 2.8 Check yourself

1. Write `fun x => fun y => y x` with de Bruijn indices.
2. Why can a checker use `==` on two terms once the names are gone?
3. A term holds `#2` at the top level, under no binder. What is wrong with it?

### Answers

1. `λ λ #0 #1`. The body applies `y`, which is the nearest binder, to `x`,
   which is one further out.
2. Because two terms that differ only in binder names are now the same data.
   Our code still keeps a name for the printer, so it compares with `alpha_eq`
   and skips that one field.
3. The index is loose, so the term is not closed, and nothing can give it a
   type. A kernel treats that as a bug in its caller.

---

## 2.9 References

- de Bruijn, *Lambda calculus notation with nameless dummies*, 1972. The paper
  that this chapter is named after.
  DOI [10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258%2872%2990034-0)
- Nederpelt and Geuvers, *Type Theory and Formal Proof*, chapters 1 and 6, for
  the untyped calculus and for de Bruijn indices at book length.
  <https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C>
- Babel, `babel-traverse`, for `generateUidIdentifier` and why it exists.
  <https://babeljs.io/docs/babel-traverse>
- Effect, the `Effect` type, for the generator of the TypeScript section.
  <https://effect.website/docs/getting-started/the-effect-type/>
- Our code. `crates/rean_kernel/src/expr.rs` holds the three operations, and
  `crates/rean_kernel/tests/substitution.rs` holds their tests.
- Lean's own source. `src/kernel/instantiate.cpp` is the same three operations
  in C++.

---

**Next:** [3. Types that depend on values](03-types-that-depend-on-values.md)
