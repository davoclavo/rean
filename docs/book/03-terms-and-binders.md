# 3. Terms, binders, and names you do not need

> **Where you are.** Chapter 3 of 9 in Part I.
>
> **Before this.** [Chapter 1](01-a-proof-is-a-program.md). You need one idea
> from it: a proof is a term.
>
> **This chapter adds** the language that terms are written in, and the one
> operation on them.
>
> **The four beats.** The idea is section 3.1. The data is section 3.2. The
> rule is sections 3.3 and 3.4. The code is sections 3.6 and 3.7.
>
> **Do not skip ahead.** Chapter 4 adds types to this language. If you skip the
> binder, nothing after it will make sense.

---

## 3.1 The idea

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

Section 3.3 answers the first. Section 3.4 answers the second, and the answer
is to throw the names away.

---

## 3.2 The data, in your language

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
name nobody else owns. Lean solves the same bug with a macro scope. Section 3.3
is the bug, with no plugin around it.

---

## 3.3 The rule

**The whole language, in three lines.** A term is one of three things.

```
e ::= x            a variable
    | fun x => e   a function, which binds x
    | e₁ e₂        an application, which calls e₁ with e₂
```

That is the untyped lambda calculus, and it is all of the language for now.
Chapters 4 and 5 add two more forms, and chapter 7 adds the last one. Nothing
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
term. That is section 3.1 as a definition. Hold on to the word. It is about to
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
Babel bug of section 3.2 with no plugin around it. Two cures exist.

1. Rename the binder before you substitute. This works, and it is slow, and it
   is easy to get subtly wrong.
2. **Delete the names.** Lean does this, and so does every kernel in this
   family.

---

## 3.4 de Bruijn indices

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

## 3.5 Three ways to see an index

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

## 3.6 The three operations, in code

A kernel needs exactly three operations on indices, and no more.

| Operation | What it does | When |
|---|---|---|
| lift | add to every loose index | a term moves under a new binder |
| instantiate | replace index 0 with a term | one β step is one call |
| abstract | the reverse. Turn a variable back into an index. | a binder closes again |

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

**Your toolchain already deletes the names.** Section 3.2 named three places,
and here is what each one maps onto.

| In your toolchain | Here |
|---|---|
| a minifier renames every local | [alpha equivalence](../GLOSSARY.md#alpha-equivalence), section 3.3 |
| `path.scope.generateUidIdentifier` in a Babel plugin | the cure for [capture](../GLOSSARY.md#capture), section 3.3, cure 1 |
| a closure that finds a variable by its slot | a [de Bruijn index](../GLOSSARY.md#de-bruijn-index), section 3.4 |
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
The three-line language of section 3.3 is what your generator compiles into.

**One difference worth naming.** A minifier may rename a variable, because it
only has to keep the program's meaning. A proof checker compares two terms
thousands of times per declaration, so it does not rename. It removes the
names, which turns the comparison into a comparison of numbers.
[The type checker chapter](../10-the-type-checker.md) holds that comparison,
and it is called `alpha_eq`.

---

## 3.7 Try it

Paste this into a TypeScript playground. It is sections 3.3 and 3.4, in thirty
lines.

```ts
type E =
  | { k: "bvar"; index: number }
  | { k: "lam"; name: string; body: E }
  | { k: "app"; fun: E; arg: E }
  | { k: "const"; name: string }

// Two functions that differ only in the name of the binder.
const withX: E = { k: "lam", name: "x", body: { k: "bvar", index: 0 } }
const withY: E = { k: "lam", name: "y", body: { k: "bvar", index: 0 } }

// The bodies are the same data. Only the printer keeps the name.
console.log(JSON.stringify(withX.body) === JSON.stringify(withY.body)) // true
```

That is section 3.4 as one comparison. Two terms, two names, one body.

Now the operation. `instantiate` puts a term in for index 0, and every index
above it drops by one, because one binder has gone away.

```ts
function instantiate(e: E, value: E, depth = 0): E {
  switch (e.k) {
    case "bvar":
      if (e.index === depth) return value
      return { k: "bvar", index: e.index > depth ? e.index - 1 : e.index }
    case "lam":
      return { ...e, body: instantiate(e.body, value, depth + 1) }
    case "app":
      return {
        k: "app",
        fun: instantiate(e.fun, value, depth),
        arg: instantiate(e.arg, value, depth),
      }
    default:
      return e
  }
}

// One β step: apply `fun x => x` to a constant.
const succ: E = { k: "const", name: "succ" }
console.log(instantiate(withX.body, succ)) // { k: "const", name: "succ" }
```

**Then break it.** Call it with a `value` that holds a loose index of its own,
such as `{ k: "bvar", index: 0 }`, and go under one binder. The index travels
inside unchanged, so it now counts from a different place and points at the
wrong binder. The cure is the first of the three operations: lift the value by
one for each binder you pass. This is the whole reason a kernel keeps three
operations rather than one, and it is the bug that section 3.3 warns about.

## 3.8 Check yourself

1. Write `fun x => fun y => y x` with de Bruijn indices.
2. Why can a checker use `==` on two terms once the names are gone?
3. A term holds `#2` at the top level, under no binder. What is wrong with it?

### Answers

1. `λ λ #0 #1`. The body applies `y`, which is the nearest binder, to `x`,
   which is one further out.
2. Because two terms that differ only in binder names are now the same data.
   A kernel still keeps the name for its printer, so its comparison skips that
   one field.
3. The index is loose, so the term is not closed, and nothing can give it a
   type. A kernel treats that as a bug in its caller.

---

## 3.9 References

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
- Lean's own source. `src/kernel/instantiate.cpp` is the same three operations
  in C++.

---

**Next:** [4. Types that depend on values](04-types-that-depend-on-values.md)
