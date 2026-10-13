# 1. A proof is a program

> **Where you are.** Chapter 1 of 8 in Part I. This is the first one, so it
> assumes nothing.
>
> **This chapter adds** one idea: a proposition is a type, and a proof is a
> term of that type.
>
> **Do not skip ahead.** Every later chapter uses this idea. If a word here is
> new, that is normal. [The glossary](../GLOSSARY.md) holds every word.

---

## 1.1 The question

A proof checker reads a file and answers one question for each theorem: yes or
no.

It does not search for a proof. It does not help you write one. A person or a
tactic writes the proof, and the checker only says whether the proof is
correct.

That sounds like a hard job for a special program. It is not. **You already use
a proof checker every day.** It is called a type checker.

---

## 1.2 You have done this before

Read this signature. It is Rust, and the body is missing.

```rust
fn id<A>(x: A) -> A
```

Now answer a question. What can the body do?

It cannot look inside `x`, because it does not know what `A` is. It cannot build
an `A`, for the same reason. It can only give back the `x` it got.

**The type forced the behaviour.** Nobody ran the function to learn that. The
signature alone said it.

Read the signature once more, and read it as a sentence about logic:

```
for every A, if you give me an A, I give you an A
```

That is the statement "A implies A". And the function is the reason the
statement holds. Write the same thing in Lean:

```lean
theorem id_thm (A : Prop) (h : A) : A := h
```

Same shape. The type is the claim. The term is the proof.

One honest note, because it matters later. A Rust function may loop for ever or
panic, so a Rust type is a weaker promise than it looks. Lean refuses both, and
[chapter 6](06-inductive-types.md) is where that refusal gets its teeth.

---

## 1.3 The dictionary

The idea has a name, the Curry-Howard correspondence, and it is a dictionary
between two worlds.

| Logic | Type theory | In a language you know |
|---|---|---|
| `A` holds | some term has type `A` | the type is **inhabited** |
| `A → B` | a function from `A` to `B` | `fn f(a: A) -> B` |
| `A ∧ B` | a pair that holds both | `(A, B)`, a struct |
| `A ∨ B` | a value that is one side or the other | an enum with two cases |
| `True` | a type with one element | the unit type |
| `False` | a type with **no** element | `Void`, or `never` |
| `¬ A` | `A → False` | a function nobody can call with a result |
| `∀ x : A, P x` | a function that takes `x` and returns a proof of `P x` | a generic, and more. [Chapter 3](03-types-that-depend-on-values.md). |

Read the `False` row twice. A false proposition is not an error and not a crash.
It is a type that nothing inhabits. To prove `¬ A`, write a function from `A`
to a type that has no elements. If you ever get a value of `A`, you can hand
back something impossible, and that is exactly what "A is false" means.

---

## 1.4 Three ways to see it

Pick whichever one sticks. They are the same idea.

**As a recipe.** A proof is not a page of text. It is a recipe that the checker
can follow. "Give me a proof of `A`, and here is how I build a proof of `B`."

**As a room.** A proposition is a room. A proof is somebody standing in it. The
proposition is true when the room is not empty. The checker does not argue about
the room. It looks for a person in it.

**As a compiler.** You run a proof checker every time you build your project.
`cargo check` already proves small theorems about your program, such as "this
value is never null here". Lean lets the theorems get as large as you like, and
the checking stays the same job.

---

## 1.5 What changes when you believe this

Three consequences, and all three shape the rest of the book.

1. **A proof checker is a type checker.** One program, one algorithm.
   [Chapter 5](05-the-calculus-of-constructions.md) writes down its rules.
2. **A proof is data.** You can print it, store it, send it to another program,
   and check it again. [Chapter 8](08-what-you-must-trust.md) is about why that
   matters so much.
3. **The checker must sometimes run your program.** A type can hold a value, so
   to compare two types the checker may have to compute.
   [Chapter 7](07-definitional-equality.md) is that story, and it is the reason
   a proof checker is not a weekend project.

---

## 1.6 Try it

The checker in this repository can already do the proof of section 1.2.

```sh
devbox run -- cargo run -p rean -- prove
```

```text
== the proof ==
fun (α : Prop) => fun (h : α) => h

== the proposition ==
(α : Prop) → α → α

== infer_type ==
the proof has type : (α : Prop) → α → α

== check ==
accepted. The proposition holds.
the proposition lives in : Prop
```

Read the third block. Nobody wrote that type in the test. The checker
**computed** it from the term, and then compared it with the claim.

The last line is chapter 4. Leave it for now.

---

## 1.7 Check yourself

You are ready for chapter 2 when you can answer these three without scrolling
up.

1. What does it mean for a proposition to be false, in terms of types?
2. `fun h => h` proves `A → A`. What proves `A → (B → A)`?
3. Why is a proof checker allowed to be small?

### Answers

1. Its type has no elements. Nothing inhabits it.
2. `fun a => fun b => a`. It takes a proof of `A`, takes a proof of `B`, throws
   the second away, and returns the first.
3. Because it only **checks**. It never searches. The search happens in
   untrusted code, and the checker re-reads the answer.

---

## 1.8 References

- *Theorem Proving in Lean 4*, the chapter on propositions and proofs. The same
  idea, with Lean's own words.
  <https://lean-lang.org/theorem_proving_in_lean4/>
- *Functional Programming in Lean*, for Lean as a language you program in.
  <https://lean-lang.org/functional_programming_in_lean/>
- Our code. `crates/rean_kernel/src/typeck.rs` holds the checker, and
  `crates/rean_kernel/tests/typeck.rs` holds the proof of section 1.2.
- Every source for Part I is in [the references](../REFERENCES.md).

---

**Next:** [2. Terms, binders, and names you do not need](02-terms-and-binders.md)
