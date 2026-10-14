# 8. What you must trust

> **Where you are.** Chapter 8 of 8 in Part I. The last one.
>
> **Before this.** Chapters [1](01-a-proof-is-a-program.md) to
> [7](07-definitional-equality.md). This chapter puts them in a machine.
>
> **This chapter adds** the shape of the whole system, and an honest answer to
> "why should I believe any of this".
>
> **The four beats.** The idea is section 8.1. Your language is in the
> TypeScript section, and this time it is the strongest mapping in Part I. The
> machine is section 8.2, and the honest hole is section 8.4.
>
> **After it** you are ready for Part II, which builds a checker in Rust, line
> by line.

---

## 8.1 The idea

Lean is a large program. It has a parser, a macro system, an elaborator, a
unifier, hundreds of tactics, and a compiler. Hundreds of people have changed
it.

So why would you believe a theorem it accepts?

**The idea in one line.** Let the clever part be wrong, and check its output
with a part small enough to read.

That is the best idea in the field, and it is worth saying slowly. **None of
that large code is trusted.** Each part only produces a **candidate** term. One
small program then re-checks that candidate from nothing, with the rules of
chapters 5 to 7. A bug anywhere in the large part produces a term that the
small part refuses. It cannot produce a false theorem.

A picture. A company may be enormous. The auditor is one person with a short
checklist. The company does the work. The auditor does not repeat the work, and
does not have to, because the checklist covers what matters.

```
   everything clever   ──►  a candidate term  ──►  a small checker  ──►  yes or no
   large, untrusted         data, readable         6,000 lines           the answer
```

The name for the rule is the **[De Bruijn
criterion](../GLOSSARY.md#de-bruijn-criterion)**, and two things make it work.

- **The candidate is data.** A term can be written to a file. So the checker
  does not have to live in the same program as the thing that made it.
- **The checker is small.** Several people have read all of Lean's, which is
  the only reason "trust it" is a reasonable thing to ask.

---

## 8.2 The five stages, and the one that counts

```
  text ──1──> tokens ──2──> Syntax ──3──> Expr ──4──> yes or no
                                            │
                                            └──5──> a program that runs
```

| Stage | Name | Where it lives in Lean | Trusted |
|---|---|---|---|
| 1 | lex | `src/Lean/Parser/Basic.lean` | no |
| 2 | parse | `src/Lean/Parser/` | no |
| 3 | elaborate | `src/Lean/Elab/` | no |
| 4 | **check** | `src/kernel/` | **yes** |
| 5 | run | `src/Lean/Compiler/LCNF/` | not for a proof |

Stage 3, the [elaborator](../GLOSSARY.md#elaborator), is the biggest part of
Lean by far. It resolves names, fills in implicit arguments, runs your
[tactics](../GLOSSARY.md#tactic), and expands your macros. A bug in it cannot
make a false theorem. It can only make a term that stage 4 refuses.

Stage 4 is about 6,000 lines of C++. That is the part you must trust, and it is
small enough that several people have read all of it.

---

## 8.3 What is in the trusted set

Four things, and you have met all four.

| The trusted part | The chapter |
|---|---|
| type inference, one arm per rule | [5](05-the-calculus-of-constructions.md) |
| definitional equality, and `whnf` | [7](07-definitional-equality.md) |
| the soundness checks on an inductive declaration | [6](06-inductive-types.md) |
| the axioms, which the kernel does **not** check | section 8.4 |

Nothing else. Not `simp`, not `omega`, not `decide`, not the pretty printer.

---

## 8.4 Axioms, and the one honest hole

An [axiom](../GLOSSARY.md#axiom) is a name with a type and no proof. The kernel
accepts it without a question, because that is what an axiom is.

Lean's library rests on three, and you can ask any theorem which ones it uses:

```lean
#print axioms Classical.em
-- 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| Axiom | What it adds |
|---|---|
| `propext` | two propositions that imply each other are equal |
| `Quot.sound` | two equivalent values have the same quotient |
| `Classical.choice` | you may pick an element from a non-empty type. This gives the excluded middle. |

Four more names appear in a real run, and they are the interesting ones. Our
checker reads the whole Lean prelude and reports every axiom it finds:

```text
trust: 7 axiom(s): Classical.choice, Lean.ofReduceBool, Lean.ofReduceNat,
                   Lean.trustCompiler, Quot.sound, propext, sorryAx
```

- `sorryAx` is what [`sorry`](../GLOSSARY.md#sorry) becomes. A proof that
  reaches it is **not a proof**, and this is why a
  [trust report](../GLOSSARY.md#trust-report) matters.
- `Lean.ofReduceBool`, `Lean.ofReduceNat` and `Lean.trustCompiler` trust the
  **compiler** rather than the kernel. The tactic `native_decide` uses them. A
  proof that rests on one asks you to trust the compiler too, and the report
  says so out loud.

That is the whole hole, and it is visible. Nothing hides.

---

## 8.5 Two accountants are better than one

Stage 4 re-checks stages 1 to 3. So who checks stage 4?

Another kernel, written by somebody else, in another language. Lean makes that
possible by writing its elaborated terms to a file that any program can read.
The tool is `lean4export`, and the file is plain text.

- `lean4checker` re-checks a compiled Lean library with a fresh kernel.
- **This repository** is one of those second opinions. Part II builds it.
- The Lean Kernel Arena runs every independent checker against the same files.
  It holds proofs that each one must **refuse**, and proofs that each one must
  accept. <https://arena.lean-lang.org/>

If two kernels written by different people in different languages agree, the
chance that both hold the same bug is small. That is the whole argument, and it
is why a second checker is worth building even though Lean already has one.

---

### If you write TypeScript

This is the strongest mapping in Part I, because **you already use this idea
and you may not have named it.**

**Generated code is the De Bruijn criterion.** You generate TypeScript from an
OpenAPI document, a Prisma schema, a GraphQL document, or a protobuf file. The
generator is thousands of lines and you did not read it. You do not have to,
because `tsc` reads the output and a bad generator produces a file that fails
to compile.

Write the two pipelines next to each other and they are the same shape.

```
   a schema   ──►  a generator      ──►  a .ts file  ──►  tsc    ──►  yes or no
   your proof ──►  Lean's frontend  ──►  an Expr     ──►  kernel ──►  yes or no
```

Lean takes the idea further in one way and further still in another.

| | your pipeline | Lean |
|---|---|---|
| the untrusted part | the generator | the parser, the elaborator, every tactic, every macro |
| the checker | `tsc`, all of it | `src/kernel` only |
| how large is the checker | hundreds of thousands of lines | about 6,000 |
| can a second tool check the same output? | no. There is one `tsc`. | **yes**, from an export file. Section 8.5. |

**The axiom report is the part with no counterpart in your toolchain.** You can
write `as unknown as T`, or a bare `any`, or `@ts-expect-error`, and nothing
downstream records that you did. A caller of your function sees a clean
signature. Lean's `#print axioms` names every hole a theorem depends on, and
`sorry` shows up there by name:

```lean
theorem hopeful : 2 + 2 = 4 := by sorry
#print axioms hopeful     -- 'hopeful' depends on axioms: [sorryAx]
```

A proof with a hole is not a proof, and the tool says so without being asked.
[What a theorem rests on](../14-what-a-theorem-rests-on.md) builds that report
for our own checker.

**And the export file is differential testing.** Two implementations, written
by different people in different languages, read the same input and must agree.
You do this for a parser or a protocol already. Here the input is a proof, and
the agreement is the argument for believing it.

---

## 8.6 Three ways to see trust

**As an auditor.** A company may be large. The auditor is one person with a
checklist, and the checklist is short enough to read.

**As a receipt.** A proof is data. You can keep it, mail it, and check it again
in ten years with a different program.

**As a firewall.** Everything clever sits on the untrusted side. The clever
part is allowed to be wrong, and that freedom is what lets Lean have tactics at
all.

---

## 8.7 Check yourself

1. A tactic has a bug. What is the worst that can happen?
2. Why is an axiom not a failure of the design?
3. Why does an export file matter so much?

### Answers

1. It builds a term that the kernel refuses. You get an error. You do not get a
   false theorem.
2. Because the kernel reports every axiom a theorem rests on. The trust is
   named, counted, and visible. A hidden assumption would be the failure.
3. Because it lets a **different** program check the same proof. One kernel
   checking itself proves little. Two independent kernels that agree prove a
   great deal.

---

## 8.8 Where to go next

Part I is done. You now know the theory that Lean's kernel implements.

Part II builds that kernel in Rust, and it starts with the two functions of
chapter 5 and chapter 7.

| Read next | It adds |
|---|---|
| [The type checker](../09-the-type-checker.md) | `infer_type`, `is_def_eq`, `whnf`, and the first real proof |
| [The environment](../10-the-environment.md) | a name with a value, and every reduction rule |
| [The guide](../README.md) | the full order, part by part |

One more thing, and it is the most useful habit in this book. **Run the
commands.** Read a chapter, run its `Try it` section, and change a number to
see what breaks. A rule you have watched fail is a rule you keep.

---

## 8.9 References

- Barendregt and Barendsen, *Autarkic computations in formal proofs*, 2002, for
  the De Bruijn criterion.
  DOI [10.1023/A:1015761529444](https://doi.org/10.1023/A:1015761529444)
- *The Lean Language Reference*, axioms.
  <https://lean-lang.org/doc/reference/latest/Axioms/>
- *The Lean Language Reference*, validating proofs, for the project's own case
  for an external checker.
  <https://lean-lang.org/doc/reference/latest/ValidatingProofs/>
- de Moura and Ullrich, *The Lean 4 Theorem Prover and Programming Language*,
  2021, for the five stages.
  <https://lean-lang.org/papers/lean4.pdf>
- Carneiro, *Metamath Zero*, 2019, for how small a trusted checker can get.
  <https://arxiv.org/abs/1910.10703>
- `lean4export` and `lean4checker`.
  <https://github.com/leanprover/lean4export>,
  <https://github.com/leanprover/lean4checker>

---

**Next:** [Part II — the kernel, built](../09-the-type-checker.md)
