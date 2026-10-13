# 8. What you must trust

> **Where you are.** Chapter 8 of 8 in Part I. The last one.
>
> **Before this.** Chapters [1](01-a-proof-is-a-program.md) to
> [7](07-definitional-equality.md). This chapter puts them in a machine.
>
> **This chapter adds** the shape of the whole system, and an honest answer to
> "why should I believe any of this".
>
> **After it** you are ready for Part II, which builds a checker in Rust, line
> by line.

---

## 8.1 The question

Lean is a large program. It has a parser, a macro system, an elaborator, a
unifier, hundreds of tactics, and a compiler. Hundreds of people have changed
it.

So why would you believe a theorem it accepts?

The answer is the best idea in the field, and it fits in one sentence. **None of
that code is trusted.** Each part only produces a **candidate** term, and one
small program re-checks the candidate from nothing, with the rules of chapters 5
to 7.

The name for the rule is the **De Bruijn criterion**.

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

Stage 3 is the biggest part of Lean by far. It resolves names, fills in implicit
arguments, runs your tactics, and expands your macros. A bug in it cannot make a
false theorem. It can only make a term that stage 4 refuses.

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

An axiom is a name with a type and no proof. The kernel accepts it without a
question, because that is what an axiom is.

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

- `sorryAx` is what `sorry` becomes. A proof that reaches it is **not a proof**,
  and this is why a report that names the axioms matters.
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
- The Lean Kernel Arena runs every independent checker against the same files,
  and it holds proofs that each one must **refuse** as well as proofs each one
  must accept. <https://arena.lean-lang.org/>

If two kernels written by different people in different languages agree, the
chance that both hold the same bug is small. That is the whole argument, and it
is why a second checker is worth building even though Lean already has one.

---

## 8.6 Three ways to see trust

**As an auditor.** A company may be large. The auditor is one person with a
checklist, and the checklist is short enough to read.

**As a receipt.** A proof is data. You can keep it, mail it, and check it again
in ten years with a different program.

**As a firewall.** Everything clever sits on the untrusted side. The clever part
is allowed to be wrong, and that freedom is what lets Lean have tactics at all.

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
commands.** Read a chapter, run its `Try it` section, and change a number to see
what breaks. A rule you have watched fail is a rule you keep.

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
