# References

Every chapter ends with a reference list. This file holds the whole list, and
one line on what each source answers. The project opened every link on
2026-10-13.

A reader who wants the theory first should read
[Part I of the book](book/README.md) and follow the references at the end of
each chapter. This file is the union of them all.

Three kinds of source appear in a chapter list.

- **Our code.** A path such as `crates/rean_kernel/src/typeck.rs`.
- **Lean's own source.** A path such as `src/kernel/type_checker.cpp`. Read it
  in the repository [leanprover/lean4](https://github.com/leanprover/lean4).
- **A paper, a book, or a manual.** This file holds the link.

A rule for a reader. Lean's source is the only authority on what Lean does
today. A paper says why. A manual says what a user may rely on.

---

## 1. Where Lean keeps each stage

The five stages of the README map onto the Lean source like this.

| Stage | Lean's source | Our crate |
|---|---|---|
| 1, lex | `src/Lean/Parser/Basic.lean`, where `tokenFn` reads the token table | `rean_lexer` |
| 2, parse | `src/Lean/Parser/` | `rean_syntax`, no parser yet |
| 3, elaborate | `src/Lean/Elab/` | missing |
| 4, check | `src/kernel/` | `rean_kernel` |
| 5, run | `src/Lean/Compiler/LCNF/`, `src/library/ir_interpreter.cpp` | `rean_eval` |

The kernel is the small part. It is about 6,000 lines of C++, and every other
directory above is untrusted.

| Kernel file | Holds |
|---|---|
| `src/kernel/expr.h` | the eleven term formers, and the cached word in each node |
| `src/kernel/level.h` | a universe level, and its normal form |
| `src/kernel/type_checker.cpp` | weak head normal form, definitional equality, type inference, the `Nat` rules |
| `src/kernel/inductive.cpp` | an inductive declaration, the recursor it derives, the positivity test, K-like reduction |
| `src/kernel/quot.cpp` | the four `Quot` constants, and the one rule that computes |
| `src/kernel/declaration.h` | the eight kinds of declaration |
| `src/kernel/environment.cpp` | the map from a name to a declaration |
| `src/kernel/instantiate.cpp` | substitution, and universe substitution |

Three files outside the kernel answer questions the chapters ask.

| File | Answers |
|---|---|
| `src/Lean/Expr.lean` | what Lean caches in a term node. The comment on `Expr.Data` gives the bit layout. |
| `src/util/name.h` | a name carries its own hash code, and a comparison uses it first |
| `src/runtime/mimalloc.cpp` | Lean links mimalloc, the allocator of chapter 26 |

- Lean's term node: <https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean>
- Lean's type checker: <https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp>
- Lean's inductive types: <https://github.com/leanprover/lean4/blob/master/src/kernel/inductive.cpp>

---

## 2. The Lean 4 papers

| Source | Read it for |
|---|---|
| de Moura and Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 2021. <https://lean-lang.org/papers/lean4.pdf>, DOI [10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37) | the design of the whole system, in 10 pages |
| Ullrich and de Moura, *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages*, IJCAR 2020. <https://arxiv.org/abs/2001.10490>, DOI [10.1007/978-3-030-51054-1_10](https://doi.org/10.1007/978-3-030-51054-1_10) | why the frontend is extensible, and what hygiene costs |
| Ullrich, *An Extensible Theorem Proving Frontend*, thesis, 2023. <https://lean-lang.org/papers/thesis-sebastian.pdf> | the long form of stages 1 to 3, with the parser in full |
| Ullrich and de Moura, *Counting Immutable Beans*, 2019. <https://arxiv.org/abs/1908.05647> | how stage 5 manages memory, by reference counting |
| Ullrich and de Moura, *`do` Unchained*, 2022. <https://lean-lang.org/papers/do.pdf> | how one notation of stage 3 is built |

---

## 3. What Lean's type theory is

The kernel implements a theory. These sources state it.

| Source | Read it for |
|---|---|
| Carneiro, *The Type Theory of Lean*, 2019. <https://github.com/digama0/lean-type-theory> | the rules, written as rules. The closest thing to a specification. |
| Carneiro, *Lean4Lean: Verifying a Typechecker for Lean, in Lean*, 2024. <https://arxiv.org/abs/2403.14064> | a second kernel, and the proofs about it |
| *The Lean Language Reference*, the type system. <https://lean-lang.org/doc/reference/latest/The-Type-System/> | what a user may rely on, stated by the project |
| *The Lean Language Reference*, axioms. <https://lean-lang.org/doc/reference/latest/Axioms/> | the three axioms, and what each one adds |
| *The Lean Language Reference*, validating proofs. <https://lean-lang.org/doc/reference/latest/ValidatingProofs/> | why an external checker exists, from the project itself |
| Carneiro, *Lean4Less*, 2024. <https://rish987.github.io/files/lean4less.pdf> | what each definitional rule costs, by taking rules away |

---

## 4. Books for a beginner

| Source | Read it for |
|---|---|
| *Theorem Proving in Lean 4*. <https://lean-lang.org/theorem_proving_in_lean4/> | propositions as types, from the first page |
| *Functional Programming in Lean*. <https://lean-lang.org/functional_programming_in_lean/> | Lean as a programming language |
| *Metaprogramming in Lean 4*. <https://leanprover-community.github.io/lean4-metaprogramming-book/> | `Syntax`, macros, and the elaborator, with code |
| *The Lean Language Reference*. <https://lean-lang.org/doc/reference/latest/> | the index to everything else |

---

## 5. The other kernels, and the scoreboard

A Lean proof is a file that any program may check. Several do.

| Source | Read it for |
|---|---|
| The Lean Kernel Arena. <https://arena.lean-lang.org/> | every independent checker, timed on mathlib, with a conformance suite |
| The arena repository. <https://github.com/leanprover/lean-kernel-arena> | the test suite, and how a checker enters |
| `lean4export`. <https://github.com/leanprover/lean4export> | the file format that chapter 11 reads |
| `lean4checker`. <https://github.com/leanprover/lean4checker> | Lean re-checking its own library, outside the compiler |
| `nanoda_lib`, in Rust. <https://github.com/ammkrn/nanoda_lib> | a kernel written for clarity, with its bug reports in the open |
| `trepplein`, in Scala. <https://github.com/gebner/trepplein> | the first independent checker, and the easiest to read |
| `lean4lean`, in Lean. <https://github.com/digama0/lean4lean> | the kernel as a Lean program, with a correctness proof |

The toolchain of this project ships several of them as binaries, which is why
chapter 25 can measure against `leanchecker` on the same machine.

---

## 6. The theory this rests on

A chapter names the rule. These are where the rule comes from.

| Source | Read it for |
|---|---|
| de Bruijn, *Lambda calculus notation with nameless dummies*, 1972. DOI [10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258%2872%2990034-0) | the index that replaces a name. Chapter 0. |
| Coquand and Huet, *The Calculus of Constructions*, 1988. DOI [10.1016/0890-5401(88)90005-3](https://doi.org/10.1016/0890-5401%2888%2990005-3) | the theory Lean extends |
| Pfenning and Paulin-Mohring, *Inductively defined types in the Calculus of Constructions*, 1990. DOI [10.1007/BFb0040259](https://doi.org/10.1007/BFb0040259) | where a recursor and the ι rule come from |
| Paulin-Mohring, *Inductive definitions in the system Coq*, 1993. DOI [10.1007/BFb0037116](https://doi.org/10.1007/BFb0037116) | the rules for an inductive family, and the positivity condition |
| Dybjer, *Inductive families*, 1994. DOI [10.1007/BF01211308](https://doi.org/10.1007/BF01211308) | an index, as against a parameter. Chapter 10, section 10.4. |
| Harper and Pollack, *Type checking with universes*, 1991. DOI [10.1016/0304-3975(90)90108-T](https://doi.org/10.1016/0304-3975%2890%2990108-T) | universe polymorphism, and level variables |
| Coquand, *An algorithm for type-checking dependent types*, 1996. DOI [10.1016/0167-6423(95)00021-6](https://doi.org/10.1016/0167-6423%2895%2900021-6) | the algorithm of chapter 9: reduce the head, then compare |
| Abel, Öhman and Vezzosi, *Decidability of conversion for type theory in type theory*, 2018. DOI [10.1145/3158111](https://doi.org/10.1145/3158111) | why the comparison of chapter 9 terminates |
| Gilbert, Cockx, Sozeau and Tabareau, *Definitional proof-irrelevance without K*, 2019. DOI [10.1145/3290316](https://doi.org/10.1145/3290316) | what proof irrelevance costs a checker. Chapter 10, section 10.7. |
| Barendregt and Barendsen, *Autarkic computations in formal proofs*, 2002. DOI [10.1023/A:1015761529444](https://doi.org/10.1023/A:1015761529444) | the De Bruijn criterion. Chapter 0, section 0.16. |
| Pratt, *Top down operator precedence*, 1973. DOI [10.1145/512927.512931](https://doi.org/10.1145/512927.512931) | the parser that stage 2 needs. Chapter 16. |
| Flatt, *Composable and compilable macros*, 2002. DOI [10.1145/581478.581486](https://doi.org/10.1145/581478.581486) | the other language whose grammar grows while it reads. Chapter 16. |
| Launchbury, *A natural semantics for lazy evaluation*, 1993. DOI [10.1145/158511.158618](https://doi.org/10.1145/158511.158618) | a thunk, forced at most once. Chapter 27. |
| Peyton Jones, *Implementing lazy functional languages on stock hardware*, 1992. <https://www.microsoft.com/en-us/research/publication/implementing-lazy-functional-languages-on-stock-hardware-the-spineless-tagless-g-machine/> | how a lazy runtime is built for real |
| Grégoire and Leroy, *A compiled implementation of strong reduction*, 2002. <https://xavierleroy.org/publi/strong-reduction.pdf> | normalisation by evaluation, the idea the fastest checker uses |
| Filliâtre and Conchon, *Type-safe modular hash-consing*, 2006. <https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf> | one node for every equal term. Chapter 26, section 26.9 prices it. |
| Brady, *Idris 2: Quantitative Type Theory in Practice*, 2021. DOI [10.4230/LIPIcs.ECOOP.2021.9](https://doi.org/10.4230/LIPIcs.ECOOP.2021.9) | a dependently typed language that erases by a different rule |
| Carneiro, *Metamath Zero*, 2019. <https://arxiv.org/abs/1910.10703> | how small a trusted checker can get |

---

## 7. How other systems do it

Each chapter has a section with this name. These are the sources behind them.

| System | Source | What differs |
|---|---|---|
| Rocq, formerly Coq | the reference manual, inductive types. <https://rocq-prover.org/doc/master/refman/language/core/inductive.html> | a guard condition on a fixpoint, in place of a recursor |
| Rocq | conversion rules. <https://rocq-prover.org/doc/master/refman/language/core/conversion.html> | the same Greek letters, β δ ι ζ η, and cumulativity as well |
| Rocq | `SProp`. <https://rocq-prover.org/doc/master/refman/addendum/sprop.html> | proof irrelevance is a second sort there. In Lean it is the rule for `Prop` itself. |
| Agda | termination checking. <https://agda.readthedocs.io/en/latest/language/termination-checking.html> | pattern matching and a termination checker, and no separate kernel |
| Agda | `--without-K`. <https://agda.readthedocs.io/en/latest/language/without-k.html> | K is optional there. Lean's kernel has K-like reduction built in. Chapter 12, section 12.3. |
| Isabelle | the implementation manual. <https://isabelle.in.tum.de/doc/implementation.pdf> | an LCF kernel. A theorem is an abstract value that only inference rules can make. |
| GHC, for Haskell | the debugging flags, `-dcore-lint`. <https://downloads.haskell.org/ghc/latest/docs/users_guide/debugging.html> | a re-checker for its own intermediate language. The nearest thing in a mainstream compiler to a kernel. |
| GHC | *System F with type equality coercions*. <https://www.microsoft.com/en-us/research/publication/system-f-with-type-equality-coercions/> | types carry proofs of equality, and the compiler checks them |
| rustc, for Rust | the developer guide, macro expansion. <https://rustc-dev-guide.rust-lang.org/macro-expansion.html> | a macro works on a token stream. It cannot add a token or a precedence. |
| Metamath Zero | <https://arxiv.org/abs/1910.10703> | a verifier small enough to audit in an afternoon |

---

## 8. The tools this project calls

| Tool | Where | Used by |
|---|---|---|
| Lean, the compiler | <https://github.com/leanprover/lean4> | chapter 24, the front door |
| `lean4export` | <https://github.com/leanprover/lean4export> | chapters 11 and 16 |
| mathlib4 | <https://github.com/leanprover-community/mathlib4> | the arena measures against it. We use the prelude. |
| our own tools | `tools/cite.py`, `tools/roots.py`, `tools/slice.py` | chapters 19 to 17 |
