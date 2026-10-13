# Glossary

Every term the chapters use, in one place. The short definition first, then
where to read more.

New to the project? Read [Part I of the book](book/README.md) first. Eight
short chapters, in order, and every word below is defined there in context.
[The guide](README.md) holds the whole reading order.
[The references](REFERENCES.md) hold every source.

A pointer such as "Part I chapter 4, section 4.4" is the gentle explanation. A
pointer such as "chapter 10, section 10.7" is the code.

## The two worlds

| Term | Meaning |
|---|---|
| **proposition** | a statement. In Lean it is a **type**. |
| **proof** | a reason the statement holds. In Lean it is a **term** of that type. |
| **Curry-Howard** | the name for that correspondence. "Check this proof" becomes "check this type". Part I chapter 1, section 1.3. |
| **data** | a value you compute with, such as `3`. It lives in `Type`. |
| **inhabited** | a type that has at least one element. A proposition is true exactly when its type is inhabited. |

## The two theories

| Term | Meaning |
|---|---|
| **CoC** | the Calculus of Constructions. Functions, dependent function types, and an impredicative `Prop`. Coquand and Huet, 1988. Part I chapter 5. |
| **CoIC** | the Calculus of Inductive Constructions. CoC plus inductive declarations, which is what Lean's kernel implements. Part I chapter 6. |

## Sorts and universes

| Term | Meaning |
|---|---|
| **`Sort u`** | the only universe former the kernel has. Part I chapter 4, section 4.2. |
| **`Prop`** | notation for `Sort 0`. The home of propositions. |
| **`Type n`** | notation for `Sort (n+1)`. The home of data. |
| **universe level** | the `u` of `Sort u`. Built from `0`, `succ`, `max`, `imax`, and a parameter. |
| **`imax u v`** | `0` when `v` is `0`, and `max u v` otherwise. The one special rule, and the reason `Prop` is impredicative. |
| **impredicative** | able to quantify over a collection that holds the thing being defined. `∀ (p : Prop), p → p` is itself a `Prop`. Part I chapter 4, section 4.4. |
| **predicative** | not that. A quantifier over `Type u` lands in a larger universe. |
| **cumulativity** | a rule that `Type 0` is a subtype of `Type 1`. Coq has it. **Lean does not.** |
| **universe polymorphism** | what Lean uses instead: a declaration takes its levels as parameters, as in `List.{u}`. |

## Terms

| Term | Meaning |
|---|---|
| **`Expr`** | the kernel's term type. Eleven variants, and a user cannot add one. |
| **Pi type** | a function type whose result may mention the argument, written `(x : A) → B`. The same term former as `∀`. |
| **de Bruijn index** | a bound variable written as a number: how many binders sit between the use and its own binder. Part I chapter 2, section 2.4. |
| **loose bound variable** | a bound variable that points outside the term it sits in. A closed term has none. |
| **free variable, `FVar`** | a variable from the local context, with an identifier that never changes number. What a binder is opened into. |
| **metavariable, `MVar`** | a hole for unification to fill. A finished proof holds none. |
| **`lift`** | add to every loose index, because a term moved under a new binder. |
| **`instantiate`** | replace index 0 with a term. One beta step is one call. |
| **`abstract`** | the reverse: turn a free variable back into a bound one, closing a binder. |
| **alpha equivalence** | equal up to the names of bound variables. With de Bruijn indices it is almost free. |
| **closed** | a term with no loose bound variable. Only a closed term has a type. Part I chapter 2, section 2.6. |
| **stuck** | a term that no rule can reduce, such as `0 + n` for a variable `n`. Stuck is a correct answer, not an error. Part I chapter 7, section 7.4. |

## Judgments and rules

| Term | Meaning |
|---|---|
| **`Γ ⊢ e : A`** | "in the context `Γ`, the term `e` has the type `A`". |
| **local context, `Γ`** | the list of what is already known. In logic, the hypotheses. |
| **environment** | the map from a `Name` to a declaration. The global one. |
| **`infer_type`** | works out the type of a term. |
| **`is_def_eq`** | decides whether two terms are the same **by computation**. |
| **conversion rule** | the rule that a term keeps its type under computation. The reason a checker must hold an evaluator. Part I chapter 7, section 7.1. |

## Reduction

| Term | Meaning |
|---|---|
| **definitional equality, `≡`** | sameness that the kernel decides by computing. Not a proposition. |
| **propositional equality, `=`** | the inductive type `Eq`. A statement you prove. `rfl : a = b` checks exactly when `a ≡ b`. |
| **whnf** | weak head normal form. Reduce until the outermost shape is stable. "Weak" means not inside a binder. |
| **β beta** | call a function: `(fun x => b) a ≡ b[x := a]`. |
| **δ delta** | unfold a definition to its value. |
| **ζ zeta** | unfold a `let`. |
| **ι iota** | run a recursor on a constructor. |
| **η eta** | `fun x => f x ≡ f`. Also, for a structure, `S.mk p.1 p.2 ≡ p`. |
| **proof irrelevance** | all proofs of one proposition are definitionally equal. |

## Inductive types

| Term | Meaning |
|---|---|
| **inductive type** | a type declared by its constructors. You get a recursor for free. |
| **constructor** | a way to build an element. |
| **parameter** | an argument of the type that is fixed across every constructor. |
| **index** | an argument of the type that varies, such as the `b` of `a = b`. |
| **field** | an argument of a constructor, after the parameters. |
| **recursor** | the eliminator. How you **use** an element. |
| **motive** | the result type of a recursor, as a function of the thing taken apart. |
| **minor premise** | what the recursor needs for one constructor. One per constructor. |
| **major premise** | the element the recursor takes apart. |
| **induction hypothesis** | the extra premise a **recursive** field adds. |
| **strict positivity** | the condition that stops `inductive Bad \| mk : (Bad → False) → Bad`. Part I chapter 6, section 6.7. |
| **nested inductive** | one whose own type sits inside another, as in `List Tree → Tree`. Lean compiles it into an auxiliary type. |
| **mutual group** | types declared together, each recursor taking one motive per type. Chapter 15. |
| **subsingleton** | a type with at most one element. A `Prop` that is one may eliminate into any sort. |
| **large elimination** | eliminating a `Prop` into a bigger universe. Only allowed for a subsingleton. |
| **structure** | an inductive type with one constructor and no index. Its fields determine it. |
| **quotient, `Quot`** | a kernel primitive no inductive declaration can express. |

## Trust

| Term | Meaning |
|---|---|
| **kernel** | the small trusted part that re-checks everything. |
| **De Bruijn criterion** | the rule that every untrusted stage only produces a candidate the kernel re-checks. Part I chapter 8, section 8.1. |
| **axiom** | a name with a type and no proof. The one thing the kernel does not check. |
| **`sorry`** | becomes the axiom `sorryAx`. A proof that reaches it is not a proof. |
| **`unsafe`, `partial`** | a declaration that may not terminate. A proof must not rest on one. |
| **trust report** | the list of axioms a theorem rests on. Lean spells it `#print axioms`. Chapter 14. |

## The pipeline

| Term | Meaning |
|---|---|
| **lexer** | text to a flat list of tokens. Stage 1. **Works here.** |
| **token table** | the set of keywords and symbols the lexer knows. It **grows** while the file is read. Chapter 16, section 16.3. |
| **parser** | tokens to a `Syntax` tree. Stage 2. **Missing here.** |
| **`Syntax`** | the lossless tree. One type for every construct, with the node kind a `Name`. |
| **trivia** | the whitespace and comments around a token. Lean keeps it. We drop it. |
| **elaborator** | `Syntax` to `Expr`. Macro expansion, name resolution, implicit arguments, tactics. Stage 3. **Missing here.** |
| **tactic** | a program that builds a proof term. Untrusted. |
| **`lean4export`** | the tool that writes Lean's elaborated declarations to a file, so another checker can read them. Chapter 11. |
| **level 1, 2, 3** | the three checkpoints of `ROADMAP.md`. Level 1 is "our kernel checks Lean's terms". |

## What a check costs

Chapters 17 to 20 are about cost, and these are the terms they add.

| Term | Meaning |
|---|---|
| **budget** | a count of **work** that each declaration may use, `REAN_FUEL`. Lean's kernel has no work budget. It bounds the term instead, with a recursion depth guard and a maximum numeral size. Ours bounds the work, so that a corrupt file cannot hang us. Chapter 17, sections 17.7 and 17.14. |
| **unit of work** | what the budget counts. A reduction step is charged the **size of the term it produced**, because an ι step can make a term larger, so counting steps bounds nothing. |
| **out of budget** | the verdict when a declaration wants more work than the budget holds. It is **not** a claim that the declaration is wrong. |
| **blocked** | the verdict when a declaration waits on another that did not check. Also not wrong, only unread. One root failure of the prelude blocked 15,272 of them. Chapter 20, section 20.8. |
| **`loose`** | the first number every node caches: one more than the largest loose bound variable index inside, or zero. `loose == 0` means closed. It turns substitution from a walk into a test. Chapter 17, section 17.6. |
| **`size`** | the second cached number, the node count. The budget asks for it after every step, so a walk would cost as much as the work it charges for. |
| **`hash`** | the third cached number, and the key of every cache. It must ignore whatever `alpha_eq` ignores: binder names, and the **shape** of a universe level. Chapter 18, section 18.2. |
| **confirm** | what a cache must do with a hit before it trusts it. Two terms can share a hash, so `alpha_eq` makes the decision. A proof checker may not be probably right. Chapter 18, section 18.3. |
| **spine** | a head and the arguments applied to it. `f x y` is the spine `(f, [x, y])`. |
| **congruence** | the rule that lets a spine be compared without reduction: same head and equal arguments means equal terms. Asking this **before** unfolding was the largest single win of the project. Chapter 19. |
| **eager** | our `whnf`: each step builds a whole new term and drops the old one. Lean's is **lazy** and rebuilds nothing. This is the one job left. Chapter 20, section 20.10. |
| **slice** | a prefix of a `lean4export` file, cut after one declaration. Valid because the format is topologically ordered. `tools/slice.py`. Chapter 19, section 19.1. |
| **root failure** | the failure at the end of a chain of blocked declarations. `tools/roots.py` ranks them by how many leaves each one holds up. |
| **oracle** | an answer from outside the project, which a measurement is held to. Lean's own kernel is the one for speed. Chapter 25, section 25.6. |
| **tally** | the instrument that counts a reduction by rule and by definition, `REAN_TALLY=1`. A profiler says where the time went. A tally says **what** was reduced. Chapter 21. |

## Stage 5, and the words a runtime needs

| Term | Meaning |
|---|---|
| **evaluator** | the part that asks what a term **comes to**, rather than whether it is correct. Stage 5, chapter 27. |
| **thunk** | an argument that is not evaluated yet. It is forced at most once, and then it holds its value. Chapter 27, section 27.3. |
| **by need** | the order our evaluator uses: compute a thunk when somebody reads it, and never before. Haskell is the language built this way. |
| **strict** | the other order: compute every argument before the call. Lean, OCaml and Rust are strict. |
| **erasure** | dropping what cannot affect the answer. Lean's compiler erases a type and a proof, because it knows the types. Our evaluator has no types, so it ignores them instead. |
| **LCNF** | the intermediate form of Lean's own stage 5, between the kernel term and the generated C. |
| **primitive** | an operation the evaluator performs itself, such as the arithmetic on a machine number. Chapter 27, section 27.5. |

## Words from the other kernels

Chapter 22 reads what other people built, and these are the words they use.

| Term | Meaning |
|---|---|
| **normalisation by evaluation** | reduce a term by building a value in the host language, with a closure for a function, and read a term back at the end. The fastest checker in the arena works this way. Chapter 22, section 22.8. |
| **delayed instantiation** | keep a term as a pointer plus a shift, so a lift costs nothing and one cache entry serves every shifted copy. Chapter 22, section 22.7. |
| **hash-consing** | build one object for every equal term, so equality is a pointer comparison. Chapter 26, section 26.9 measures it here, and does not take it. |
| **the arena** | the Lean Kernel Arena. It times every independent checker on the same files, and it holds proofs that each one must **refuse**. <https://arena.lean-lang.org/> |
| **guard condition** | the rule Rocq uses in place of a recursor, to be sure a recursion ends. Chapter 13, section 13.10. |
| **singleton elimination** | Rocq's name for what chapter 13, section 13.3 calls large elimination out of `Prop`. |
| **LCF kernel** | the design Isabelle uses: a theorem is a value that only an inference rule can build. There is no proof term to re-check. |

## Where each word comes from

- The Greek letters, and the rules: Carneiro, *The Type Theory of Lean*.
  <https://github.com/digama0/lean-type-theory>
- The pipeline, and the extensible frontend: de Moura and Ullrich, 2021, and
  Ullrich and de Moura, 2020. <https://lean-lang.org/papers/lean4.pdf>
- What a user may rely on: *The Lean Language Reference*.
  <https://lean-lang.org/doc/reference/latest/>
- Everything else: [the references](REFERENCES.md).
