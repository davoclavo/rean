# Glossary

Every term the chapters use, in one place. The short definition first, then
where to read more.

## The two worlds

| Term | Meaning |
|---|---|
| **proposition** | a statement. In Lean it is a **type**. |
| **proof** | a reason the statement holds. In Lean it is a **term** of that type. |
| **Curry-Howard** | the name for that correspondence. "Check this proof" becomes "check this type". Chapter 0, section 0.2. |
| **data** | a value you compute with, such as `3`. It lives in `Type`. |
| **inhabited** | a type that has at least one element. A proposition is true exactly when its type is inhabited. |

## Sorts and universes

| Term | Meaning |
|---|---|
| **`Sort u`** | the only universe former the kernel has. Chapter 0, section 0.9. |
| **`Prop`** | notation for `Sort 0`. The home of propositions. |
| **`Type n`** | notation for `Sort (n+1)`. The home of data. |
| **universe level** | the `u` of `Sort u`. Built from `0`, `succ`, `max`, `imax`, and a parameter. |
| **`imax u v`** | `0` when `v` is `0`, and `max u v` otherwise. The one special rule, and the reason `Prop` is impredicative. |
| **impredicative** | able to quantify over a collection that holds the thing being defined. `∀ (p : Prop), p → p` is itself a `Prop`. Chapter 0, section 0.10. |
| **predicative** | not that. A quantifier over `Type u` lands in a larger universe. |
| **cumulativity** | a rule that `Type 0` is a subtype of `Type 1`. Coq has it. **Lean does not.** |
| **universe polymorphism** | what Lean uses instead: a declaration takes its levels as parameters, as in `List.{u}`. |

## Terms

| Term | Meaning |
|---|---|
| **`Expr`** | the kernel's term type. Eleven variants, and a user cannot add one. |
| **Pi type** | a function type whose result may mention the argument, written `(x : A) → B`. The same term former as `∀`. |
| **de Bruijn index** | a bound variable written as a number: how many binders sit between the use and its own binder. Chapter 0, section 0.5. |
| **loose bound variable** | a bound variable that points outside the term it sits in. A closed term has none. |
| **free variable, `FVar`** | a variable from the local context, with an identifier that never changes number. What a binder is opened into. |
| **metavariable, `MVar`** | a hole for unification to fill. A finished proof holds none. |
| **`lift`** | add to every loose index, because a term moved under a new binder. |
| **`instantiate`** | replace index 0 with a term. One beta step is one call. |
| **`abstract`** | the reverse: turn a free variable back into a bound one, closing a binder. |
| **alpha equivalence** | equal up to the names of bound variables. With de Bruijn indices it is almost free. |

## Judgments and rules

| Term | Meaning |
|---|---|
| **`Γ ⊢ e : A`** | "in the context `Γ`, the term `e` has the type `A`". |
| **local context, `Γ`** | the list of what is already known. In logic, the hypotheses. |
| **environment** | the map from a `Name` to a declaration. The global one. |
| **`infer_type`** | works out the type of a term. |
| **`is_def_eq`** | decides whether two terms are the same **by computation**. |
| **conversion rule** | the rule that a term keeps its type under computation. The reason a checker must hold an evaluator. Chapter 0, section 0.8. |

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
| **strict positivity** | the condition that stops `inductive Bad \| mk : (Bad → False) → Bad`. Chapter 4, section 4.5. |
| **nested inductive** | one whose own type sits inside another, as in `List Tree → Tree`. Lean compiles it into an auxiliary type. |
| **mutual group** | types declared together, each recursor taking one motive per type. Chapter 7. |
| **subsingleton** | a type with at most one element. A `Prop` that is one may eliminate into any sort. |
| **large elimination** | eliminating a `Prop` into a bigger universe. Only allowed for a subsingleton. |
| **structure** | an inductive type with one constructor and no index. Its fields determine it. |
| **quotient, `Quot`** | a kernel primitive no inductive declaration can express. |

## Trust

| Term | Meaning |
|---|---|
| **kernel** | the small trusted part that re-checks everything. |
| **De Bruijn criterion** | the rule that every untrusted stage only produces a candidate the kernel re-checks. Chapter 0, section 0.16. |
| **axiom** | a name with a type and no proof. The one thing the kernel does not check. |
| **`sorry`** | becomes the axiom `sorryAx`. A proof that reaches it is not a proof. |
| **`unsafe`, `partial`** | a declaration that may not terminate. A proof must not rest on one. |
| **trust report** | the list of axioms a theorem rests on. Lean spells it `#print axioms`. Chapter 6. |

## The pipeline

| Term | Meaning |
|---|---|
| **lexer** | text to a flat list of tokens. Stage 1. **Works here.** |
| **token table** | the set of keywords and symbols the lexer knows. It **grows** while the file is read. Chapter 8, section 8.3. |
| **parser** | tokens to a `Syntax` tree. Stage 2. **Missing here.** |
| **`Syntax`** | the lossless tree. One type for every construct, with the node kind a `Name`. |
| **trivia** | the whitespace and comments around a token. Lean keeps it. We drop it. |
| **elaborator** | `Syntax` to `Expr`. Macro expansion, name resolution, implicit arguments, tactics. Stage 3. **Missing here.** |
| **tactic** | a program that builds a proof term. Untrusted. |
| **`lean4export`** | the tool that writes Lean's elaborated declarations to a file, so another checker can read them. Chapter 3. |
| **level 1, 2, 3** | the three checkpoints of `ROADMAP.md`. Level 1 is "our kernel checks Lean's terms". |

## What a check costs

Chapters 9 to 12 are about cost, and these are the terms they add.

| Term | Meaning |
|---|---|
| **budget** | a count of **work** that each declaration may use, `REAN_FUEL`. The kernel has no such limit; ours exists so that a corrupt file cannot hang us. Chapter 9, section 9.7. |
| **unit of work** | what the budget counts. A reduction step is charged the **size of the term it produced**, because an ι step can make a term larger, so counting steps bounds nothing. |
| **out of budget** | the verdict when a declaration wants more work than the budget holds. It is **not** a claim that the declaration is wrong. |
| **blocked** | the verdict when a declaration waits on another that did not check. Also not wrong, only unread. One root failure of the prelude blocked 15,272 of them. Chapter 12, section 12.8. |
| **`loose`** | the first number every node caches: one more than the largest loose bound variable index inside, or zero. `loose == 0` means closed. It turns substitution from a walk into a test. Chapter 9, section 9.6. |
| **`size`** | the second cached number, the node count. The budget asks for it after every step, so a walk would cost as much as the work it charges for. |
| **`hash`** | the third cached number, and the key of every cache. It must ignore whatever `alpha_eq` ignores: binder names, and the **shape** of a universe level. Chapter 10, section 10.2. |
| **confirm** | what a cache must do with a hit before it trusts it. Two terms can share a hash, so `alpha_eq` makes the decision. A proof checker may not be probably right. Chapter 10, section 10.3. |
| **spine** | a head and the arguments applied to it. `f x y` is the spine `(f, [x, y])`. |
| **congruence** | the rule that lets a spine be compared without reduction: same head and equal arguments means equal terms. Asking this **before** unfolding was the largest single win of the project. Chapter 11. |
| **eager** | our `whnf`: each step builds a whole new term and drops the old one. Lean's is **lazy** and rebuilds nothing. This is the one job left. Chapter 12, section 12.10. |
| **slice** | a prefix of a `lean4export` file, cut after one declaration. Valid because the format is topologically ordered. `tools/slice.py`. Chapter 11, section 11.1. |
| **root failure** | the failure at the end of a chain of blocked declarations. `tools/roots.py` ranks them by how many leaves each one holds up. |
