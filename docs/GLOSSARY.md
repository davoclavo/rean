# Glossary

Every term the chapters use, in one place. The short definition first, then
where to read more.

New to the project? Read [Part I of the book](book/README.md) first. Eight
short chapters, in order, and every word below is defined there in context.
[The guide](README.md) holds the whole reading order.
[The references](REFERENCES.md) hold every source.

A pointer such as "Part I chapter 4, section 4.4" is the gentle explanation. A
pointer such as "chapter 10, section 10.7" is the code.

Every term below has an anchor, so a chapter can link straight to it. A word in
a chapter that reads like
[definitional equality](GLOSSARY.md#definitional-equality) points here.

---

## If you come from TypeScript or Scala 3

You already use most of these ideas. The names are different, and two of them
are stronger here than in your language.

| You know | Here it is | The difference |
|---|---|---|
| `never` in TypeScript, `Nothing` in Scala | the [empty type](#empty-type), which is how `False` is built | none. A type with no values **is** a false proposition. |
| `Unit` in Scala, `void` in TypeScript | the [unit type](#unit-type), which is how `True` is built | none |
| a generic function, `<A>(a: A) => A` | a [proof](#proof) of `A → A` | a Lean function must be [total](#total), so the type is a real promise |
| the `R` channel of `Effect<A, E, R>`, and a `Layer` that satisfies it | the [environment](#environment) and the [local context](#local-context) | the same bookkeeping, and the kernel checks it on every term |
| the `E` channel of `Effect<A, E, R>` | a type that records a fact about a value | none. You are already writing propositions. |
| `given` and `using` in Scala 3, instance search | what the [elaborator](#elaborator) does before the kernel sees a term | it is **untrusted**. The kernel re-checks the term it builds. |
| `inline` and a macro in Scala 3 | stage 3 again, also untrusted | a Lean macro may add a **token** as well. Chapter 16. |
| a match type in Scala 3, a conditional type in TypeScript | a type that **reduces**, which is [definitional equality](#definitional-equality) | Lean reduces with β δ ι ζ η on any term, and it must end |
| a dependent method, `def key(e: Entry): e.Key` | a [Pi type](#pi-type) | in Lean the result type may hold **any** value, not only a member type |
| type erasure at run time | [erasure](#erasure) of a proof | the reason is [proof irrelevance](#proof-irrelevance), not a compiler choice |
| a literal type, `"GET"` or `23` | an [index](#index) of a type family | Lean computes with it, so `Vector α (2 + 1)` and `Vector α 3` are one type |

Two warnings for a reader with this background.

- **A type here is not a set of values you check at run time.** It is a
  statement, and the term is the reason the statement holds.
- **Equality of types is not structural.** It is
  [definitional equality](#definitional-equality), which runs your program a
  little. Part I chapter 7 is that story.

## The two worlds

| Term | Meaning |
|---|---|
| <a id="proposition"></a>**proposition** | a statement. In Lean it is a **type**. |
| <a id="proof"></a>**proof** | a reason the statement holds. In Lean it is a **term** of that type. |
| <a id="curry-howard"></a>**Curry-Howard** | the name for that correspondence. "Check this proof" becomes "check this type". Part I chapter 1, section 1.3. |
| <a id="data"></a>**data** | a value you compute with, such as `3`. It lives in `Type`. |
| <a id="inhabited"></a>**inhabited** | a type that has at least one element. A proposition is true exactly when its type is inhabited. |
| <a id="empty-type"></a>**empty type** | a type with no element, such as `False`. `never` in TypeScript and `Nothing` in Scala are the same idea. |
| <a id="unit-type"></a>**unit type** | a type with exactly one element, such as `True`. `Unit` in Scala is the same idea. |
| <a id="total"></a>**total** | a function that returns for every input, and never loops. Every Lean function is total, and that is what makes a type a promise. |

## The two theories

| Term | Meaning |
|---|---|
| <a id="coc"></a>**CoC** | the Calculus of Constructions. Functions, dependent function types, and an impredicative `Prop`. Coquand and Huet, 1988. Part I chapter 5. |
| <a id="coic"></a>**CoIC** | the Calculus of Inductive Constructions. CoC plus inductive declarations, which is what Lean's kernel implements. Part I chapter 6. |

## Sorts and universes

| Term | Meaning |
|---|---|
| <a id="sort"></a>**`Sort u`** | the only universe former the kernel has. Part I chapter 4, section 4.2. |
| <a id="prop"></a>**`Prop`** | notation for `Sort 0`. The home of propositions. |
| <a id="type-n"></a>**`Type n`** | notation for `Sort (n+1)`. The home of data. |
| <a id="universe-level"></a>**universe level** | the `u` of `Sort u`. Built from `0`, `succ`, `max`, `imax`, and a parameter. |
| <a id="imax"></a>**`imax u v`** | `0` when `v` is `0`, and `max u v` otherwise. The one special rule, and the reason `Prop` is impredicative. |
| <a id="impredicative"></a>**impredicative** | able to quantify over a collection that holds the thing being defined. `∀ (p : Prop), p → p` is itself a `Prop`. Part I chapter 4, section 4.4. |
| <a id="predicative"></a>**predicative** | not that. A quantifier over `Type u` lands in a larger universe. |
| <a id="cumulativity"></a>**cumulativity** | a rule that `Type 0` is a subtype of `Type 1`. Coq has it. **Lean does not.** |
| <a id="universe-polymorphism"></a>**universe polymorphism** | what Lean uses instead: a declaration takes its levels as parameters, as in `List.{u}`. |

## Terms

| Term | Meaning |
|---|---|
| <a id="expr"></a>**`Expr`** | the kernel's term type. Eleven variants, and a user cannot add one. |
| <a id="pi-type"></a>**Pi type** | a function type whose result may mention the argument, written `(x : A) → B`. The same term former as `∀`. |
| <a id="de-bruijn-index"></a>**de Bruijn index** | a bound variable written as a number: how many binders sit between the use and its own binder. Part I chapter 2, section 2.4. |
| <a id="loose-bound-variable"></a>**loose bound variable** | a bound variable that points outside the term it sits in. A closed term has none. |
| <a id="free-variable"></a>**free variable, `FVar`** | a variable from the local context, with an identifier that never changes number. What a binder is opened into. |
| <a id="metavariable"></a>**metavariable, `MVar`** | a hole for unification to fill. A finished proof holds none. |
| <a id="lift"></a>**`lift`** | add to every loose index, because a term moved under a new binder. |
| <a id="instantiate"></a>**`instantiate`** | replace index 0 with a term. One beta step is one call. |
| <a id="abstract"></a>**`abstract`** | the reverse: turn a free variable back into a bound one, closing a binder. |
| <a id="substitution"></a>**substitution** | `b[x := a]`, which is `b` with every free `x` replaced by `a`. The one operation of the theory. Part I chapter 2, section 2.3. |
| <a id="capture"></a>**capture** | the bug where a substitution puts a term under a binder that owns its name, and the meaning changes. de Bruijn indices make it impossible. |
| <a id="alpha-equivalence"></a>**alpha equivalence** | equal up to the names of bound variables. With de Bruijn indices it is almost free. |
| <a id="closed"></a>**closed** | a term with no loose bound variable. Only a closed term has a type. Part I chapter 2, section 2.6. |
| <a id="stuck"></a>**stuck** | a term that no rule can reduce, such as `0 + n` for a variable `n`. Stuck is a correct answer, not an error. Part I chapter 7, section 7.4. |

## Judgments and rules

| Term | Meaning |
|---|---|
| <a id="judgment"></a>**`Γ ⊢ e : A`** | "in the context `Γ`, the term `e` has the type `A`". |
| <a id="local-context"></a>**local context, `Γ`** | the list of what is already known. In logic, the hypotheses. |
| <a id="environment"></a>**environment** | the map from a `Name` to a declaration. The global one. |
| <a id="infer-type"></a>**`infer_type`** | works out the type of a term. |
| <a id="is-def-eq"></a>**`is_def_eq`** | decides whether two terms are the same **by computation**. |
| <a id="derivation"></a>**derivation** | the tree of rules that justifies one judgment. A checker builds it and throws it away. Part I chapter 5, section 5.5. |
| <a id="conversion-rule"></a>**conversion rule** | the rule that a term keeps its type under computation. The reason a checker must hold an evaluator. Part I chapter 7, section 7.1. |

## Reduction

| Term | Meaning |
|---|---|
| <a id="definitional-equality"></a>**definitional equality, `≡`** | sameness that the kernel decides by computing. Not a proposition. |
| <a id="propositional-equality"></a>**propositional equality, `=`** | the inductive type `Eq`. A statement you prove. `rfl : a = b` checks exactly when `a ≡ b`. |
| <a id="whnf"></a>**whnf** | weak head normal form. Reduce until the outermost shape is stable. "Weak" means not inside a binder. |
| <a id="beta"></a>**β beta** | call a function: `(fun x => b) a ≡ b[x := a]`. |
| <a id="delta"></a>**δ delta** | unfold a definition to its value. |
| <a id="zeta"></a>**ζ zeta** | unfold a `let`. |
| <a id="iota"></a>**ι iota** | run a recursor on a constructor. |
| <a id="eta"></a>**η eta** | `fun x => f x ≡ f`. Also, for a structure, `S.mk p.1 p.2 ≡ p`. |
| <a id="proof-irrelevance"></a>**proof irrelevance** | all proofs of one proposition are definitionally equal. |

## Inductive types

| Term | Meaning |
|---|---|
| <a id="inductive-type"></a>**inductive type** | a type declared by its constructors. You get a recursor for free. |
| <a id="constructor"></a>**constructor** | a way to build an element. |
| <a id="parameter"></a>**parameter** | an argument of the type that is fixed across every constructor. |
| <a id="index"></a>**index** | an argument of the type that varies, such as the `b` of `a = b`. |
| <a id="field"></a>**field** | an argument of a constructor, after the parameters. |
| <a id="recursor"></a>**recursor** | the eliminator. How you **use** an element. |
| <a id="motive"></a>**motive** | the result type of a recursor, as a function of the thing taken apart. |
| <a id="minor-premise"></a>**minor premise** | what the recursor needs for one constructor. One per constructor. |
| <a id="major-premise"></a>**major premise** | the element the recursor takes apart. |
| <a id="induction-hypothesis"></a>**induction hypothesis** | the extra premise a **recursive** field adds. |
| <a id="strict-positivity"></a>**strict positivity** | the condition that stops `inductive Bad \| mk : (Bad → False) → Bad`. Part I chapter 6, section 6.7. |
| <a id="nested-inductive"></a>**nested inductive** | one whose own type sits inside another, as in `List Tree → Tree`. Lean compiles it into an auxiliary type. |
| <a id="mutual-group"></a>**mutual group** | types declared together, each recursor taking one motive per type. Chapter 15. |
| <a id="subsingleton"></a>**subsingleton** | a type with at most one element. A `Prop` that is one may eliminate into any sort. |
| <a id="large-elimination"></a>**large elimination** | eliminating a `Prop` into a bigger universe. Only allowed for a subsingleton. |
| <a id="structure"></a>**structure** | an inductive type with one constructor and no index. Its fields determine it. |
| <a id="quotient"></a>**quotient, `Quot`** | a kernel primitive no inductive declaration can express. |

## Trust

| Term | Meaning |
|---|---|
| <a id="kernel"></a>**kernel** | the small trusted part that re-checks everything. |
| <a id="de-bruijn-criterion"></a>**De Bruijn criterion** | the rule that every untrusted stage only produces a candidate the kernel re-checks. Part I chapter 8, section 8.1. |
| <a id="axiom"></a>**axiom** | a name with a type and no proof. The one thing the kernel does not check. |
| <a id="sorry"></a>**`sorry`** | becomes the axiom `sorryAx`. A proof that reaches it is not a proof. |
| <a id="unsafe"></a>**`unsafe`, `partial`** | a declaration that may not terminate. A proof must not rest on one. |
| <a id="trust-report"></a>**trust report** | the list of axioms a theorem rests on. Lean spells it `#print axioms`. Chapter 14. |

## The pipeline

| Term | Meaning |
|---|---|
| <a id="lexer"></a>**lexer** | text to a flat list of tokens. Stage 1. **Works here.** |
| <a id="token-table"></a>**token table** | the set of keywords and symbols the lexer knows. It **grows** while the file is read. Chapter 16, section 16.3. |
| <a id="parser"></a>**parser** | tokens to a `Syntax` tree. Stage 2. **Missing here.** |
| <a id="syntax"></a>**`Syntax`** | the lossless tree. One type for every construct, with the node kind a `Name`. |
| <a id="trivia"></a>**trivia** | the whitespace and comments around a token. Lean keeps it. We drop it. |
| <a id="elaborator"></a>**elaborator** | `Syntax` to `Expr`. Macro expansion, name resolution, implicit arguments, tactics. Stage 3. **Missing here.** |
| <a id="tactic"></a>**tactic** | a program that builds a proof term. Untrusted. |
| <a id="lean4export"></a>**`lean4export`** | the tool that writes Lean's elaborated declarations to a file, so another checker can read them. Chapter 11. |
| <a id="level-1-2-3"></a>**level 1, 2, 3** | the three checkpoints of `ROADMAP.md`. Level 1 is "our kernel checks Lean's terms". |

## What a check costs

Chapters 17 to 20 are about cost, and these are the terms they add.

| Term | Meaning |
|---|---|
| <a id="budget"></a>**budget** | a count of **work** that each declaration may use, `REAN_FUEL`. Lean's kernel has no work budget. It bounds the term instead, with a recursion depth guard and a maximum numeral size. Ours bounds the work, so that a corrupt file cannot hang us. Chapter 17, sections 17.7 and 17.14. |
| <a id="unit-of-work"></a>**unit of work** | what the budget counts. A reduction step is charged the **size of the term it produced**, because an ι step can make a term larger, so counting steps bounds nothing. |
| <a id="out-of-budget"></a>**out of budget** | the verdict when a declaration wants more work than the budget holds. It is **not** a claim that the declaration is wrong. |
| <a id="blocked"></a>**blocked** | the verdict when a declaration waits on another that did not check. Also not wrong, only unread. One root failure of the prelude blocked 15,272 of them. Chapter 20, section 20.8. |
| <a id="loose"></a>**`loose`** | the first number every node caches: one more than the largest loose bound variable index inside, or zero. `loose == 0` means closed. It turns substitution from a walk into a test. Chapter 17, section 17.6. |
| <a id="size"></a>**`size`** | the second cached number, the node count. The budget asks for it after every step, so a walk would cost as much as the work it charges for. |
| <a id="hash"></a>**`hash`** | the third cached number, and the key of every cache. It must ignore whatever `alpha_eq` ignores: binder names, and the **shape** of a universe level. Chapter 18, section 18.2. |
| <a id="confirm"></a>**confirm** | what a cache must do with a hit before it trusts it. Two terms can share a hash, so `alpha_eq` makes the decision. A proof checker may not be probably right. Chapter 18, section 18.3. |
| <a id="spine"></a>**spine** | a head and the arguments applied to it. `f x y` is the spine `(f, [x, y])`. |
| <a id="congruence"></a>**congruence** | the rule that lets a spine be compared without reduction: same head and equal arguments means equal terms. Asking this **before** unfolding was the largest single win of the project. Chapter 19. |
| <a id="eager"></a>**eager** | our `whnf`: each step builds a whole new term and drops the old one. Lean's is **lazy** and rebuilds nothing. This is the one job left. Chapter 20, section 20.10. |
| <a id="slice"></a>**slice** | a prefix of a `lean4export` file, cut after one declaration. Valid because the format is topologically ordered. `tools/slice.py`. Chapter 19, section 19.1. |
| <a id="root-failure"></a>**root failure** | the failure at the end of a chain of blocked declarations. `tools/roots.py` ranks them by how many leaves each one holds up. |
| <a id="oracle"></a>**oracle** | an answer from outside the project, which a measurement is held to. Lean's own kernel is the one for speed. Chapter 25, section 25.6. |
| <a id="tally"></a>**tally** | the instrument that counts a reduction by rule and by definition, `REAN_TALLY=1`. A profiler says where the time went. A tally says **what** was reduced. Chapter 21. |

## Stage 5, and the words a runtime needs

| Term | Meaning |
|---|---|
| <a id="evaluator"></a>**evaluator** | the part that asks what a term **comes to**, rather than whether it is correct. Stage 5, chapter 27. |
| <a id="thunk"></a>**thunk** | an argument that is not evaluated yet. It is forced at most once, and then it holds its value. Chapter 27, section 27.3. |
| <a id="by-need"></a>**by need** | the order our evaluator uses: compute a thunk when somebody reads it, and never before. Haskell is the language built this way. |
| <a id="strict"></a>**strict** | the other order: compute every argument before the call. Lean, OCaml and Rust are strict. |
| <a id="erasure"></a>**erasure** | dropping what cannot affect the answer. Lean's compiler erases a type and a proof, because it knows the types. Our evaluator has no types, so it ignores them instead. |
| <a id="lcnf"></a>**LCNF** | the intermediate form of Lean's own stage 5, between the kernel term and the generated C. |
| <a id="primitive"></a>**primitive** | an operation the evaluator performs itself, such as the arithmetic on a machine number. Chapter 27, section 27.5. |

## Words from the other kernels

Chapter 22 reads what other people built, and these are the words they use.

| Term | Meaning |
|---|---|
| <a id="normalisation-by-evaluation"></a>**normalisation by evaluation** | reduce a term by building a value in the host language, with a closure for a function, and read a term back at the end. The fastest checker in the arena works this way. Chapter 22, section 22.8. |
| <a id="delayed-instantiation"></a>**delayed instantiation** | keep a term as a pointer plus a shift, so a lift costs nothing and one cache entry serves every shifted copy. Chapter 22, section 22.7. |
| <a id="hash-consing"></a>**hash-consing** | build one object for every equal term, so equality is a pointer comparison. Chapter 26, section 26.9 measures it here, and does not take it. |
| <a id="the-arena"></a>**the arena** | the Lean Kernel Arena. It times every independent checker on the same files, and it holds proofs that each one must **refuse**. <https://arena.lean-lang.org/> |
| <a id="guard-condition"></a>**guard condition** | the rule Rocq uses in place of a recursor, to be sure a recursion ends. Chapter 13, section 13.10. |
| <a id="singleton-elimination"></a>**singleton elimination** | Rocq's name for what chapter 13, section 13.3 calls large elimination out of `Prop`. |
| <a id="lcf-kernel"></a>**LCF kernel** | the design Isabelle uses: a theorem is a value that only an inference rule can build. There is no proof term to re-check. |

## Where each word comes from

- The Greek letters, and the rules: Carneiro, *The Type Theory of Lean*.
  <https://github.com/digama0/lean-type-theory>
- The pipeline, and the extensible frontend: de Moura and Ullrich, 2021, and
  Ullrich and de Moura, 2020. <https://lean-lang.org/papers/lean4.pdf>
- What a user may rely on: *The Lean Language Reference*.
  <https://lean-lang.org/doc/reference/latest/>
- Everything else: [the references](REFERENCES.md).
