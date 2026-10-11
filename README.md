# rean

A Lean compiler in Rust. This repository holds the foundations of the frontend.

## Start

```sh
devbox shell          # enter the toolchain
devbox run build      # cargo build --workspace
devbox run test       # cargo test --workspace
devbox run check      # fmt, clippy, and test
devbox run coverage   # line and region coverage
```

Two commands show the code at work:

```sh
cargo run -p rean -- lex examples/twice.lean    # print every token
cargo run -p rean -- demo                       # walk the four stages
cargo run -p rean -- prove                      # check a proof with the kernel
cargo run -p rean -- check fixtures/lean4export/Nat.add_succ.ndjson
```

## Examples

| File | Shows |
|---|---|
| `examples/twice.lean` | a small, ordinary Lean file |
| `examples/tokens.lean` | every token kind that the lexer knows |
| `examples/universes.lean` | `Sort`, `Prop`, and `Type`, next to chapter 0 |
| `examples/notation.lean` | three symbols that the table does not hold yet |

`notation.lean` reports three errors on purpose. It records the gap that the
parser must close. `crates/rean_lexer/tests/examples.rs` locks each count in
place, and it also shows that one `TokenTable::insert` per symbol clears them.

## How Lean compiles a file

Lean does not use the pipeline of a C compiler. The order below is the one that
matters, and it explains why the crates split the way they do.

1. **Lex.** Text becomes tokens. The set of tokens is not fixed. A `notation`
   command adds a token while the compiler reads the file.
2. **Parse.** Tokens become a `Syntax` tree. The parser is a Pratt parser, and
   it reads its grammar from a table that user commands extend.
3. **Elaborate.** The `Syntax` tree becomes an `Expr`. This stage expands
   macros, resolves names, infers implicit arguments, and runs tactics. It is
   the largest stage and it holds every rule about meaning.
4. **Check.** The kernel checks the `Expr`. The kernel is small, and it is the
   only part that you must trust.
5. **Compile.** The kernel term becomes LCNF, then C code or an interpreter
   call. This repository does not reach stage 5 yet.

Stage 3 is where Lean differs most from other languages. In Rust the compiler
owns the grammar and the type rules. In Lean a file can extend both. The
compiler therefore reads the grammar and the elaboration rules out of an
environment that grows as it works.

## The crates

| Crate | Job |
|---|---|
| `rean_core` | `Name`, `Span`, `SourceMap`, `Diagnostic`. Every crate uses these. |
| `rean_lexer` | `TokenTable`, `Lexer`, `Token`. Stage 1. |
| `rean_syntax` | `Syntax`, the lossless tree. The result of stage 2. |
| `rean_kernel` | `Expr`, `Level`, the variable operations, the `Environment`, and the checker. Stage 4. |
| `rean_export` | reads a `lean4export` NDJSON file into an `Environment`. |
| `rean` | The driver. Each command returns a value, and the binary prints it. |

No library crate reads a file or prints a line. Only `rean` does. A test can
therefore call any stage directly.

## The plan

See [the roadmap](docs/ROADMAP.md). In short: build the whole pipeline here, and
use `lean4export` output from the real Lean as a ground truth that our answers
must meet.

## Learning path

New to this? Read in this order. Each chapter is self-contained and ends with
exercises and answers.

| If you want | Start at |
|---|---|
| to understand what a proof checker **is** | [chapter 0](docs/00-introduction-to-the-kernel.md) |
| to see a checker **built**, step by step | chapters [1](docs/01-the-type-checker.md) and [2](docs/02-the-environment.md) |
| to see it meet **real Lean** | [chapter 3](docs/03-the-ground-truth.md) |
| to see what **breaks** and how it is found | chapters [4](docs/04-making-it-work.md) to [7](docs/07-mutual-and-nested.md) |
| to see what a checker **costs**, measured | chapters [9](docs/09-structures-and-cost.md) to [12](docs/12-ask-the-cheapest-question.md) |
| to see how to **find** a performance fault | chapters [11](docs/11-compare-before-you-unfold.md) and [12](docs/12-ask-the-cheapest-question.md) |
| to see where a compiler **begins** | [chapter 8](docs/08-the-frontend.md), independent of the rest |
| a word you do not know | [the glossary](docs/GLOSSARY.md) |

## Chapters

| Chapter | Topic |
|---|---|
| [0 — Introduction to the kernel](docs/00-introduction-to-the-kernel.md) | What a proof checker is. `Sort`, `Prop`, `Type`, de Bruijn indices, definitional equality, and the ultimate primitives. |
| [1 — The type checker](docs/01-the-type-checker.md) | `alpha_eq`, `LocalContext`, `whnf`, `is_def_eq`, and `infer_type`. The first real proof. |
| [2 — The environment](docs/02-the-environment.md) | declarations, δ, ι, η, proof irrelevance, projections, level normalization. |
| [3 — The ground truth](docs/03-the-ground-truth.md) | reading a real `lean4export` file and checking it. |
| [4 — Making it work](docs/04-making-it-work.md) | `Nat` literals, K-like ι, the quotient rules, strict positivity, and coverage. |
| [5 — What a checker must check](docs/05-what-a-checker-must-check.md) | red team. It accepted a proof of `False`. Recursor checking, large elimination, universe hygiene. |
| [6 — What a theorem rests on](docs/06-what-a-theorem-rests-on.md) | derived minor premises, the axiom trust report, unsafe isolation. |
| [7 — Mutual and nested](docs/07-mutual-and-nested.md) | mutual groups, nested positivity, the inductive universe constraint. |
| [8 — The frontend](docs/08-the-frontend.md) | `Name`, spans, diagnostics, the **extensible token table**, and the lossless tree. Independent of the kernel. |
| [9 — Structures, and what the kernel costs](docs/09-structures-and-cost.md) | the three rules a structure needs, the two numbers every node caches, and why a faster kernel checked no more declarations. |
| [10 — The cache](docs/10-the-cache.md) | the third number, a cache on `whnf` and on `is_def_eq`, and the rule that keeps a cache honest: a hash **finds** an answer, equality **decides** whether to trust it. |
| [11 — Compare before you unfold](docs/11-compare-before-you-unfold.md) | one moved line, 3,951 declarations. How to take one failing case out of 676 and let the measurement overrule your plan. |
| [12 — Ask the cheapest question first](docs/12-ask-the-cheapest-question.md) | proof irrelevance belongs before reduction, not after. Why the rule alone made things worse, and why a pair of changes is one unit of measurement. |
| [Glossary](docs/GLOSSARY.md) | every term the chapters use |

Every claim in a chapter has a test:

```sh
devbox run -- cargo test -p rean_kernel --test universes   # chapter 0
devbox run -- cargo test -p rean_kernel --test typeck      # chapters 1 and 2
devbox run -- cargo test -p rean_export                    # chapters 3 and 4
devbox run -- cargo test -p rean_kernel --test structures  # chapter 9
devbox run -- cargo test -p rean_kernel --test cache       # chapter 10
devbox run -- cargo test -p rean_kernel --test comparison  # chapters 11 and 12
```

## The scoreboard

| Checkpoint | Score | Meaning |
|---|---|---|
| level 1 | **95 of 95** | the two committed fixtures |
| level 1, stress | **39,244 of 57,512** | the whole Lean prelude, in 192 seconds |
| level 2 | 0 of 32 | our pipeline inhabits Lean's types. Needs a parser. |
| level 3 | 0 of 32 | our term matches Lean's term |
| tests | **418** | `devbox run test` |
| coverage | **94.7% of regions, 96.5% of lines** | `devbox run coverage` |
| red team | **39 lies refused** | `cargo test -p rean_kernel --test soundness` |
| trust | every axiom reported, by name | the `trust:` line of `rean check` |

```sh
cargo run -p rean -- check fixtures/lean4export/Nat.add_succ.ndjson
cargo run -p rean -- check fixtures/lean4export/shapes.ndjson
```

| Fixture | Covers |
|---|---|
| `Nat.add_succ.ndjson` | one real module: an inductive type, a recursor with its ι rules, a projection, universe polymorphism, type class instances |
| `shapes.ndjson` | a **mutual** inductive group, a **nested** one, all four `Quot` constants, a structure, a `let`, and `2 + 3 = 5` |

See [the roadmap](docs/ROADMAP.md) and
[`fixtures/lean4export/PROVENANCE.md`](fixtures/lean4export/PROVENANCE.md).

## The building blocks

### 1. `Name`: a hierarchical identifier

See `crates/rean_core/src/name.rs`.

`Nat.succ` is not a string. It is a list of parts that grows at the front.

```rust
Name::from_dotted("Nat.succ")   // Str(Str(Anonymous, "Nat"), "succ")
```

Three reasons explain the design:

- A `namespace` command only adds a prefix. A list makes that cheap.
- The elaborator invents fresh names, such as `_uniq.17`. A numeric part needs
  no string.
- A `Syntax` node kind is also a `Name`. One type serves both jobs.

### 2. `Span`: a byte range

See `crates/rean_core/src/source.rs`.

A position is one `u32` byte offset. A `Span` is therefore 8 bytes, and every
syntax node can hold one. The compiler computes a line and a column only when it
prints a message. `SourceFile` keeps a table of line starts for that job.

### 3. `Diagnostic`: many errors in one run

See `crates/rean_core/src/diag.rs`.

A stage never stops at the first error. It puts a `Diagnostic` into a
`DiagnosticBag`, repairs the hole, and continues. This rule is the reason that
the syntax tree needs a `Missing` node.

### 4. `TokenTable`: the lexer has no keyword list

See `crates/rean_lexer/src/table.rs`.

This block is the first real surprise of a Lean frontend. A C lexer holds its
keywords in a `match`. A Lean lexer cannot, because this line adds a token:

```lean
infixl:65 " ⊹ " => HAdd.hAdd
```

Before that line, `⊹` is an unknown character. After it, `⊹` is a token. The
lexer therefore asks a table on every token, and the table can grow. The table
answers one question: what is the longest token in the table that starts this
text? The longest match matters. Without it, `:=` would lex as `:` and then `=`.

```rust
let mut table = TokenTable::builtin();
table.insert("⊹");        // what a notation command does
```

### 5. `Syntax`: one lossless tree for every construct

See `crates/rean_syntax/src/lib.rs`.

Most compilers give each construct its own struct. Lean has one tree type with
four cases, and the node kind is a `Name` such as `Rean.Parser.Term.app`.

The macro system forces this design. A `syntax` command declares a new node kind
at run time. A fixed set of Rust enum variants could not hold it. A `Name` can.

The tree keeps every keyword and every bracket, so the tree is lossless. A
pretty printer and a language server both need that.

The price is that a later stage cannot trust the shape of a node. The elaborator
must check the shape itself.

### 6. `Expr`: the kernel term

See `crates/rean_kernel/src/expr.rs`.

`Expr` has ten variants and a user cannot add one. It is the input of the type
checker.

A bound variable has no name. It has a de Bruijn index, which is the count of
binders between the use and the binder that owns it.

```text
fun x => fun y => x        becomes   Lam (Lam (BVar 1))
fun x => fun y => y        becomes   Lam (Lam (BVar 0))
```

Two terms that differ only in binder names become the same `Expr`. A type
checker compares types on every step, so this property removes a whole class of
bugs.

The cost is that substitution must renumber. Three operations do that work:

- `lift` adds to every loose index. A term that moves under a new binder needs
  it.
- `instantiate` replaces index 0 with a term. A beta step is one `instantiate`.
- `abstract_fvar` is the reverse. The elaborator opens a binder, works with a
  free variable that never changes number, and then closes the binder again.

### 7. `Level`: universes

See `crates/rean_kernel/src/level.rs`.

`Type` cannot hold itself, so `Sort` takes a level. A level is not only a
number, because a polymorphic definition needs a level variable. `IMax` exists
for `Prop`: a function into `Prop` is a proposition, whatever the level of its
argument is.

## What is not here yet

The order below is the order to build.

1. **Trivia on a token.** Lean keeps the whitespace before and after each atom
   in the `Syntax` tree. A `do` block needs the column, and a pretty printer
   needs the text. The lexer now drops whitespace.
2. **A Pratt parser.** It reads a precedence table, so a `notation` command can
   extend the grammar. It writes `Syntax` and `Missing`.
3. **An `Environment`.** A map from `Name` to a declaration, plus the token
   table and the grammar table. Every stage reads it, and a command extends it.
4. **A local context and metavariables.** The elaborator needs `FVarId` to point
   at a binder and `MVarId` to hold a hole.
5. **The elaborator.** `Syntax` becomes `Expr`. Macro expansion, name
   resolution, unification, and implicit arguments live here.
6. **`whnf` and `isDefEq`.** Weak head normal form and definitional equality.
   They need delta, zeta, iota, and eta, not only the beta step that exists now.
7. **`inferType` and the kernel checker.** The part that you must trust.
8. **Inductive types.** The recursor, the iota rule, and the positivity test.
9. **LCNF and a backend.** Stage 5.

## References

- *The Lean 4 Theorem Prover and Programming Language*, de Moura and Ullrich.
- *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages*,
  Ullrich and de Moura.
- The Lean 4 source. `src/Lean/Parser`, `src/Lean/Elab`, and
  `src/kernel` match stages 2, 3, and 4.
