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

## Three commands for your own Lean code

Point `rean` at a `.lean` file. It calls the real Lean to elaborate the file,
calls `lean4export` to write the terms, and then **our kernel checks every one
of them**.

```sh
cargo run --release -p rean -- check Demo.lean --decl twice_two
cargo run --release -p rean -- show  Demo.lean twice      # what the kernel sees
cargo run --release -p rean -- check prelude        # Lean's `Init`, all of it
cargo run --release -p rean -- check Some.Module    # a module on REAN_LEAN_PATH
cargo run --release -p rean -- export Demo.lean     # write the file, check nothing
```

`show` is the one to try first, and it answers in half a second:

```text
def twice

type
  Nat → Nat

value
  fun (n : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n

rests on 4 constant(s)
trust: no axiom
```

Nobody wrote `HAdd.hAdd` or `instAddNat`. Lean's elaborator put them there, and
this is how to see what it did. Ask it about the library too:
`rean show prelude Nat.sub` shows that subtraction is a **course of values
recursion** over a step function that the equation compiler generated.

```text
export: Demo -> /tmp/rean-export/Demo.ndjson (41 KB) in 0.3s, by Lean 4.35.0-rc3
  ok    inductive  Nat
  ...
  ok    theorem    twice_two

level 1: checked 39 of 39 declarations
trust: no accepted declaration rests on an axiom
```

Read that output carefully, because it says something about trust. `twice_two`
is three lines of Lean, and checking it took **39 declarations**: `Nat`, its
recursor, `HAdd`, `OfNat`, and the instances between them. A checker that
trusted the library and looked only at the theorem would be checking nothing.
`--decl` keeps the export to one declaration and what it rests on. Without it,
the export is the whole closure of the module, which for anything that imports
the prelude is 345 MB and a few minutes.

Four things are worth knowing before the first run.

1. **The elaborator is Lean's, not ours.** Stages 2 and 3 of the pipeline below
   still do not exist here. This is checkpoint level 1 of
   [the roadmap](docs/ROADMAP.md): our kernel, Lean's terms. Level 2 is the one
   that needs our own parser.
2. **It needs the real Lean and `lean4export`, from one toolchain.** `rean`
   looks on `PATH` and in `~/.elan/toolchains`. `REAN_LEAN` and
   `REAN_LEANEXPORT` name them by hand, and
   [`fixtures/lean4export/PROVENANCE.md`](fixtures/lean4export/PROVENANCE.md)
   says how to build the exporter.
3. **An `.ndjson` file needs none of that.** `rean check file.ndjson` reads what
   anybody exported, on any machine.
4. **Lean's errors stay Lean's.** A file that does not compile gets Lean's own
   message, and our checker never sees it.

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
| to see what a checker **costs**, measured | chapters [9](docs/09-structures-and-cost.md) to [17](docs/17-twelve-seconds.md) |
| to see **what Lean hands the kernel** | `rean show prelude Nat.sub`, and [chapter 17](docs/17-twelve-seconds.md) |
| to see how to **find** a performance fault | chapters [11](docs/11-compare-before-you-unfold.md) to [13](docs/13-a-hundred-million.md) |
| to **check your own Lean file** | [chapter 16](docs/16-the-front-door.md) |
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
| [12 — Ask the cheapest question first](docs/12-ask-the-cheapest-question.md) | proof irrelevance belongs before reduction, not after. Why the rule alone made things worse, why a pair of changes is one unit of measurement, and how to rank 107 failures so you work on the one worth 15,272. |
| [13 — A hundred million](docs/13-a-hundred-million.md) | the checker counted down from 100,000,000 one `Nat.succ` at a time. When a profiler stops helping, count things in the language of the **problem**: which recursor, which number, which definition. Then the **report** became the slow part. |
| [14 — What the others do](docs/14-what-the-others-do.md) | independent Lean kernels exist and some are 20× faster than Lean's own. Reading their write-ups found a rule we had wrong and the O(n²) in our β step. |
| [15 — The last two hundred and forty-eight](docs/15-the-last-two-hundred.md) | eleven hypotheses, eleven measurements. Eight changed nothing, one ruled out a rewrite, one test failed because the kernel got **more correct**, and a profile found a **crash** that hours of measurement had read as a slow run. |
| [16 — The front door](docs/16-the-front-door.md) | `rean check Demo.lean`. Three lines of Lean cost **39 declarations**, the one substitution that chapter 9's rule had missed, a limit that counted the wrong thing, and the instrument that is kept because a profiler cannot name a definition. |
| [17 — Twelve seconds](docs/17-twelve-seconds.md) | `rean show`, and the two bugs it found in an hour. Three knobs that reach nothing. And the number that reframes the project: **Lean's own kernel re-checks the whole prelude in 12 seconds**, so measure against something that is not yourself. |
| [Glossary](docs/GLOSSARY.md) | every term the chapters use, including what a check **costs** |

Every claim in a chapter has a test:

```sh
devbox run -- cargo test -p rean_kernel --test universes   # chapter 0
devbox run -- cargo test -p rean_kernel --test typeck      # chapters 1 and 2
devbox run -- cargo test -p rean_export                    # chapters 3 and 4
devbox run -- cargo test -p rean_kernel --test structures  # chapter 9
devbox run -- cargo test -p rean_kernel --test cache       # chapter 10
devbox run -- cargo test -p rean_kernel --test comparison  # chapters 11 and 12
devbox run -- cargo test -p rean_kernel --test substitution # chapter 14
devbox run -- cargo test -p rean_kernel --test limits       # chapter 16
devbox run -- cargo test -p rean --test frontdoor           # chapter 16
devbox run -- cargo test -p rean --test show                # chapter 17
```

## Three tools, and the method they serve

Both of the largest wins in this project came from one move: **take one failing
declaration out of hundreds, and let the measurement choose the fix.** Three
plans were retired that way before a line of them was written.

```sh
# Which failure is worth the trouble? One of them blocked 15,272 declarations.
./target/release/rean check full.ndjson > report.txt
python3 tools/roots.py report.txt

# Cut that one declaration and its dependencies out of the export.
python3 tools/slice.py full.ndjson one.ndjson _private.Init.Prelude.0.isValidChar_UInt32

# Then sweep. Passes at a bigger budget in a second? The budget was the fault.
# The three knobs are coupled: a bigger budget builds a deeper term, a deeper
# term needs a deeper recursion limit, and that needs a bigger stack.
REAN_FUEL=2000000000 REAN_DEPTH=60000 REAN_STACK=8192 \
  ./target/release/rean check one.ndjson

# And ask the kernel what it did. One failing declaration, counted by rule.
REAN_TALLY=1 ./target/release/rean check one.ndjson
```

```text
  FAIL  theorem    ..ByteArray.utf8DecodeChar?.assemble₄._proof_3
          the kernel reached 6000 levels of recursion, so it was not checked
          deepest recursion: 6000
               3276469  units of work charged
                 73582  beta
                 12065  iota Nat.rec
                 12024  delta Nat.casesOn
                  5980  declined read_nat: nested too deep
                  5980  delta Nat.sub._f
```

Chapters [11](docs/11-compare-before-you-unfold.md) and
[12](docs/12-ask-the-cheapest-question.md) are that method, worked twice.
Chapter [16](docs/16-the-front-door.md) is the third, and the tally above is
what made it quick: `delta Nat.sub._f` names a cause, and "`whnf` is 41%" does
not. A profiler cannot say **which** definition, and after chapter 13 that is
the only question left.

A third tool keeps the chapters honest. Every chapter cites its tests by name,
and `tools/cite.py` fails the gate when a chapter names a test that the code
does not define. It found six stale citations in chapter 1 the day it was
written, and chapter 1 says so.

```sh
devbox run cite
```

## The scoreboard

Every row is Lean **4.35.0-rc3**, exported by `rean export`. All three of the
libraries that the toolchain ships now run to completion, with no crash:

| Library | Declarations | Checked | Failed | Time |
|---|---|---|---|---|
| `Init`, the prelude | 59,349 | **55,835** | 72 | 231 s |
| `Std` | 99,619 | **95,237** | 120 | 330 s |
| `Lean`, the compiler | 171,817 | **150,420** | 127 | 367 s |

```sh
cargo run --release -p rean -- check prelude
cargo run --release -p rean -- check Std
cargo run --release -p rean -- check Lean
```

| Checkpoint | Score | Meaning |
|---|---|---|
| level 1 | **95 of 95** | the two committed fixtures |
| level 1, the prelude | **55,835 of 59,349** | the default budget, in 231 seconds |
| level 1, patient | **59,199 of 59,349** | **99.75%**, with `REAN_FUEL=2000000000 REAN_STACK=8192`, in 36 minutes |
| level 1, what is left | one family of limits, and **5 real rejections** | the limits are `Int32`, `Int64` and `ISize`. The five are `_sizeOf_N_eq` lemmas of **nested** inductive types in `Lean`, where our kernel says no and Lean says yes. [Chapter 17](docs/17-twelve-seconds.md) names them. |
| level 2 | 0 of 32 | our pipeline inhabits Lean's types. Needs a parser. |
| level 3 | 0 of 32 | our term matches Lean's term |
| tests | **479** | `devbox run test` |
| citations | every chapter's test names resolve | `devbox run cite` |
| coverage | **93.1% of regions, 95.1% of lines** | `devbox run coverage` |
| red team | **39 lies refused** | `cargo test -p rean_kernel --test soundness` |
| trust | every axiom reported, by name | the `trust:` line of `rean check` |
| crashes | **none**, at any setting | the kernel reports `OutOfStack` instead. [Chapter 16](docs/16-the-front-door.md) |
| the oracle for speed | **12 s** | `leanchecker Init`, Lean's own kernel, all of it. We take 199 s. [Chapter 17](docs/17-twelve-seconds.md) |

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

`Expr` has eleven variants and a user cannot add one. It is the input of the
type checker.

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

Every subterm is a `Sub`, which is an `Arc<Expr>` and **three cached numbers**.
Each one is computed from the children in constant time, so building a term pays
O(1) per node, and the real Lean kernel caches the same three.

| Number | What it saves |
|---|---|
| `loose` | one more than the largest loose index, or zero. Substitution asks it and skips a closed subterm instead of walking it. |
| `size` | the node count. The work budget asks for it after **every** reduction step, so a walk would cost as much as the work it charges for. |
| `hash` | the key of every cache. It must ignore what `alpha_eq` ignores, and a cache hit is **confirmed** with `alpha_eq` before it is trusted. |

Chapters [9](docs/09-structures-and-cost.md) and [10](docs/10-the-cache.md) are
those three numbers and what each one bought. One of them bought nothing, and
the chapter says which.

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
