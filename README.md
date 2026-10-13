# rean

A Lean compiler in Rust. This repository holds the foundations of the frontend.

**New here? Start at [Part I of the book](docs/book/README.md).** Eight short
chapters build the theory that Lean 4 rests on, in order, and they assume
nothing. A reader who writes TypeScript or Scala 3 will find a section in every
one of them that maps the idea onto `never`, `Nothing`, a match type, a GADT, or
the `R` channel of `Effect<A, E, R>`. [The guide](docs/README.md) holds the whole reading order,
[the glossary](docs/GLOSSARY.md) holds every word, and
[the references](docs/REFERENCES.md) hold every source.

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
cargo run --release -p rean -- run   Demo.lean main      # check it, then run it
cargo run --release -p rean -- check prelude        # Lean's `Init`, all of it
cargo run --release -p rean -- check Some.Module    # a module on REAN_LEAN_PATH
cargo run --release -p rean -- export Demo.lean     # write the file, check nothing
```

And `run` is the one that does something:

```text
$ rean run Prog.lean main
level 1: checked 1750 of 1750 declarations
hello from rean
fib 25 = 75025
  square of 0 is 0
  square of 1 is 1

main ran
6149 steps, 133 levels deep
```

**Our kernel checked every declaration it rests on, and then our evaluator ran
it**, and Lean's own `#eval main` prints the same lines. The check is not
optional: only declarations that pass go into the environment the evaluator
uses. `--no-check` skips it and says so.

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
   call. **Stage 5 is here**, as the interpreter: `rean run Prog.lean main`
   checks a program with our kernel and then runs it with our evaluator, and
   the output matches Lean's own. See [chapter 27](docs/27-a-program-that-runs.md).

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
| `rean_eval` | the evaluator: what a term **computes to**. Stage 5. |
| `rean_export` | reads a `lean4export` NDJSON file into an `Environment`. |
| `rean` | The driver. Each command returns a value, and the binary prints it. |

No library crate reads a file or prints a line. Only `rean` does. A test can
therefore call any stage directly.

## The plan

See [the roadmap](docs/ROADMAP.md). In short: build the whole pipeline here, and
use `lean4export` output from the real Lean as a ground truth that our answers
must meet.

## The book

The documentation is a book, and it is meant to be read in order. Part I is the
theory. Parts II to VIII build the checker, measure it, and then score it
against a suite that other people wrote.

| Part | Chapters | It answers |
|---|---|---|
| **I — The ideas** | [1 to 8](docs/book/README.md) | what a proof is, and what the Calculus of Inductive Constructions is |
| **II — The kernel, built** | [the type checker](docs/09-the-type-checker.md), [the environment](docs/10-the-environment.md) | the five functions a checker is made of |
| **III — Meeting real Lean** | [the ground truth](docs/11-the-ground-truth.md), [making it work](docs/12-making-it-work.md) | reading a file the real Lean wrote |
| **IV — Trustworthy** | chapters [13](docs/13-what-a-checker-must-check.md) to [15](docs/15-mutual-and-nested.md) | what a checker must refuse |
| **V — The frontend** | [the frontend](docs/16-the-frontend.md) | stage 1, and the table that grows |
| **VI — What it costs** | chapters [17](docs/17-structures-and-cost.md) to [26](docs/26-thirty-four-per-cent.md) | the lab notebook. Read it for the method. |
| **VII — A program runs** | [a program that runs](docs/27-a-program-that-runs.md) | stage 5, with our own evaluator |
| **VIII — The outside suite** | [the arena](docs/28-the-arena.md) | what a suite written by other people found that our own tests did not |

| If you want | Go to |
|---|---|
| to start from nothing | [Part I chapter 1](docs/book/01-a-proof-is-a-program.md) |
| the whole order, with the gates | [the guide](docs/README.md) |
| every rule in one dense file | [the appendix](docs/00-introduction-to-the-kernel.md) |
| to **check your own Lean file** | [the front door](docs/24-the-front-door.md) |
| to see **what Lean hands the kernel** | `rean show prelude Nat.sub`, and [twelve seconds](docs/25-twelve-seconds.md) |
| a word you do not know | [the glossary](docs/GLOSSARY.md) |
| the source for a claim | [the references](docs/REFERENCES.md) |

## Every chapter

**Part I, the ideas.** Read these first, in this order.

| Chapter | Topic |
|---|---|
| [1 — A proof is a program](docs/book/01-a-proof-is-a-program.md) | propositions as types, and why a type checker is a proof checker |
| [2 — Terms, binders, and names you do not need](docs/book/02-terms-and-binders.md) | the language, substitution, capture, de Bruijn indices |
| [3 — Types that depend on values](docs/book/03-types-that-depend-on-values.md) | the Pi type, and what no mainstream language has |
| [4 — Prop, Type, and Sort](docs/book/04-prop-type-and-sort.md) | the universe tower, `imax`, proof irrelevance, erasure |
| [5 — The Calculus of Constructions](docs/book/05-the-calculus-of-constructions.md) | the five rules, a derivation, and the limit that forces CoIC |
| [6 — Inductive types, and the I in CoIC](docs/book/06-inductive-types.md) | constructors, recursors, ι, positivity, structures, quotients |
| [7 — Definitional equality](docs/book/07-definitional-equality.md) | the seven rules, `whnf`, and why `rfl` sometimes refuses |
| [8 — What you must trust](docs/book/08-what-you-must-trust.md) | the five stages, the seven axioms, and the second opinion |

**Parts II to VIII, the implementation.**

| Chapter | Topic |
|---|---|
| [0 — The foundations, in one file](docs/00-introduction-to-the-kernel.md) | the appendix. All of Part I, dense, in one file. |
| [9 — The type checker](docs/09-the-type-checker.md) | `alpha_eq`, `LocalContext`, `whnf`, `is_def_eq`, and `infer_type`. The first real proof. |
| [10 — The environment](docs/10-the-environment.md) | declarations, δ, ι, η, proof irrelevance, projections, level normalization. |
| [11 — The ground truth](docs/11-the-ground-truth.md) | reading a real `lean4export` file and checking it. |
| [12 — Making it work](docs/12-making-it-work.md) | `Nat` literals, K-like ι, the quotient rules, strict positivity, and coverage. |
| [13 — What a checker must check](docs/13-what-a-checker-must-check.md) | red team. It accepted a proof of `False`. Recursor checking, large elimination, universe hygiene. |
| [14 — What a theorem rests on](docs/14-what-a-theorem-rests-on.md) | derived minor premises, the axiom trust report, unsafe isolation. |
| [15 — Mutual and nested](docs/15-mutual-and-nested.md) | mutual groups, nested positivity, the inductive universe constraint. |
| [16 — The frontend](docs/16-the-frontend.md) | `Name`, spans, diagnostics, the **extensible token table**, and the lossless tree. Independent of the kernel. |
| [17 — Structures, and what the kernel costs](docs/17-structures-and-cost.md) | the three rules a structure needs, the two numbers every node caches, and why a faster kernel checked no more declarations. |
| [18 — The cache](docs/18-the-cache.md) | the third number, a cache on `whnf` and on `is_def_eq`, and the rule that keeps a cache honest: a hash **finds** an answer, equality **decides** whether to trust it. |
| [19 — Compare before you unfold](docs/19-compare-before-you-unfold.md) | one moved line, 3,951 declarations. How to take one failing case out of 676 and let the measurement overrule your plan. |
| [20 — Ask the cheapest question first](docs/20-ask-the-cheapest-question.md) | proof irrelevance belongs before reduction, not after. Why the rule alone made things worse, why a pair of changes is one unit of measurement, and how to rank 107 failures so you work on the one worth 15,272. |
| [21 — A hundred million](docs/21-a-hundred-million.md) | the checker counted down from 100,000,000 one `Nat.succ` at a time. When a profiler stops helping, count things in the language of the **problem**: which recursor, which number, which definition. Then the **report** became the slow part. |
| [22 — What the others do](docs/22-what-the-others-do.md) | independent Lean kernels exist and some are 20× faster than Lean's own. Reading their write-ups found a rule we had wrong and the O(n²) in our β step. |
| [23 — The last two hundred and forty-eight](docs/23-the-last-two-hundred.md) | eleven hypotheses, eleven measurements. Eight changed nothing, one ruled out a rewrite, one test failed because the kernel got **more correct**, and a profile found a **crash** that hours of measurement had read as a slow run. |
| [24 — The front door](docs/24-the-front-door.md) | `rean check Demo.lean`. Three lines of Lean cost **39 declarations**, the one substitution that chapter 17's rule had missed, a limit that counted the wrong thing, and the instrument that is kept because a profiler cannot name a definition. |
| [25 — Twelve seconds](docs/25-twelve-seconds.md) | `rean show`, and the two bugs it found in an hour. Three knobs that reach nothing. And the number that reframes the project: **Lean's own kernel re-checks the whole prelude in 12 seconds**, so measure against something that is not yourself. |
| [26 — Thirty-four per cent](docs/26-thirty-four-per-cent.md) | six changes, **three kept and four reverted**. A hash that may refuse, a name that carries its own, and an allocator. Why one of them was worth nothing alone, why `Arc<[Level]>` made the common case worse, why the same fix was worth 120× in one function and nothing in its twin, and why **82% of the nodes this kernel builds are duplicates** and sharing them is still slower. |
| [27 — A program that runs](docs/27-a-program-that-runs.md) | **stage 5**. `rean run` checks a Lean program and then runs it, and the output matches Lean's. Why it needed no parser, why it is lazy, why `fib 25` took 2,571 steps rather than 242,785, and three silent bugs that were all the same bug: a runtime may know what a value **means** and not what it is **made of**. |
| [28 — The arena](docs/28-the-arena.md) | an outside conformance suite, and the six rules it found. What a kernel must **refuse**, scored by somebody else. |
| [Glossary](docs/GLOSSARY.md) | every term the chapters use, including what a check **costs** |
| [The guide](docs/README.md) | the reading order, part by part, and what you miss if you skip |
| [The references](docs/REFERENCES.md) | every paper, manual and source file the chapters cite, with one line on what each one answers |

Every chapter now ends with two sections: **How other systems do it**, which
says what Rocq, Agda, Isabelle, Haskell or Rust does in the same place, and
**References**, which names our code, the matching file in Lean's own source,
and the papers behind the rule.

Every claim in a chapter has a test:

```sh
devbox run -- cargo test -p rean_kernel --test universes   # chapter 0
devbox run -- cargo test -p rean_kernel --test typeck      # chapters 9 and 10
devbox run -- cargo test -p rean_export                    # chapters 11 and 12
devbox run -- cargo test -p rean_kernel --test structures  # chapter 17
devbox run -- cargo test -p rean_kernel --test cache       # chapter 18
devbox run -- cargo test -p rean_kernel --test comparison  # chapters 19 and 20
devbox run -- cargo test -p rean_kernel --test substitution # chapter 22
devbox run -- cargo test -p rean_kernel --test limits       # chapter 24
devbox run -- cargo test -p rean --test frontdoor           # chapter 24
devbox run -- cargo test -p rean --test show                # chapter 25
devbox run -- cargo test -p rean_eval                       # chapter 27
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

Chapters [19](docs/19-compare-before-you-unfold.md) and
[20](docs/20-ask-the-cheapest-question.md) are that method, worked twice.
Chapter [24](docs/24-the-front-door.md) is the third, and the tally above is
what made it quick: `delta Nat.sub._f` names a cause, and "`whnf` is 41%" does
not. A profiler cannot say **which** definition, and after chapter 21 that is
the only question left.

A third tool keeps the chapters honest. Every chapter cites its tests by name,
and `tools/cite.py` fails the gate when a chapter names a test that the code
does not define. It found six stale citations in chapter 9 the day it was
written, and chapter 9 says so.

```sh
devbox run cite
```

## The scoreboard

Every row is Lean **4.35.0-rc3**, exported by `rean export`. All three of the
libraries that the toolchain ships now run to completion, with no crash:

| Library | Declarations | Checked | Failed | Time |
|---|---|---|---|---|
| `Init`, the prelude | 59,349 | **55,835** | 72 | 155 s |
| `Std` | 99,619 | **95,237** | 120 | 268 s |
| `Lean`, the compiler | 171,817 | **150,420** | 127 | 299 s |

[Chapter 26](docs/26-thirty-four-per-cent.md) took **34%** off those times and
moved no verdict. Lean's own kernel still does the first row in 12 seconds.

```sh
cargo run --release -p rean -- check prelude
cargo run --release -p rean -- check Std
cargo run --release -p rean -- check Lean
```

| Checkpoint | Score | Meaning |
|---|---|---|
| level 1 | **95 of 95** | the two committed fixtures |
| level 1, the prelude | **55,835 of 59,349** | the default budget, in 155 seconds |
| level 1, patient | **59,199 of 59,349** | **99.75%**, with `REAN_FUEL=2000000000 REAN_STACK=8192`, in 36 minutes |
| level 1, what is left | one family of limits, and **5 real rejections** | the limits are `Int32`, `Int64` and `ISize`. The five are `_sizeOf_N_eq` lemmas of **nested** inductive types in `Lean`, where our kernel says no and Lean says yes. [Chapter 25](docs/25-twelve-seconds.md) names them. |
| level 2 | 0 of 32 | our pipeline inhabits Lean's types. Needs a parser. |
| level 3 | 0 of 32 | our term matches Lean's term |
| **stage 5** | **a program runs** | `rean run Prog.lean main`, and the output matches Lean's. [Chapter 27](docs/27-a-program-that-runs.md) |
| tests | **496** | `devbox run test` |
| citations | every chapter's test names resolve | `devbox run cite` |
| coverage | **93.1% of regions, 95.1% of lines** | `devbox run coverage` |
| red team | **39 lies refused** | `cargo test -p rean_kernel --test soundness` |
| trust | every axiom reported, by name | the `trust:` line of `rean check` |
| crashes | **none**, at any setting | the kernel reports `OutOfStack` instead. [Chapter 24](docs/24-the-front-door.md) |
| the oracle for speed | **12 s** | `leanchecker Init`, Lean's own kernel, all of it. We take 155 s. [Chapter 25](docs/25-twelve-seconds.md) |

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

Chapters [17](docs/17-structures-and-cost.md) and [18](docs/18-the-cache.md) are
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

[`docs/REFERENCES.md`](docs/REFERENCES.md) holds the full list, with one line on
what each source answers. The five that matter most:

- de Moura and Ullrich, *The Lean 4 Theorem Prover and Programming Language*,
  2021, for the design of the whole system.
  <https://lean-lang.org/papers/lean4.pdf>
- Ullrich and de Moura, *Beyond Notations: Hygienic Macro Expansion for Theorem
  Proving Languages*, 2020, for why the frontend is extensible.
  <https://arxiv.org/abs/2001.10490>
- Carneiro, *The Type Theory of Lean*, for the rules the kernel implements.
  <https://github.com/digama0/lean-type-theory>
- *The Lean Language Reference*, for what a user may rely on.
  <https://lean-lang.org/doc/reference/latest/>
- The Lean 4 source. `src/Lean/Parser`, `src/Lean/Elab` and `src/kernel` match
  stages 2, 3 and 4. <https://github.com/leanprover/lean4>

And the standard this project is held to:

- The Lean Kernel Arena, which times every independent checker on the same
  files and holds proofs that each one must refuse.
  <https://arena.lean-lang.org/>
