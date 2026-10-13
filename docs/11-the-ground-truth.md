# Chapter 11 — The ground truth

> **Where you are.** Chapter 11 of 28, in Part III of [the guide](README.md).
>
> **Before this.** Part II, both chapters. You need an environment to read a
> file into.
>
> **After it you can** check terms that the real Lean elaborated, out of a file
> that any program may read.

Every test so far was written by hand. That proves the checker agrees with its
author, and nothing more.

This chapter points the checker at the real Lean.

```sh
devbox run -- cargo run -p rean -- check fixtures/lean4export/Nat.add_succ.ndjson
devbox run -- cargo test -p rean_export
```

## The result

```
fixtures/lean4export/Nat.add_succ.ndjson
  lean4export 3.0.0, format 3.0.0, Lean 4.27.0-rc1
  32 declarations

  ok    inductive  Nat
  ok    ctor       Nat.zero
  ok    ctor       Nat.succ
  ok    rec        Nat.rec
  ok    inductive  Eq
  ...
  ok    def        Nat.add
  ok    def        rfl
  ok    theorem    Nat.add_succ

level 1: checked 32 of 32 declarations
```

Our kernel verified `theorem Nat.add_succ` and every declaration it depends on,
from a file that the real Lean wrote. That is the level 1 checkpoint of
`docs/ROADMAP.md`.

---

## 11.1 What `lean4export` is for

Chapter 0, section 0.16 described the De Bruijn criterion. The elaborator, the
macro system, and every tactic are **untrusted**, because the kernel re-checks
their output from nothing.

`lean4export` takes the idea one step further. It writes the elaborated terms to
a file so that a **different program** can check them. If two kernels written by
different people in different languages agree, the chance that both hold the
same bug is small.

`rean` is now one of those programs.

---

## 11.2 The format

NDJSON. One JSON object per line. The first line is a `meta` object with three
version numbers. Every later line defines one object at an index, and refers to
earlier objects by index.

```json
{"meta":{"exporter":{"name":"lean4export","version":"3.0.0"}, ...}}
{"in":1,"str":{"pre":0,"str":"Nat"}}
{"il":1,"succ":0}
{"ie":0,"sort":1}
```

Read those four lines in order:

1. The versions.
2. Name index 1 is the name `Nat`, whose prefix is name index 0.
3. Level index 1 is the successor of level index 0.
4. Term index 0 is `Sort` of level index 1, which is `Type`.

The index key names the table: `in` for a name, `il` for a level, `ie` for a
term. A line with none of those three is a declaration.

---

## 11.3 Four facts that came from the file, not the document

The format document answers none of these. A real file answers all four in a
minute.

| Question | Answer |
|---|---|
| Is name index 0 pre-populated? | **yes.** No line defines it. It is the anonymous name. |
| Is level index 0 pre-populated? | **yes.** No line defines it. It is `Level::Zero`. |
| Is term index 0 pre-populated? | **no.** Terms start at 0 and the first term line defines it. |
| Does a reference point backwards? | **yes.** One pass is enough. |

So the reader seeds two tables and not three:

```rust
names.insert(0, Name::anonymous());
levels.insert(0, Level::Zero);
```

The test is `index_zero_is_implicit_for_names_and_levels`.

## 11.4 Two places where the document is wrong for this file

| Thing | The document says | The file says |
|---|---|---|
| inductive fields | `types`, `ctors`, `recs` | `inductiveVals`, `constructorVals`, `recursorVals` |
| a `def` or `thm` payload | one object | an **array** of them, for a mutual group |

The document on the `lean4export` master branch describes a newer format. Master
pins Lean v4.35.0-rc4, and the fixture reports format 3.0.0 and Lean 4.27.0-rc1.

So the reader does two things:

- It **rejects** a format version it does not know, rather than guess:
  ```
  this reader knows export format 3.0.0, and the file says 9.9.9
  ```
- Where the two spellings differ, it accepts either.

JSON key order also varies from line to line, so the reader never depends on it.

---

## 11.5 Our `Expr` already matched

The term layer needed no translation. Every former lines up:

| Our type | The file |
|---|---|
| `Name::Str { prefix, part }` | `{"str": {"pre": i, "str": s}}` |
| `Name::Num { prefix, part }` | `{"num": {"pre": i, "i": n}}` |
| `Level::Succ`, `Max`, `IMax`, `Param` | `succ`, `max`, `imax`, `param` |
| `Expr::BVar`, `Sort`, `Const`, `App` | `bvar`, `sort`, `const`, `app` |
| `Expr::Lam`, `Forall`, `Let` | `lam`, `forallE`, `letE` |
| `Expr::Proj` | `proj` |
| `Literal::Nat` holding digits as text | `{"natVal": "123"}`, a **string** |
| `BinderInfo`, four cases | `"default"`, `"implicit"`, `"strictImplicit"`, `"instImplicit"` |

The `natVal` row was luck. Chapter 0 stored the digits as text because a Lean
`Nat` has no upper bound, and the format did the same thing for the same reason.

Two differences, both small:

- The file has `mdata`, an annotation node. Our `Expr` has none, so the reader
  **drops** the annotation and keeps the inner term. That is sound. `mdata`
  carries no meaning for the kernel.
- `letE` carries a `nondep` flag that we ignore.

Note what the format does **not** have: no `FVar` and no `MVar`. Chapter 0,
section 0.14 predicted that. A finished declaration holds neither.

---

## 11.6 The harness

```rust
let mut known = Environment::new();
for name in &module.order {
    let decl = module.env.get(name).unwrap();
    let mut tc = TypeChecker::new(&known);
    match tc.check_declaration(decl) { /* count it */ }
    known.add(decl.clone());          // only now
}
```

Three choices matter.

1. **In file order.** A later declaration uses an earlier one.
2. **Add after checking.** A declaration can only use the ones before it, so a
   circular definition cannot prove itself.
3. **Add even on failure.** One broken declaration should not cascade into a
   hundred `unknown constant` errors.

The report is one line per declaration and one number at the end. That number is
the whole point. It turns every later chapter into a measurable step.

---

## 11.7 What the fixture found that hand-written tests did not

The fixture is the transitive closure of one theorem: 32 declarations, 103
names, 15 levels, 434 terms. It covers an inductive declaration, a recursor
with its ι rules, a projection, universe polymorphism, type class instances, and
the helpers Lean generates on its own, such as `Nat.add.match_1` and
`Nat.brecOn`.

On the first run, 31 of 32 passed. The one failure was the theorem itself.

### The bug

`theorem Nat.add_succ` says `n + Nat.succ m = Nat.succ (n + m)`, and its proof
is `rfl`. So the kernel must show the two sides are definitionally equal. That
needs the whole chain: δ through `HAdd.hAdd`, `instHAdd`, `Add.add`,
`instAddNat`, and `Nat.add`; then ι on `Nat.rec` inside `Nat.brecOn`; then a
projection out of a `PProd`.

Every one of those worked. `n + Nat.zero` reduced to `n` correctly.

The failure was in the comparison. After reduction, both sides looked like this:

```
Nat.succ ( (Nat.rec ... m).1 n )
```

Look at the inner term. Its application spine is headed by a **projection**, not
by a constant. And `spine_eq` had arms for a `Const` head, an `FVar` head, and a
`BVar` head, and then:

```rust
_ => return Ok(false),
```

So the comparison gave up. The cure is four lines:

```rust
(Expr::Proj(p1), Expr::Proj(p2)) => {
    if p1.index != p2.index || !self.is_def_eq(&p1.value, &p2.value)? {
        return Ok(false);
    }
}
```

The recursion ends because the target of a projection is strictly smaller than
the whole term.

### Why no hand-written test caught it

A projection at the head of a spine is not a shape anybody writes by hand. It is
what the **compiler** produces when it compiles a recursive definition through
`brecOn`. Our own tests used lambdas, applications, and sorts, because those are
the shapes a person thinks of.

That is the argument for the ground truth, in one bug. The test is
`the_step_case_of_addition_is_definitionally_equal`, and its doc comment says
what it guards.

---

## 11.8 What is still missing

The fixture passes, and the checker is still not one you should trust.

| Missing | Why it matters |
|---|---|
| the strict positivity check | a crafted `inductive` can prove `False`. We trust every one. |
| recursor re-derivation | we trust the recursor and the ι rules that the file hands us |
| K-like ι reduction | `Eq.rec` reduces only when its major premise is already `Eq.refl` |
| the quotient rules | `Quot` is stored and never computed |
| a full level normal form | a hard pair of open levels can fail to match |
| `Nat` and `String` literal arithmetic | the real kernel computes on them directly |

The first two are the important ones. A checker that believes the recursor it
reads is checking arithmetic, not soundness. Roadmap stage 5 closes them.

Three gaps have a test that asserts the wrong answer on purpose, so closing one
will break a test and that is the reminder.

---

## 11.9 How to get a bigger fixture

`fixtures/lean4export/PROVENANCE.md` has the details. The short version:
`lean4` 4.30.0 is in devbox, and `lean4export` master pins v4.35.0-rc4, so it
does not build here yet. Three ways out, none done:

1. Install `elan` and let it fetch the pinned toolchain.
2. Check out a `lean4export` commit that matches the devbox Lean.
3. Bump the devbox `lean4` version.

Once one of them works, the next number to chase is the whole Lean prelude. The
pass rate will drop a long way, and that is the point.

---

## 11.10 Exercises

1. The reader rejects an unknown format version. Argue for and against accepting
   it with a warning instead.
2. The harness adds a declaration even when the check fails. When is that the
   wrong choice?
3. `mdata` is dropped. Prove to yourself that the dropped annotation cannot
   change whether a term checks.
4. Our kernel trusts the recursor in the file. Sketch what it would take to
   derive `Nat.rec` from the `Nat` declaration instead.
5. Term index 0 is defined by a line, and name index 0 is not. Why would a
   format designer make them different?

### Answers

1. **For:** a newer format is mostly the old one, so a warning would let the
   tool keep working. **Against:** a silent field change gives a wrong answer
   rather than an error, and a checker that says yes when it should say no is
   worse than useless. The second argument wins for a checker.
2. When a failed declaration is an `axiom` that the rest of the file leans on.
   Then the count of later passes is meaningless. A report should say which
   declarations rest on a failure.
3. The kernel never reads `mdata`. No type rule and no reduction equation
   mentions it, so a term with it and a term without it take the same path.
4. You need the motive, one minor premise per constructor shaped from the
   constructor's fields, the ι rule per constructor, and a check that each
   recursive occurrence is in a strictly positive position. That last check is
   what makes the whole thing sound.
5. The anonymous name and the zero level are the unique roots of their trees, and
   every name and every level is built from them. A term has no such root.

---

## 11.11 How other systems do it

Every system that wants a second opinion needs a file that a second program can
read. The designs differ in one choice: text that anybody can parse, or an image
of the prover's own memory.

| System | The file | Who can read it |
|---|---|---|
| Lean 4 | an `.olean` file, which is an image of a compacted heap | Lean, on the same version and the same machine word size |
| Lean 4 | an export file from `lean4export`, which is the text format of this chapter | any program, on any machine |
| Rocq | a `.vo` file, re-checked by the separate tool `coqchk` | Rocq, and `coqchk` |
| Isabelle | a proof term, when a user asks for one | Isabelle, and a tool that reads its format |
| Metamath Zero | a binary proof file, with a text form beside it | a verifier of a few thousand lines |

Two notes.

- **The format is boring on purpose.** One object per line, and a reference is
  an index into what came before. There is no name resolution, no notation and
  no implicit argument left to work out. That is what makes a second checker
  possible in a weekend, and it is why chapter 19 can cut a file in half with
  `tools/slice.py` and still have a valid module. The later chapters call that
  cut a **slice**, and it is how one failing declaration gets looked at alone.
- **A version check is not a formality.** Section 3.4 shows the format
  document describing a newer format than the file. The reader refuses a
  version it does not know, because a silent guess about a format is how a
  checker says yes to something it never read.

## 11.12 References

**Our code**

- `crates/rean_export/src/reader.rs`, the reader
- `crates/rean_export/tests/fixture.rs`, `shapes.rs`, `every_shape.rs`,
  `completeness.rs`, `scratch_order.rs`
- `fixtures/lean4export/PROVENANCE.md`, how each fixture was made

**The tools**

- `lean4export`, the exporter. <https://github.com/leanprover/lean4export>
- `lean4checker`, Lean re-checking its own library from outside the compiler.
  <https://github.com/leanprover/lean4checker>
- `src/LeanExport.lean` and `src/LeanChecker.lean` in the Lean source. Recent
  toolchains ship both as binaries, which is why chapter 25 can time Lean's own
  kernel on the same machine.

**Read more**

- *The Lean Language Reference*, validating proofs, for the reason an external
  checker exists, in the project's own words.
  <https://lean-lang.org/doc/reference/latest/ValidatingProofs/>
- The Lean Kernel Arena, which runs every independent checker against the same
  files. <https://arena.lean-lang.org/>
- Carneiro, *Lean4Lean*, for a second checker with a proof about it.
  <https://arxiv.org/abs/2403.14064>
- Barendregt and Barendsen, *Autarkic computations in formal proofs*, 2002, for
  the criterion this chapter serves.
  DOI [10.1023/A:1015761529444](https://doi.org/10.1023/A:1015761529444)

---

**Next:** [Making it work](12-making-it-work.md)
