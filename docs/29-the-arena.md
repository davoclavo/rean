# Chapter 29 — The arena

> **Where you are.** It belongs with Part IV of
> [the guide](README.md), which is about what a checker must refuse.
>
> **Before this.** [What a checker must check](14-what-a-checker-must-check.md),
> which built the refusals, and
> [Mutual and nested](16-mutual-and-nested.md), which left some of them open.
>
> **After it you can** say what an outside test suite found that nineteen
> chapters of our own tests did not.

Chapter 14 asked "so does it have full coverage as a checker?" and answered
**no**, with an inventory. Chapter 14 wrote that inventory from the inside. This
chapter runs somebody else's.

The Lean Kernel Arena is a test suite for kernel checkers, from the Lean project
itself. It holds 198 export files: **126 that a checker must accept** and **72
that it must reject**. We scored 112 and 58.

Fourteen of the 72 lies were accepted. Every one of them is a soundness bug.

---

## 29.1 What the suite is, and the order it scores in

```sh
curl -sSLO https://arena.lean-lang.org/lean-arena-tests.tar.gz
tar xzf lean-arena-tests.tar.gz -C /tmp/arena
python3 tools/arena.py /tmp/arena
```

The files are `lean4export` NDJSON, format 3.1.0, written by Lean 4.34.1. So
chapter 25's front door reads them with no new code at all, and the whole suite
is one command.

The arena scores a bad test above a good one, and so does `tools/arena.py`.

1. A **bad** test we accept is a soundness bug. Nothing else on the list matters
   while one of those is open.
2. A **good** test we reject is a rule we are missing, or a limit we set too
   low.
3. The time comes last.

### The distinction the harness adds

A bad test that we reject **because we ran out of budget** is the right answer
for the wrong reason. The kernel says so itself: `OutOfFuel` and `OutOfStack`
mean "we did not check it", and not "this is wrong". A checker that refused
everything would score perfectly on the bad half and be useless, and the way
that failure starts is one test at a time.

So `tools/arena.py` reads the message. A rejection by a limit is counted and
named apart from a rejection by a rule, which is the same rule chapter 26 sets
for `TypeError::is_a_limit`.

---

## 29.2 The score

| | before | after |
|---|---|---|
| accepted of 126 good | 112 | **115** |
| rejected of 72 bad | 58 | **72** |
| wrongly accepted, which are soundness bugs | **14** | **0** |
| wrongly rejected by a **rule** | 3 | **0** |
| wrongly rejected by a **limit**, or no answer in 300 s | 11 | 11 |

The 11 that remain are chapter 26's subject and not this chapter's. They are
`perf/` tests, built to be expensive, and each one reports a budget rather than
a verdict.

The three libraries hold their counts exactly, which is the measurement that
mattered most while this chapter was written:

| library | declarations | checked | time |
|---|---|---|---|
| `Init`, the prelude | 59,349 | 55,835 | 141 s |
| `Std` | 99,619 | 95,237 | 217 s |
| `Lean`, the compiler | 171,817 | 150,420 | 234 s |

Six new rules, 504 tests, and not one declaration of three real libraries
changed its verdict. That is the shape a soundness fix should have.

---

## 29.3 Five of the six rules were not about terms at all

Nineteen chapters built the term rules: β, δ, ι, ζ, η, proof irrelevance,
projection, strict positivity, universes, recursor shape. The arena found one
hole there. The other five holes were in the **paperwork**.

| the lie | the arena test | the rule it needed |
|---|---|---|
| a `Prop` with two elements eliminating into `Type` | `bad/bugs/large-elim-param` | a universe parameter **can** be zero |
| data read out of a proof | `bad/bugs/proj-of-imax-prop`, `tutorial/090` to `094` | a proof has no fields |
| a theorem that is its own proof | `tutorial/014_selfProof` | a declaration may not see itself |
| a theorem whose statement is not one | `tutorial/012_nonPropThm` | a theorem states a proposition |
| an inductive type that is no type | `tutorial/047`, `049`, `139` | three questions about a declaration |
| a constructor of a type that is absent | `other/orphan-ctor` | a constructor belongs to its type |
| a recursor under another name | `tutorial/136`, `137` | a recursor is called `I.rec` |

Read `other/orphan-ctor`, which is the clearest of them:

```text
inductive False : Prop            -- declared with no constructors
ctor rogue : False, of Orphan     -- a constructor of a type that is
                                  -- nowhere in the file
theorem inconsistent : False := rogue
```

Every term rule in this kernel agrees with that file. `rogue` has the type the
file gives it, the type is `False`, and the theorem's value has the theorem's
type. There is nothing to reduce and nothing to compare. The only place to
catch it is the declaration itself, where a constructor names the type it comes
from and nobody had asked that type whether it agreed.

`Self::check_constructor_owner` asks. `Self::check_inductive` asks the three
questions behind `tutorial/047`, `049` and `139`. `Self::check_proposition`
asks whether a theorem states anything. And `tutorial/014_selfProof` is four
words long:

```text
theorem selfProof : ∀ (p : Prop), p := selfProof
```

That one was **our own doing**. `with_group` makes a mutual group visible to
its own members, because an inductive type, its constructors and its recursor
arrive on one line of the export and speak about each other. A theorem gets a
group of one, which is itself. So the proof was in the environment while the
kernel checked it.

The fix is to hide the declaration rather than to look for a cycle, because
hiding costs nothing: the name is simply not there when `lookup` asks, and
Lean's own kernel reports the same thing for the same reason, an unknown
constant.

> **A term rule is a rule about a term. A declaration is a claim about the
> world.** We had spent nineteen chapters on the first kind.

---

## 29.4 Two questions about a universe, one rule apart, opposite answers

The first soundness bug and the second are both about whether a `Sort` is
`Prop`. They need opposite questions, and that is the part worth keeping.

### The careful question, for elimination

`bad/bugs/large-elim-param` declares `MyBool.{u} : Sort u` with two
constructors, and a recursor that eliminates into `Sort v`. A `Prop` with two
elements may not do that. Chapter 14, section 14.3 is the rule, and
`check_elimination_universe` had it.

It asked `Level::is_zero`, which answers "is this level **written** as zero".
The level was `u`, a parameter, so the answer was no, and the recursor went
through. Then the file instantiated `u := 0` and proved `False`.

So the question has to be "**can** this level be zero", and `Level::is_never_zero`
answers it. A universe parameter is not a proof that the universe is not zero.

### The definite question, for a projection

The projection rule of section 29.5 asks the same thing about the structure it
is projecting, and asking it carefully would refuse real code.
`PProd.{u, v} : Sort (max u v)` **can** be a `Prop`, its fields are `Sort u`
and `Sort v`, and the Lean prelude projects one of them millions of times
inside `Nat.below`. Chapter 26, section 26.4 counted those.

The definite question is safe there, and the reason is the universe constraint
of chapter 16, section 16.4: an inductive type's universe bounds its fields. A
structure whose level really is zero has fields whose levels are zero, and one
whose level is a parameter becomes a `Prop` only in an instantiation where its
fields do too. The attack needs a `Prop` with a field that is not a proof, and
the constraint forbids that unless the declaration lied, which is what
`check_field_universes` is for.

> One rule needs "can it be zero" and its neighbour needs "is it zero", and
> each one is **wrong** in the other's place. The first version of this chapter
> got that backwards and the prelude said so within the minute: every `PProd`
> projection in `Nat.below`.

---

## 29.5 A proof has no fields

Proof irrelevance makes any two proofs of one proposition definitionally equal.
So a `Prop` that carried **data** would have two equal proofs whose data
differed, and that is `False` in four lines:

```text
inductive ImaxProp : Prop where mk (b : Bool)
def  f (p : ImaxProp) : Bool := p.1          -- we accepted this
theorem irrel : mk false = mk true := rfl    -- proof irrelevance
theorem bad : False := by rewrite irrel; ... -- and then False
```

`structure_params` asks three questions of a type before it allows a
projection: one constructor, no index, not recursive. Lean asks a fourth, and
it is about the **field**: in a `Prop`, the field must be a `Prop` too.

`Exists` is the same shape and the same hazard: one constructor, no index, not
recursive, and a first field that is data. `And` and `Iff` are **not** stopped,
and that is why the question is about the field and not about the structure.
Their fields are proofs, so irrelevance covers the fields as well, and `h.1` is
sound.

### The six tests that pin the rule down

The arena spends `tutorial/089` to `094` on one structure. It is a `Prop`, and
its six fields alternate.

| field | its type | the arena says |
|---|---|---|
| 0 | a proof | accept |
| 1 | data | refuse |
| 2 | a proof | **accept** |
| 3 | data | refuse |
| 4 | a proof about field 3 | refuse |
| 5 | a proof | **refuse** |

Fields 2 and 5 have the same type. One is good and one is bad, so the rule
cannot be only about the field that was asked for.

It is about the fields the kernel **steps over**. A later field type can mention
an earlier field, so `infer_proj` fills each earlier binder with a projection of
the same term. To reach field 5 it must put `x.3` into the type of field 4, and
`x.3` is a projection it would refuse. To reach field 2 it steps over fields 0
and 1, nothing later mentions either, and it substitutes nothing.

So the question is asked where the substitution happens, and one field read
decides whether it happens at all:

```rust
if body.loose() == 0 {
    ty = body.to_expr();
    continue;
}
if a_proof {
    self.field_must_be_a_proof(proj, index, &binder_type.to_expr())?;
}
```

`Sub::loose` is the count this kernel stores on every node, from chapter 10. It
was put there to make instantiation cheap, and here it is the thing that
separates a good test from a bad one.

**Honest note on where this rule came from.** The six tests pin it exactly, and
that is how it was derived. This repository does not hold Lean's C++ kernel, and
no claim here rests on a line of it that was not read.

`a_proof_may_not_be_asked_for_its_data` and
`the_fields_on_the_way_are_asked_as_well` are the tests.

---

## 29.6 A new rule broke an old one, twice, in the same way

The projection rule refused four theorems of `Std`:

```text
FAIL  theorem  Std.DTreeMap.Internal.Impl.Const.getEntryGE_eq
      field 0 of `Exists` lives in `Sort u+1` and `Exists` is a `Prop`
```

`Exists.0` is the witness, and the rule is right to refuse it. But no file asked
for that projection. **The kernel built it.**

Two rules build a projection out of nothing:

- `struct_eta_eq`, which compares `p` with `S.mk p.1 p.2` and is chapter 14,
  section 14.5;
- the ι rule's structure case, which rewrites a recursor over an opaque
  structure into its constructor applied to the projections of that structure.

Both now decline for a `Prop`, which is what Lean does, and the reason is that
proof irrelevance has already answered the question those rules were about.

The way the failure showed itself is the part to keep. `struct_eta_eq` carries
this comment, from the chapter that wrote it:

> A comparison helper must decline, never error.

The new rule walked straight into it. `is_def_eq` asked a question, a helper
built a term, the term was refused, and the **error left `is_def_eq`
altogether** and failed a declaration over a rule that simply did not apply.
The test `a_comparison_helper_declines_rather_than_errors_on_an_open_term` was
already in the repository, about a different cause of the same fault.

Then the reduction side said the same thing a second time.
`the_rule_declines_when_the_type_is_missing_its_parameters` builds a term whose
type has no sort at all, to check that the ι rule declines. The new guard asked
for a sort and got an error. So the guard asks the careful way:

```rust
match self.infer_sort(&major_type) {
    Ok(level) if level.normalize().is_zero() => return Ok(None),
    Ok(_) => {}
    Err(err) if err.is_a_limit() => return Err(err),
    Err(_) => return Ok(None),
}
```

A limit is the one answer that still has to travel. It does not mean "no".

---

## 29.7 Reduce before you judge

Three **good** tests were refused, and all three were one missing rule.
`good/tutorial/055_reduceCtorParam.mk` is the smallest:

```text
def constType (a b : Type) : Type := a
inductive I (α : Type) where
  | mk (x : constType (I α) (I α))
```

The field type reduces to `I α`, which is a plain recursive occurrence and
exactly what a constructor is allowed to hold. Unreduced, its head is
`constType`, a function the positivity check knows nothing about, and an
occurrence in the argument of such a function is refused. So we refused a
declaration that Lean built, and the recursor that went with it.

Two sites, and the first was a two-line bug of a kind worth naming.
`induction_hypothesis_inner` asked `whnf` whether a field type was a function
and then **went on with the type it had before**:

```rust
while let Expr::Forall { .. } = self.whnf(&ty)? {   // the answer, discarded
    ty = body.instantiate(&Expr::FVar(id));
}
```

The two forms differ exactly when a definition stands where a type should. So
the field looked like data, the premise needed no induction hypothesis, and the
recursor Lean built did not match the one we derived.

The second site is the positivity check itself. It is a syntactic check, so it
has to read the shape the type **reduces to**, and `reduced_telescope` gives it
that shape. It reduces under every binder of a field type, because
`tutorial/119_reduceCtorParamRefl.mk` hides the occurrence one binder deeper.

### The direction nobody was looking at

That is a false rejection, and fixing it was politeness. The other direction is
not:

```text
def Bad (X : Type) : Type := (I X) → Unit
inductive I (α : Type) where
  | mk (x : Bad α)
```

`Bad α` holds no occurrence of `I` **at all**, so the old check had nothing to
refuse. The reduced form has `I` to the left of an arrow, which is the negative
occurrence that strict positivity exists to stop.

> A syntactic check that does not reduce can be fooled by **hiding** the thing
> it looks for, and not only by dressing it up. The arena tests the polite
> direction. The other one was open the whole time and no test of ours would
> ever have found it.

---

## 29.8 What is still open

The arena is a sample, and these are the things it leaves or confirms.

- **11 tests report a limit** and not a verdict. All 11 are `perf/`, which is
  chapter 26's subject: a budget of 40,000,000 nodes and a 6 MiB stack are what
  stand between us and an answer. Chapter 27 made the same work 34% cheaper and
  did not change what a budget buys.
- **5 declarations of `Lean` still fail**, all of the shape
  `Lean.Elab.Term.Do.Code._sizeOf_4_eq`. They are nested inductives, which
  chapter 16, section 16.5 says this kernel trusts rather than checks.
- **Nested positivity is still trusted.** `tutorial/` has no test that attacks
  it, and chapter 14's inventory still names it first.
- **Mutual recursors above one motive are still skipped**, for the same reason
  and with the same honesty.
- **Scale is not tested.** The arena's files are tens of declarations. Mathlib
  is the next ground truth and nothing here says we can read it.

---

## 29.9 How other systems do it

| | what it is | what it reads |
|---|---|---|
| `leanchecker` | Lean's own kernel, over `.olean` | the compiled library |
| `lean4lean` | Lean's kernel, written again in Lean | the environment, inside Lean |
| `nanoda` and `trepplein` | independent checkers, in Rust and in Scala | the export format |
| `rean` | this | the export format |

Four notes.

- **The arena exists because this is a crowded field.** A kernel checker is a
  small program with one job, so several people write one, and a shared suite is
  how the field keeps them honest. It is the same role that `lean4export` plays
  for the format.
- **Lean's own kernel does not read a recursor from a file.** It builds one from
  the inductive declaration. This kernel reads it and checks it, which is the
  harder half, and section 29.3's name rule is the other half: it is what stops
  a second rule for one type.
- **`lean4lean` is the strongest statement of the same idea.** It is Lean's
  kernel written in Lean and proved correct against the paper rules, so a bug
  in it is a bug in a theorem. Ours is a Rust program with 504 tests.
- **The arena's own scoring is the one this chapter copies.** Soundness first,
  completeness second, speed last. A checker that is fast and wrong has the
  numbers of a checker that does not work.

---

## 29.10 References

**Our code**

- `crates/rean_kernel/src/typeck.rs`, where all six rules live
- `crates/rean_kernel/src/level.rs`, for `Level::is_never_zero`
- `crates/rean_kernel/tests/soundness.rs`, the red team file. Eight of its
  tests are the arena's, and every one of them failed before this chapter.
- `tools/arena.py`, the harness of section 29.1

**The suite**

- The Lean Kernel Arena. <https://arena.lean-lang.org/>
- `lean4export`, which writes the format the suite is in.
  <https://github.com/leanprover/lean4export>

**Read more**

- Carneiro, *Lean4Lean: Towards a formalized metatheory for the Lean theorem
  prover*, 2024, for a kernel whose correctness is a theorem.
  <https://arxiv.org/abs/2403.14064>
- Carneiro, *The Type Theory of Lean*, 2019, for the rules every one of these
  checkers implements.
  <https://github.com/digama0/lean-type-theory/releases>
- *The Lean Language Reference*, the kernel, for what Lean itself promises about
  a declaration it accepts.
  <https://lean-lang.org/doc/reference/latest/>

---

**Next:** [The eleven that were not wrong](30-the-eleven.md)
