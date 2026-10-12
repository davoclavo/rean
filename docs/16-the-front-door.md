# Chapter 16 — The front door

Fifteen chapters built a kernel that reads 99.57% of the Lean prelude, and
there was no way to point it at a file of your own.

That is the gap this chapter closes, and it turns out the gap had two halves.
One is a missing command. The other is that the checker could not survive its
own best settings: at a hundred times the default budget it did not report a
failure, it **aborted**.

---

## 16.1 The command that was missing

`rean check foo.ndjson` needed an export file, and making one took a page of
`fixtures/lean4export/PROVENANCE.md`: clone `lean4export`, match its toolchain,
patch a link line for the macOS SDK, set `LEAN_PATH`, and run it. Every
instruction was true and nobody was going to follow them.

Now:

```sh
rean check Demo.lean --decl twice_two
rean check prelude
rean check Some.Module
rean export Demo.lean
```

The driver finds the real Lean, compiles the file, runs the exporter, and checks
every declaration that comes out.

Three facts about the design, each of which is a decision somebody will
otherwise have to guess.

**The target tells you what it is.** `.ndjson` is an export, `.lean` is source,
`prelude` is `Init`, and anything else is a module name. There is no `--kind`
flag, because the answer is already written in what the reader typed.
`Target::parse` is the whole of it. Tests:
`an_ndjson_path_is_an_export_and_a_lean_path_is_source`,
`check_with_a_missing_export_file_fails`.

**The two binaries must come from one toolchain.** An exporter reads the
`.olean` files that its own Lean wrote. A mismatched pair fails with a message
about a header, not about a version, so the search takes both from the same
directory or it reports that it found neither. `REAN_LEAN` and
`REAN_LEANEXPORT` override it, and a variable that names a file which is not
there is an **error** and not a silent fall back to a search: a reader who
mistypes a path must hear about the path, not get a verdict from a different
Lean. Tests: `an_override_that_names_nothing_is_an_error_and_not_a_silent_search`,
`the_error_names_the_variable_that_fixes_it`.

**Lean's errors stay Lean's.** A file that does not compile gets Lean's own
message, and our kernel never sees the file. Test:
`lean_refuses_a_bad_file_and_we_pass_its_message_on`.

One check that the front door changes nothing: the file it writes for the
prelude is **byte for byte** the file this chapter's measurements were taken
on, which was made by hand with the page of instructions above.

```sh
rean export prelude --out /tmp/pre     # 329.7 MB in 14.0s, by Lean 4.35.0-rc3
cmp /tmp/pre/Init.ndjson prelude.ndjson
```

---

## 16.2 What three lines of Lean cost

```lean
def twice (n : Nat) : Nat := n + n

theorem twice_two : twice 2 = 4 := rfl
```

```text
export: Demo -> /tmp/rean-export/Demo.ndjson (41 KB) in 0.3s, by Lean 4.35.0-rc3
  ok    inductive  Nat
  ok    ctor       Nat.zero
  ...
  ok    theorem    twice_two

level 1: checked 39 of 39 declarations
trust: no accepted declaration rests on an axiom
```

**Thirty-nine declarations for one theorem.** `Nat` and its two constructors,
`Nat.rec`, `Nat.add` and the `match` helper the equation compiler left behind,
`HAdd`, `Add`, `OfNat`, `instAddNat`, and the instances between them.

That number is the point of level 1, and it is worth saying plainly. A checker
that trusted the library and looked only at the theorem would be checking
almost nothing. The trust line is the other half of the same idea: it names
every axiom that an accepted declaration rests on, and here there are none.

The export is the whole transitive closure of the module by default, which for
anything that imports the prelude is 345 MB and a few minutes. `--decl` cuts it
to one declaration and what that declaration needs. Test:
`a_lean_file_reaches_our_kernel`.

---

## 16.3 One substitution that rebuilt everything

Before any of the above could be measured honestly, a profile of the hardest
declaration said something embarrassing.

Half the samples were in the allocator, and `Expr::instantiate_levels` was
near the top of what fed it.

`/usr/bin/sample` for 15 seconds, on the slice that holds the declaration which
blocks 2,283 others, at `REAN_FUEL=1600000000 REAN_STACK=4096`. 8,963 samples
on the thread that does the work, by what sat at the top of the stack:

| frame | samples |
|---|---|
| `malloc` and `free`, every variant | about 4,000 |
| `Sub::new`, which builds a node | 926 |
| the drop of an `Expr` | 777 |
| hashing a new node | 790 |
| `Expr::instantiate_levels` | 365 |
| `Expr::instantiate_many_at` | 252 |
| the clone of an `Expr` | 222 |

**Nearly half of it is the allocator**, and every allocation is a node of a
term that one reduction step built and the next one dropped.

`Expr::instantiate_levels` replaces the universe parameters of a definition
with the arguments at the call site, and the δ rule calls it on **every single
unfold**. It rebuilt every node of the value, every time, whether or not any
universe parameter appeared anywhere in it.

Chapter 9 fixed exactly this fault for `instantiate_at` and `lift`, and
measured a factor of fifteen in the frames it moved. The rule it set is "return
**nothing changed** and keep the existing `Arc`". `instantiate_levels` is the
one substitution in the kernel that never got the rule, and it is the one the δ
rule leans on hardest: on one declaration of the prelude, `Nat.casesOn` unfolds
283,803 times.

So `Level::substitute_opt` and `Expr::instantiate_levels_opt` return
`Option`, and `None` means the caller keeps what it has.

The same slice, same 4 GB stack, and one of the two rows reaches the end:

| budget | before | after |
|---|---|---|
| 400,000,000 | 20.5 s | 16.8 s |
| 1,600,000,000 | 33.3 s | 29.5 s |

Tests: `a_term_with_no_universe_parameter_is_not_rebuilt`,
`a_level_that_names_another_parameter_is_not_rebuilt`,
`the_parameter_is_still_replaced_where_it_appears`.

Two things to take from that table, and the second one matters more.

The **verdicts did not move.** Not one more declaration checked. That is
chapter 9's rule stated for the fourth time: the budget is charged by work, so
a faster kernel does the same work faster. A reader who wants more declarations
must make the work **smaller** or the budget **bigger**. Speed alone buys
nothing.

And it explains a measurement that chapter 15 recorded as a mystery. Section
15.6 cached the result of this very substitution, keyed by name and levels, and
got **nothing** for it, slightly slower. The reading was "a cache for an
unmeasurable gain is a cost with no payment", which is true and is not the
cause. The cause is that the work being cached was work that never needed
doing. **A cache cannot help where the answer should have been "nothing
changed".**

---

## 16.4 A hundred times the budget, and the crash it found

With the front door working, the obvious measurement is the whole prelude at a
budget large enough to finish it. Chapter 15 had reached 99.57% at forty times
the default.

```sh
REAN_FUEL=2000000000 REAN_STACK=4096 rean check prelude
```

```text
  ok    theorem    ISize.ofInt_eq_ofNat

thread '<unknown>' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

A hundred times the budget, a stack eight times the default, and the run
**died** after 16,583 declarations. Not a slow declaration: a dead process, and
a dead process reports nothing about the 42,766 declarations it had not reached.

Chapter 15 section 15.11 had met this shape and read it correctly: *a
measurement that reads a crash as a timeout is a measurement that has not been
checked*. The cause is the same one it named. To reduce a recursor the kernel
must first reduce the **major premise**, and the major premise can be another
recursor application, so the recursion is as deep as the term, and the term is
one that the reduction itself built.

Section 15.11 fixed one instance of it by capping how far `read_nat` forces a
nested argument. That cap was right and it was local. The general case needs a
guard where the recursion is.

> **A limit that the checker cannot survive is not a limit. It is a crash with
> a plan.**

---

## 16.5 The guard that counted the wrong thing

The obvious guard is Lean's. Lean bounds its own recursion with `maxRecDepth`,
a count of levels, and reports when it is reached. So the kernel counted levels
on entry to `whnf`, `is_def_eq` and `infer_type`, which is where every deep
chain this project has ever overflowed a stack went through.

It worked, and then the measurement refused the design.

| stack | depth 100,000 | depth 200,000 |
|---|---|---|
| 512 MB | holds | **overflows** |

So a level costs about 5 KB on that chain, and 100,000 levels is what 512 MB
carries. But the chain that actually goes deep is `whnf -> reduce -> whnf`, and
those frames are far smaller than 5 KB, so the same 512 MB carries many more of
**those**.

There is no right count. A count set for the fat path refuses work the thin path
can finish, and a count set for the thin path crashes on the fat one. Lean can
use a count because `maxRecDepth` is a limit on the **elaborator**, where a
level is one user-visible step; here a level is whichever of three functions
happened to be entered.

So the kernel measures the thing it is running out of:

```rust
#[inline]
fn check_stack(&mut self) -> TypeResult<()> {
    let here = stack_pointer();
    if self.stack_base == 0 {
        self.stack_base = here;
    }
    // The stack grows down, so the base is the larger address.
    let used = self.stack_base.saturating_sub(here);
    if used >= self.stack_budget {
        return Err(TypeError::OutOfStack(self.stack_budget));
    }
    Ok(())
}
```

The address of a local against the address of one at the start. Two
instructions, no counter, and **nothing to undo on the way out**, because the
measurement falls as the stack unwinds by itself. The count needed an increment
and a decrement, and a decrement that an early return skips is a bug waiting
for a deep term.

The allowance is `REAN_STACK` less a margin, and the margin is **64 MB and not
a fraction**. That is also a measurement, and getting it wrong cost an hour.

A fifth was held back first, which sounds careful and refuses real work. The
declaration that blocks 2,283 others needs between 3.6 and 4.2 GB of stack:

| allowance | the declaration that blocks 2,283 |
|---|---|
| 3,276 MB, a fifth held back from 4 GB | fails |
| 3,600 MB | fails |
| **4,200 MB** | **passes**, in 25 s |

A reader who writes `REAN_STACK=4096` has said what they meant, and a guard
that keeps a fifth of it back is overruling them. The margin has one job: cover
the work between two entries, which is a walk of a term and not a recursion
through a rule.

### The hour it cost, and the reason

The first reading of that table was "the guard has broken a declaration that
used to pass on the default stack". It had not. **The baseline I compared with
had `REAN_STACK=4096` in it**, four lines up in my own shell history, and I read
it as the default.

> **A measurement is the settings and the number. A number alone is a
> recollection.**

Every table in these sixteen chapters names its settings for that reason, and
the one time I trusted memory instead, memory was wrong by a factor of eight.

It is a **test** on the first line of each of those three functions, and not a
wrapper that takes a closure. The first version was
`self.deeper(|tc| tc.whnf_inner(e))`, which reads better and adds a frame of its
own to every level of a recursion whose depth is the depth of the term. That is
stack spent to measure stack, in the one place where the resource is the thing
being saved.

This also kills the third knob. The first version had `REAN_DEPTH`, and a
reader would have had to learn that it moves with `REAN_STACK`, which moves
with `REAN_FUEL`. Now there are two knobs again, as chapter 9 section 9.8 says,
and the sentence in that chapter about a stack overflow after 4,034
declarations is no longer what happens.

Tests: `a_recursion_past_the_allowance_is_a_verdict_and_not_a_crash`,
`a_generous_allowance_checks_the_same_term`,
`the_message_names_the_knob_that_raises_it`,
`the_budget_is_a_limit_and_a_type_error_is_not`.

The last of those is the one that matters for soundness. Several rules of
`is_def_eq` ask a question that may fail, and a failure there means "this rule
does not apply", not "the declaration is wrong". A limit is the exception: it
has to travel out, or the report blames the wrong cause. `TypeError::is_a_limit`
is that distinction, and it now covers both limits rather than only the budget.

---

## 16.6 The fourth instrument, and the rule it found

Chapters 13 and 15 each wrote a counter, measured, learned something, and
deleted it. Chapter 15 section 15.3 paid for the lesson that an instrument
needs review as much as the kernel does: a counter that watched **one exit of
three** reported a fact about the counter and cost hours.

This is the fourth one, and it stays. `rean_kernel::tally` counts every rule
the kernel fires, by name, and the driver prints it for a declaration that
failed.

```sh
REAN_TALLY=1 rean check one.ndjson
```

```text
  FAIL  theorem    ..ByteArray.utf8DecodeChar?.assemble₄._proof_3
          the kernel used the 409 MiB of stack it is allowed, so it was not checked
          most stack used: 409 MiB
               3276469  units of work charged
                 73582  beta
                 18933  no rule applies
                 12065  iota Nat.rec
                 12024  delta Nat.casesOn
                  6049  proj PProd.0
                  5980  declined read_nat: nested too deep
                  5980  delta Nat.mul.match_1
                  5980  delta Nat.sub._f
                  5964  delta Nat.pow.match_1
                  5964  delta Nat.pred
```

It is kept for the reason chapter 13 found and did not act on: after a certain
point a profiler stops helping. "`whnf` is 41%" is true in every run. `delta
Nat.sub._f` names a cause. The kernel is the only thing that knows which
recursor, which number, which definition, so the kernel counts them. It watches
every exit, it has tests, and it costs one `bool` load per step when it is off.
Tests: `the_tally_names_the_rules_that_fired`,
`a_run_without_the_variable_prints_no_tally`,
`a_tally_that_is_off_counts_nothing_and_builds_no_key`.

### What it said, and the hypothesis it killed in four minutes

Read the row that says `declined read_nat: nested too deep`, 5,980 times,
beside `delta Nat.sub._f`, 5,980 times.

`read_nat` reads a number out of a term, and it forces nested arithmetic at
most sixteen levels deep, because section 15.11 found that descent overflowing
a 32 GB stack. When it declines, the kernel falls back to unfolding the
definition — and that unfold happens **inside the dynamic extent of the
decline**, so `nat_depth` is still at its limit for the whole subtree below it.
One decline at depth sixteen poisons every `read_nat` beneath it. The counts
being equal is that cascade, written down.

The reading is obvious and it is wrong. Lifting the limit was measured:

| `NAT_DEPTH_LIMIT` | the slice that blocks 3,231 |
|---|---|
| 16 | **3.5 s** |
| 1,000,000 | more than 120 s |

More than thirty times worse. The reader walks the tower of successors,
reducing as it goes, and `nat_step` tries it again on every step whose head is a
`Nat` operation. The cap is doing its job. **The cascade is the symptom of the
cure, not of the disease.**

That measurement cost one constant and one run, and it is the third hypothesis
in this project that a measurement retired before a line of it was written.

---

## 16.7 The ceiling was the crash

Chapter 15 ends with a sentence that this chapter has to take back.

> **99.57% is where an eager kernel with four caches gets to.** The last 0.43%
> is not a missing rule, not a budget, and not a cache. It is the
> representation, and changing it is a different project.

Here is the same family, the 68 signed integer lemmas of `Int32`, `Int64` and
`ISize`, in a slice of 16,584 declarations, measured with the stack guard in
place so that nothing can die:

| settings | checked | failed | time |
|---|---|---|---|
| default | 15,664 | 18 | 48 s |
| `REAN_FUEL=2000000000`, 512 MB stack | 15,692 | 14 | 52 s |
| `REAN_FUEL=2000000000`, **8 GB stack** | **16,583** | **1** | 213 s |
| `REAN_FUEL=2000000000`, 16 GB stack | 16,583 | 1 | 237 s |
| `REAN_FUEL=2000000000`, 32 GB stack | 16,583 | 1 | 250 s |

One declaration left in 16,584, and it is the **work budget**, not the stack.

The last three rows are the same answer, so **8 GB is the whole of it**. That
matters for more than tidiness: a 32 GB stack is 32 GB of memory once the
recursion touches it, and a run at 32 GB took this machine from 36 GB of free
memory to 4 GB and had to be stopped. The right stack is the smallest one that
gives the answer, and the way to find it is to ask.

Chapter 15 asked eleven questions of this family and every measurement it made
was sound. The conclusion was not, and the reason is written in its own section
15.11: the runs at four billion units and at sixteen billion **crashed**, in the
same 345 seconds, and a crash that is read as a ceiling becomes a fact about the
kernel in the next chapter. It was a fact about 32 GB of stack and a guard that
did not exist.

The representation is still the reason this work is expensive. Half the profile
is the allocator, and that does not change. But it is **not** what stopped these
declarations, and "the last 0.43% is the representation" was a conclusion drawn
from runs that died before they could answer.

> **A measurement that ends in a crash has not measured the thing you asked
> about. It has measured the crash.**

Chapter 15 said that about one sweep. It is true of a conclusion as well.

---

## 16.8 Where the prelude stands

Lean 4.35.0-rc3, `lean4export` 3.1.0, the whole `Init` closure: 59,349
declarations in 345 MB of NDJSON, exported in 16 seconds.

| settings | checked | failed | blocked | time |
|---|---|---|---|---|
| default, before this chapter | 55,754 | 74 | 3,521 | 259 s |
| default | 55,754 | 74 | 3,521 | **209 s** |
| `REAN_FUEL=2000000000`, 4 GB stack, before the guard | **crashed** after 16,583 | | | 219 s |
| `REAN_FUEL=2000000000`, 512 MB stack | 55,949 | 53 | 3,347 | 461 s |
| **`REAN_FUEL=2000000000 REAN_STACK=8192`** | **59,199** | **45** | **105** | 2,172 s |

**59,199 of 59,349 is 99.75%**, in 36 minutes, with no crash. Chapter 15
reached 99.57% of a smaller prelude in 44 minutes and left 180 declarations
blocked; this leaves 105.

Read the third and fifth rows together. They are the same budget. The
difference between "crashed after 16,583" and "59,199 checked" is a guard that
reports and a stack large enough to say yes.

**Every failure is a limit.** Not one is a rule the kernel is missing.

At the default settings, 71 of the 74 are the work budget, and the other three
are an "unknown constant" that is itself a cascade: `ctor_when_struct` builds
`S.mk` out of the declaration of `S`, so a refused constructor is asked for by a
term that never mentions it and the dependency test cannot see it coming. Those
three are reported as **blocked** now, which is what they are. Test:
`a_constant_we_refused_is_a_block_and_not_a_failure`.

At the patient settings, all 45 that remain are one family and two causes:

| cause | count |
|---|---|
| the 8 GB stack allowance | 40 |
| the work budget of two billion units | 5 |

Every root is `Int32`, `Int64` or `ISize`, and the tail is flat: the worst one
blocks 27.

```text
45 failures block 105 declarations

blocked  root failure
     27  ..SInt.Lemmas.0.ISize.toInt_ofInt_of_le._proof_1_2
     12  ..SInt.Lemmas.0.ISize.le_toInt._proof_1_1
     11  ..SInt.Lemmas.0.Int64.toInt_ofNat_of_lt._proof_1_1
     10  ..SInt.Lemmas.0.Int32.toInt_ofNat_of_lt._proof_1_1
```

The roots at the **default** settings are a different list, and the first line
of it is the whole reason the patient run is worth the 36 minutes:

```text
74 failures block 3521 declarations

blocked  root failure
   3231  ..String.Decode.0.ByteArray.utf8DecodeChar?.assemble₄._proof_3
     57  Lean.Grind.Ring.OfSemiring.mul_helper
     45  ..String.Decode.0.String.utf8EncodeChar_eq_utf8EncodeCharFast._proof_1_12
     28  ..Array.Extract.0.Array.extract_append._proof_1_1
     27  ..SInt.Lemmas.0.ISize.toInt_ofInt_of_le._proof_1_2
```

One declaration blocks 3,231 of the 3,521, which is 92% of them, and
`tools/roots.py` says so in a second. It passes at eighty times the default
budget and a 4 GB stack, in 25 seconds, and 3,231 declarations come with it.

The cost of an **eager** `whnf` that builds a term for every step is still what
makes all of this expensive. It is not what stops it. See section 16.7.

---

## 16.9 What is left, and what it would take

The honest statement of where this project's kernel stands.

- **Nothing in the prelude needs a rule we do not have.** Every failure that
  remains is the budget or the stack, and both are reported as what they are.
- **Both knobs buy real declarations now**, because a run at the far end of
  either one no longer dies.
- **The representation is why this is expensive, not why it stops.** Half the
  profile is the allocator, building and dropping terms that one reduction step
  made and the next discarded. Normalisation by evaluation is the cure that
  chapter 14 named, and section 16.7 is the correction: it would make the work
  cheaper and faster, and it is no longer the thing standing between this
  kernel and the prelude.
- **The five that want budget are reachable.** One of them,
  `WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix`, was asked the
  question directly, and the front door made asking it cheap:

  ```sh
  rean export prelude --decl WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix
  # 759 KB in 1.3s, 206 declarations, instead of 345 MB and 14 seconds
  ```

  | budget | result |
  |---|---|
  | 2,000,000,000 | 205 of 206, in 17 s |
  | **8,000,000,000** | **206 of 206**, in 313 s |

  It is real work, and five minutes of it for one theorem. The method of
  chapters 11 and 12 is now one command, and that is the front door earning
  its place in a performance chapter rather than a usability one.

- **The forty that want stack are not reachable by that knob.** The stack was
  doubled, from 8 GB to 16 GB, and the **same six** declarations failed at the
  point the run was stopped, each having used all 16,320 MB of its allowance.
  Not one of them closed.

  That is the measured case for normalisation by evaluation, and it is a better
  case than "the last 0.43%" because it names the mechanism. These declarations
  need **Rust** stack, because the descent into a major premise is a Rust
  recursion. An evaluator with an explicit stack puts that chain on the heap,
  where a 96 GB machine has room that no thread stack can match. And a thread
  stack has a second cost that the heap does not: a 32 GB stack is 32 GB of
  **memory** once the recursion touches it, which took this machine to 4 GB of
  free memory twice in one evening.
- **Level 2 is still zero.** A `.lean` file reaches our kernel through Lean's
  elaborator, not ours. That is the next island, and it needs the parser of
  chapter 8 with an elaborator behind it.

The front door adds no rule and no stage. What it does is make the project's
own claim checkable by somebody else: point it at your file, and read what our
kernel says about every declaration underneath it.
