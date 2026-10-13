# Chapter 17 — Twelve seconds

Chapter 16 left the checker at 99.75% of the Lean prelude and a list of 45
failures in one family. This chapter is about the attempt to close them, which
failed, and about the two things it found instead: a command this project should
have had from chapter 0, and a number that changes what "finished" means.

The number is in the title. **Lean's own kernel re-checks the whole prelude in
twelve seconds.** Ours takes 199.

---

## 17.1 Three knobs, and none of them reach, and then a fourth

The 45 that remain split into 40 that run out of stack and 5 that run out of
budget. Chapter 16 showed the budget is reachable: one of the five passes at
four times it. So the question is the 40, and the first move is to try every
knob, because a knob is cheaper than a plan. A fourth one, built in section
17.5 because the first three pointed at it, does not reach either.

| knob | tried | result |
|---|---|---|
| the stack | 8 GB, then 16 GB | the **same six** declarations fail, each having used all of it |
| the work budget | 2 billion, then 8 billion | 8 billion reaches one of the five, and no more |
| the arithmetic reader's depth | 16, 32, 64, 256, none | 32 and 64 are the same as 16. 256 is far slower. None of it runs out of stack. |

The last row is the new one, and it needed a knob that did not exist, so
`REAN_NAT_DEPTH` now holds the depth that [`read_nat`] forces to. It is a
**trade** and both sides of it are measured. Without a cap, the `Nat.pow` and
`Nat.pred` work on the hardest declaration falls by **42 times**, from
2,421,228 steps to 57,344, because the reader reaches the literals and computes
with them. And the declaration that blocks 3,231 others then runs out of stack,
because reaching those literals is a descent and a descent is frames.

So 16 stays the default. It is the value that checks the most declarations, and
the knob is there so that the next reader does not have to rebuild the kernel to
disagree.

[`read_nat`]: https://docs.rs/rean_kernel

---

## 17.2 The command this project should have had first

Every chapter so far asks the reader to imagine the terms. `rean demo` prints a
term that **was built by hand**, and a hand built term is always tidier than a
real one.

```sh
rean show prelude Nat.sub
rean show Demo.lean twice          # half a second, from your own file
```

```text
def Nat.sub

type
  Nat → Nat → Nat

value
  fun (x : Nat) => fun (x1 : Nat) =>
    Nat.brecOn.{1} (fun (x2 : Nat) => Nat → Nat) x1 Nat.sub._f x
```

That is three lines and it teaches more about Lean than a paragraph can.
`Nat.sub` is not a subtraction. It is a **course of values recursion** over a
generated step function, and `Nat.sub._f` is that step function:

```text
def Nat.sub._f

type
  (x : Nat) → Nat.below.{1} (fun (x1 : Nat) => Nat → Nat) x → Nat → Nat
```

It takes the number, a **table** of every earlier answer, and the other
argument. Nobody wrote it. The equation compiler did, and chapter 3 said that is
why checkpoint level 3 compares types and not terms.

For a `.lean` target the name is passed to the exporter as well, so
`rean show Demo.lean twice` exports 759 KB and takes half a second, where the
whole closure of a module that imports the prelude is 345 MB and fourteen
seconds.

Tests: `a_definition_shows_its_type_and_its_value`,
`a_universe_polymorphic_declaration_shows_its_parameters`,
`a_name_that_is_nearly_right_gets_the_nearest_few`,
`show_reads_a_declaration_out_of_a_lean_file`.

---

## 17.3 Two bugs in the first hour

A tool that shows you the data finds bugs in the thing that reads the data.
Both of these had been in the kernel for chapters.

### A name that could not be read back

```text
rean show prelude _private.Init.Data.SInt.Lemmas.0.ISize.toInt_ofInt_of_le._proof_1_2
error: holds no declaration called `...`. Did you mean:
  _private.Init.Data.SInt.Lemmas.0.Int8.sub_le._proof_1_2
```

The name is right. It is in the file. The reader is wrong.

Lean's private names carry a **numeric** part: that `0` is `Name.num 0`, not the
string `"0"`. `Name::from_dotted` made a string part out of every part, so the
name it built was a different name, and no environment holds it.

That is a two line fix and it was not a two line bug. The driver attaches the
axioms of a declaration by looking it up through that very route:

```rust
rests_on.get(&rean_core::Name::from_dotted(&outcome.name))
```

So for **every private declaration of the prelude** the lookup missed and the
trust report said nothing rested on anything. The trust line is the one output
of this checker that a reader is asked to take seriously, and it was quietly
wrong for a third of the file. A test now writes the name out and reads it back.

> **A round trip is a test. Anything that goes to text and comes back needs
> one.**

### A cache that remembered the absence of an answer

`read_nat` returns the number a term is, or nothing. Nothing meant two different
things:

- this term is not a number, and it never will be;
- a limit stopped me, so I do not know.

Only the first is an answer. The second was being written into the cache of
terms that are not numbers, so a term that is a perfectly good number, read once
while the reader happened to be sixteen levels deep, was remembered as **not a
number** for the rest of the declaration. Every later read of it declined at
once, without looking, however shallow the stack had become.

`NatRead` now has three cases and only the answer is cached.

> **A cache may hold an answer. It may not hold the absence of one.**

And a second fault beside it, of the same kind. The depth guard was the **first**
test in the function, before either cache. It is the one exit that remembers
nothing, so a term it declined was asked again on the next reduction step, and
the next. Three lines of `eprintln!` on that path counted it:

```text
5,290,885  DECLINE (Nat.rec.{1} (fun (t : Nat) => PProd.{1,1} ... (Nat.sub._f ...
```

**One term, five million times.** An answer that is already known is known at
any depth, so the caches are asked first now.

Neither fix moved the count by one declaration. Both are kept, because one of
them was reporting a falsehood and the other was a cache telling lies about
terms it had never read.

---

## 17.4 What the hard proof actually asks for

With `rean show` the hardest declaration of the family stops being a mystery:

```text
theorem _private.Init.Data.SInt.Lemmas.0.ISize.toInt_ofInt_of_le._proof_1_2

value
  fun {n : Int} => ... =>
    Lean.Omega.Constraint.not_sat'_of_isImpossible
      (Constraint.mk (some (-2147483648)) (some (-9223372036854775809)))
      (of_decide_eq_true ... (Eq.refl ...))
```

`of_decide_eq_true` is the shape that matters. To accept this proof the kernel
must evaluate

```text
Lean.Omega.Constraint.isImpossible ⟨some (-2147483648), some (-9223372036854775809)⟩
```

and get `true`. That is a comparison of two integers, one about 2³¹ and one
about 2⁶³. With literals it is a single machine instruction. Our kernel instead
reaches `Nat.sub` through `Int.subNatNat`, fails to keep the literal form
somewhere along the way, and counts down through `Nat.sub._f` one `Nat.pred` at
a time. The tally stops at 1,089,527 of those because the stack ran out, not
because the countdown ended.

This is chapter 13 again, through a different door. Chapter 13 found the checker
counting down from a hundred million to answer `Nat.ble`, and fixed it by
reading a number through its constructor form. The same disease, in a place that
cure does not reach.

---

## 17.5 A better limit, built and measured and reverted

Section 17.1 left the arithmetic reader's depth as a trade with no winning
value, and section 17.3's instrument says why that is the wrong knob. **The
kernel declined to read the number zero.** A limit on nesting is global to the
checker, so once it is deep inside one descent, every other read is refused,
however easy.

So count **work** instead of nesting. A read may spend a few hundred units of
the declaration's budget and then give up. A trivial argument costs a handful of
steps and is read at any depth; a pathological one declines, as before; and the
stack guard of chapter 16 catches anything deeper than the machine can hold,
which is the job the nesting count was really doing.

That is a better design. It is also much worse.

| limit on one read | the signed integer slice | time |
|---|---|---|
| **16 levels of nesting** | **16,583 of 16,584** | **205 s** |
| 1,000 units of work | 15,737 of 16,584 | 743 s |
| 200 units of work | 15,681 of 16,584 | 1,125 s |

**Eight hundred declarations and four times the time**, at the better of the two
allowances. A larger allowance is less bad than a smaller one, which is the
clue: more allowance means fewer reads reach the limit at all. The reason is the shape
of the failure, and it is obvious once seen. A read that declines on nesting
costs **nothing**: the guard is one comparison. A read that declines on work has
spent its whole allowance first. The arithmetic of this family is genuinely too
deep to read, so the kernel pays that allowance millions of times over and
declines anyway.

> **When a guard fires often, what it costs to fire matters more than what it
> measures.**

Reverted, and the measurement is the part worth keeping. One half of it stays: a
term that is **already** a numeral is now read before the guard, at no cost,
because declining to read a literal is absurd whatever the limit is. It buys
nothing measurable on this declaration, and it is still right.

### My instrument lied about which exit, again

The table in section 17.3 names three terms that the kernel refused. One of them
is the literal `0`, and the fast path above was written for it. The declines did
not move by one.

The instrument printed **both** arguments of the operation, without saying which
one had failed. The literal was the innocent one standing next to the guilty
one. Chapter 15, section 15.3, has the same lesson from the other direction: an
instrument that watches one exit of three reports a fact about the instrument.
This one watched both arguments and named neither.

> **An instrument must say which exit it saw, not which exits exist.**

---

## 17.6 Twelve seconds

Three of the independent checkers that chapter 14 read about are installed on
this machine beside the Lean that made the export. One of them is Lean's own
kernel.

```sh
leanchecker --verbose Init
```

```text
replaying Init
replaying Init.SimpLemmas
replaying Init.Hints
...
```

It replays every module of the prelude and re-checks every declaration with
Lean's kernel. **It finishes in twelve seconds**, and it checks the ones we
cannot check at all.

| checker | the whole prelude |
|---|---|
| Lean's own kernel, `leanchecker` | **12 s**, all of it |
| rean, default | 199 s, 55,754 of 59,349 |
| rean, `REAN_FUEL=2000000000 REAN_STACK=8192` | 2,172 s, 59,199 of 59,349 |

Read the first row twice. It is not a scolding, it is a **gift**. Fifteen
chapters of this project measured against itself, and a conclusion drawn that
way can only ever say "faster than last week". Chapter 16 had to take back
chapter 15's conclusion for exactly that reason. Now there is an oracle for
speed, on this machine, over the same input, and it is 16 times faster than our
default run while failing nothing.

That reframes every remaining question. "The last 45 declarations need a
different representation" is no longer a safe thing to say, because something on
this machine checks them in the time our kernel takes to read the file. Whatever
it does, it is a mechanism, and a mechanism can be found.

> **Measure against something that is not yourself. A project that only
> measures against its own last week can only learn that it is improving.**

---

## 17.7 What else can it check?

Sixteen chapters measured one library: `Init`, the prelude. The toolchain ships
two more, and the front door makes trying them a command each.

```sh
rean check Std      # 536 MB of NDJSON, exported in 22 s
rean check Lean     # the compiler itself, 708 MB, exported in 30 s
```

The first attempt did not finish. `Std` reached 23,699 declarations of 99,619
and **stopped**, twice, at exactly the same one:
`Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q`.
Not a crash and not the budget. `rean show` said why in one line:

```text
2617556290 nodes in the value, counted as a tree
```

**Two and a half billion nodes.** A term is a graph, because `Arc` shares every
subterm, and that lemma is a few hundred thousand nodes as a graph. Two of our
walks did not know the difference.

- `collect_constants` walked the tree. The driver asks what a declaration rests
  on **before** the kernel sees it, so every run paid it. A visited set keyed by
  the address of the shared node makes it a graph walk: two minutes became
  **1.06 seconds**.
- `infer_type` walked the tree **and was charged one unit for it**. To type an
  application the kernel instantiates the function's `Forall` body, and that
  rebuild happens in one call with no reduction step to charge for it. Seven
  minutes inside a twenty million unit budget, and then the operating system
  killed the process for its memory. The size is cached in every node, so the
  kernel now charges for the walk **before** making it: seven minutes and a
  process kill became **15 seconds and a verdict**.

> **A budget that bounds neither time nor memory bounds nothing.**

With those two, all three libraries run to completion:

| library | declarations | checked | failed | time |
|---|---|---|---|---|
| `Init`, the prelude | 59,349 | 55,835 | 72 | 231 s |
| `Std` | 99,619 | **95,237** | 120 | 330 s |
| `Lean`, the compiler | 171,817 | **150,420** | 127 | 367 s |

Three hundred and thirty thousand declarations, no crash, about fifteen minutes
for all three. That is the first time this project has read anything but the
prelude.

### Five declarations that we refuse and Lean accepts

Every failure of `Init` and of `Std` is a limit. `Lean` has 122 of those and
**five of another kind**:

```text
Lean.Elab.Term.Do.Code._sizeOf_4_eq
Lean.Elab.Term.Do.Code._sizeOf_5_eq
Lean.Meta.DiscrTree.Trie._sizeOf_3_eq
Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_17_eq
Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_18_eq
```

They report a **type mismatch**, which means our kernel says no where Lean says
yes. The shape is the same in all five:

```text
Nat.add (1 + sizeOf head) (Trie._sizeOf_3 tail)
Nat.add (1 + sizeOf head) (sizeOf tail)
```

The kernel cannot see that a generated `_sizeOf_N` equals the `SizeOf` instance
it was generated from. Every one of those three types is a **nested** inductive:
`Do.Code` holds an array of itself, `Trie` holds an array of pairs of itself,
and so does `EqCnstr`.

That is where chapter 7, section 7.1, said the weakness was:

> Every group check would fire on a correct declaration. So a nested recursor is
> now **trusted**, and that is the one place the checker still takes a recursor
> on faith.

The roadmap has been asking for a mutual fixture to validate that ordering. It
can stop asking. There are five counterexamples in the Lean compiler, with
names, and a counterexample beats a fixture.

> **Run it on something you did not choose.** Sixteen chapters of one library
> found every kind of fault except the kind that one library does not have.

---

## 17.8 So how do we get to 100%

Ranked by what the measurements support, and each one is a measurement before
it is a plan.

1. **A differential harness.** Run `leanchecker` and `rean` over the same
   slice, and compare **per declaration**. The method of chapters 11 and 12,
   with an oracle that is not us: take the declaration whose ratio is worst,
   and ask what Lean does that we do not. This is the cheapest item on the list
   and the only one that can answer a question the project cannot currently
   ask.
2. **Keep the literal form.** Section 17.4 says the kernel loses the literal
   somewhere between `Int.subNatNat` and `Nat.sub`. One declaration, one
   instrument on `nat_step`, and the place where a literal becomes a `brecOn`
   will name itself. If Lean has a kernel rule we lack, this is where it shows.
3. **An evaluator with an explicit stack.** The 40 that run out of stack need
   it: they need **Rust** stack today because the descent into a major premise
   is a Rust recursion. On the heap, a 96 GB machine has room that no thread
   stack can match. This is the rewrite chapter 14 named, and section 16.9 gives
   it a mechanism rather than a percentage.
4. **Pointer identity before hashing.** Lean's kernel asks "same pointer?"
   first and ours asks for a hash and then `alpha_eq`. Chapter 10's rule stands
   either way, because a pointer that is equal is a term that is equal.
   Unmeasured, and cheap to measure.
5. **A number library.** Not yet. The instrument counts how often the
   arithmetic overflows a `u128`, and on these declarations the count is
   **zero**. `nat_lit.rs` names this limit in its own first paragraph, and it is
   still not the one being paid.

**The list has a new first item.** Those five rejections are a rule the kernel
is missing, not a limit, and they are the only such thing found in 330,785
declarations. A rule gap outranks every performance item on this list, because
a checker that refuses a correct declaration is wrong in the direction that
matters least and is still wrong.

What this chapter does **not** recommend is another sweep. Four knobs were
swept here, one of them was rebuilt as a better knob first, and the best of
them bought one declaration out of 45.

And one number that did move, on the whole prelude at the default settings:
**74 failures became 71**, because the three that said "unknown constant" were
cascades from a refused constructor and are now reported as blocked. The count
of checked declarations is unchanged at 55,754 and the time fell from 209
seconds to 199. Three phantoms off the list that `tools/roots.py` ranks is worth
more than it sounds: a reader who chases a phantom finds nothing, and concludes
the tool is lying.
