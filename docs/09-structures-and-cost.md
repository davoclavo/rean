# Chapter 9 — Structures, and what the kernel costs

Chapter 7 closed the last soundness gap we could name. This chapter answers a
different question: **the prelude of Lean is 57,512 declarations, so what stops
a checker from reading all of them?**

Two things stop it, and they are not the same kind of thing.

1. Rules the kernel does not have. The checker then **refuses correct Lean**.
2. Work the kernel does too slowly. The checker then **runs out of budget**.

The first is a hole in the theory. The second is a hole in the engineering. This
chapter finds three of the first and two of the second.

```sh
devbox run -- cargo test -p rean_kernel --test structures
```

---

## 9.1 A structure is an inductive type with one constructor and no index

Lean writes

```lean
structure ByteArray where
  mk :: data : Array UInt8
```

and that is not a new kind of declaration. It is an inductive type with one
constructor. The word **structure** names a shape, not a feature:

- exactly **one** constructor,
- **no** index,
- and, for the rules below, **no recursion**.

That shape has a consequence the kernel can use. If `x : ByteArray`, then `x`
holds one field and nothing else, so

```text
x  ≡  ByteArray.mk x.0
```

for **every** `x`, even a variable whose value nobody knows. The term on the
right is built from `x` itself, so the equation says nothing new about the
world. It only writes `x` in a different shape.

Three rules of the kernel are that one equation, read in three directions.

---

## 9.2 Rule one: η for a structure, in a comparison

The checker had this rule already. If one side is a constructor application and
the other is anything of the same type, compare field by field:

```text
S.mk p.0 p.1   ≡   p
```

`struct_eta_eq` does it. The rule needs **one side to be a constructor
already**, and that turns out to be the limit worth naming.

---

## 9.3 Rule two: η for a structure, on a major premise

The ι rule needs its major premise in constructor form. A variable is not in
constructor form, so the rule declines, and a reduction that Lean performs we do
not.

The prelude showed exactly that. `List.toList_data_toByteArray` failed with

```text
expected: ByteArray.data (ByteArray.push _f14 _f12)
got     : Array.push    (ByteArray.data _f14) _f12
```

Read the two sides. They differ in one place: on the left, `ByteArray.push` has
not reduced. It cannot, because `push` takes its argument apart with `⟨bs⟩`, and
`_f14` is a free variable.

So before ι gives up, rebuild the major premise:

```text
_f14  ~>  ByteArray.mk _f14.0
```

Now `push` matches, ι fires, the projection of the constructor takes the field,
and both sides reach `Array.push (ByteArray.data _f14) _f12`.

`ctor_when_struct` is the rule. Three conditions keep it sound, and Lean checks
the same three:

| Condition | What goes wrong without it |
|---|---|
| one constructor | the term could be either one, so the rebuilt term is a guess |
| no index | an index can differ between `x` and the rebuilt term, so the two need not even have the same type |
| not recursive | a field of the type itself makes the rebuilt term grow with no end |

`Eq` is the example for the second row, and it is why `Eq.rec` needs the
separate **K** rule and not this one.

Tests: `iota_fires_on_a_variable_of_a_structure`, and one negative test per row
of that table.

### What this rule cost, measured

| | failures of kind "type mismatch" |
|---|---|
| before | 168 |
| after | **9** |

One rule, 159 declarations. Every one of them was a **false refusal**: correct
Lean that our checker rejected because it lacked a reduction.

---

## 9.4 Rule three: a type with one term

`Unit.ext` of the prelude says

```lean
theorem Unit.ext (a b : Unit) : a = b
```

and its proof is `rfl`. So the kernel must find `a ≡ b` for two variables.

Rule two cannot help: neither side is a constructor. Rule one cannot help for
the same reason. But `Unit` is a structure whose constructor has **no field**,
so it has exactly one term, and

```text
a  ≡  ⟨⟩  ≡  b
```

`unit_like_eq` is the rule: if both sides have the same type, and that type is a
structure whose constructor carries nothing, the two sides are equal.

The words "the same type" are the whole safety of it. Without that test the rule
would equate a term of one one-term type with a term of another.

Tests: `two_terms_of_a_one_term_type_are_equal`,
`two_terms_of_a_type_with_a_field_are_not_equal`,
`two_terms_of_two_one_term_types_are_not_equal`.

---

## 9.5 A string literal is a structure too

`String` in Lean 4.30 is

```lean
structure String where
  ofByteArray :: (toByteArray : ByteArray) (isValidUTF8 : toByteArray.IsValidUTF8)
```

The kernel stores `"ab"` as a literal and never writes that pair out. So a
projection of a literal has to produce the field:

```text
"ab".toByteArray  ~>  ByteArray.mk (Array.mk [UInt8.ofNat 97, UInt8.ofNat 98])
```

Two points are easy to get wrong, and we got the first one wrong first.

1. **The field is bytes, not characters.** An older Lean held a `List Char`. This
   one holds UTF-8 bytes. `é` is one character and **two** bytes. A Rust `str`
   is UTF-8 already, so its bytes are the ones Lean means.
2. **The second field needs no rule.** It is a proof, and proof irrelevance
   makes any two proofs of it equal, so the projection may stay a projection.

Tests: `the_first_field_of_a_string_literal_is_its_byte_array`,
`the_bytes_are_utf8_and_not_code_points`,
`the_second_field_of_a_string_literal_stays_a_projection`.

How we found the shape: we asked the real Lean.

```sh
echo '#print String' > /tmp/q.lean
devbox run -- lean /tmp/q.lean
```

A guess from memory gave `String.mk` and a `List Char`, and the checker then
reported `unknown constant String.mk`. The lesson is the one chapter 3 already
states: **read the ground truth, do not recall it**.

---

## 9.6 The engineering half: what the kernel caches

A profile of the prelude named one frame above all others:

```text
instantiate_at   41,436 samples
lift_opt          4,790 samples
```

Substitution dominated. The reason is that `instantiate_at` walked a whole
subterm to discover that **nothing in it changed**. A closed subterm has no
bound variable pointing out of it, so substitution cannot touch it, and the walk
learns nothing.

So cache the one fact that decides it. Every subterm now carries

```rust
pub struct Sub {
    expr: Arc<Expr>,
    loose: u32,
    size: u32,
}
```

`loose` is one more than the largest **loose** bound variable index inside, or
zero when there is none. Each node computes it from its children in constant
time, so building a term pays O(1) per node:

```rust
Expr::App { fun, arg } => fun.loose.max(arg.loose),
Expr::Lam { binder_type, body, .. } =>
    binder_type.loose.max(body.loose.saturating_sub(1)),
```

The `saturating_sub(1)` is the whole idea of de Bruijn indices in one line.
Going under a binder discharges index 0, so the body's range drops by one.

Then substitution asks instead of walks:

```rust
fn instantiate_at(&self, depth: u32, value: &Expr) -> Option<Sub> {
    if self.settled_at(depth) { return None; }   // loose <= depth
    ...
}
```

The real Lean kernel stores the same number in every expression header. We now
know why.

### The second cache, which the first one revealed

With substitution fixed, a new frame surfaced:

```text
Expr::size_up_to::walk   6,845 samples
```

That is **our own accounting**. The checker charges fuel by the size of the term
each reduction produced, so it asks for that size after every single step, and
the answer was a walk of the term. The accounting cost as much as the work it
accounted for.

`size` is the same trick, so `size_up_to` is now a lookup and a clamp.

| | time for the prelude |
|---|---|
| before both caches | 198 s |
| `loose` cached | 181 s |
| `size` cached too | **160 s** |

---

## 9.7 The lesson that cost the most

The `loose` cache did not change the number of declarations we checked. Not one.

| budget | checked | time |
|---|---|---|
| 20,000,000 | 33,539 | 198 s → 160 s |

The reason is that the budget is charged by **work**, and the caches do not make
the work smaller. They make the same work faster. A declaration that needed more
than 20,000,000 units of work still needs it.

So the honest reading of a performance change has two questions, not one:

1. Did the frame I aimed at go away? For `instantiate_at`, yes.
2. Did the number I care about move? No.

Both answers are useful, and reporting only the first would have been a lie.

---

## 9.8 Raising the budget found a third bug

If the caches bought time, spend it: raise the budget. At 100,000,000 the
checker died after 40 seconds with

```text
thread 'main' has overflowed its stack
```

Not a budget. Not memory. **The stack.** The kernel walks a term by recursion,
so the depth of the Rust stack follows the depth of the term, and a term that a
reduction built can be very deep. A main thread gets 8 MB, which is not enough.

The fix is four lines, and `rustc` solves the same problem the same way:

```rust
let child = std::thread::Builder::new()
    .stack_size(stack_bytes(std::env::var("REAN_STACK").ok().as_deref()))
    .spawn(run)
    .expect("the main thread must start");
```

512 MB is the default, and it is **not** a number that holds for every budget.
The two limits are coupled: a larger budget lets a reduction run longer, a
longer reduction builds a deeper term, and a deeper term needs more stack. At a
thousand times the default budget this stack overflowed after 4,034
declarations, so the size is a knob, `REAN_STACK`, in MiB. `rean help` names
both knobs and says they are coupled, because a reader who raises one and then
meets the other has been failed by the text.

Tests: `the_stack_size_reads_a_number_of_mebibytes`,
`a_stack_size_nobody_wrote_is_the_default`,
`the_usage_text_names_both_knobs_and_their_coupling`.

Note what the first budget sweep reported before this fix: "did not finish". A
timeout and a crash look the same from outside, and we read it as the first for
one whole measurement. **Read the exit code and the stderr, not the clock.**

---

## 9.9 A new rule has a cost, and the profile named it

The three rules bought 159 declarations and **lost 25 seconds**: 160 s became
185 s. The profile said why in one line.

```text
infer_type   29,569 samples
drop_slow    11,678
is_def_eq     9,001
```

`ctor_when_struct` reads the **type** of the major premise, and it ran on every
recursor application in the prelude. Most of those are over `Nat` or `List`,
which are no structures, so the answer was almost always "no" and the cost of
asking was a full `infer_type`.

The fix is to ask a cheap question first:

```rust
if !rec.all.iter().any(|name| self.structure_params(name).is_some()) {
    return Ok(None);
}
```

That test reads one declaration out of the environment. It does not infer
anything. `infer_type` fell from 29,569 samples to 8,126, and the prelude went
from 185 s to 171 s.

**Put the cheap test before the expensive one, and let the profile tell you
which is which.**

---

## 9.10 The kernel asked a question by building a string

With `infer_type` down, a frame appeared that is not a rule at all:

```text
rean_core::Name   2,196 samples
```

`Name` is a list of parts. The readable way to ask whether a name is `Nat.add`
was

```rust
match name.to_string().as_str() {
    "Nat.add" => ...,
```

and `whnf` asks that on nearly every step whose head is a constant, which is
most steps. Each ask built a `String`, compared it, and dropped it.

`Name::two_parts` answers the same question with no allocation, by comparing two
string slices that already exist:

```rust
let ("Nat", op) = name.two_parts()? else { return None };
match op {
    "add" => number(a.checked_add(b)?),
```

171 s became 163 s. The reading is the same every time: **the kernel is a loop,
so anything inside it that allocates is worth looking at.**

---

## 9.11 Where the prelude stands

| | checked | failed | blocked | time |
|---|---|---|---|---|
| start of this chapter | 33,539 | 742 | 23,231 | 198 s |
| after everything here | **33,862** | **650** | 23,000 | **163 s** |

And the failures, by kind:

| kind | before | after |
|---|---|---|
| out of budget | 565 | 642 |
| type mismatch | 168 | **0** |
| not a structure | 9 | **0** |
| unknown constant | 0 | 8 |

Read the middle rows first. **Every type mismatch is gone, and so is every
"not a structure".** On this input the checker no longer refuses correct Lean
for a rule it does not have.

Read the first row next, and do not read it as a regression. Those 77
declarations did not get worse. They used to fail **earlier**, for a missing
rule; now they get past that rule and reach the budget instead. Progress moves a
declaration from one failure to a later one before it removes it.

The last row is the same 8 declarations that used to say "not a structure", and
they are not a kernel gap. All 8 are one cascade: a constructor that the checker
rejected never entered the environment, so a later projection could not find it.
The old message sent the reader after the wrong fault. The checker now says what
is true:

```text
unknown constant `String.Slice.Pos.Splits.mk`
```

Tests: `a_missing_constructor_is_named_as_missing`,
`both_rules_decline_when_the_constructor_is_missing`.

---

## 9.12 A bigger budget, measured

The budget is a real knob, and `REAN_FUEL` exposes it.

| budget | checked | failed | blocked | time |
|---|---|---|---|---|
| 20,000,000 | 33,862 | 650 | 23,000 | 163 s |
| 100,000,000 | 34,629 | 647 | 22,236 | 477 s |

Five times the budget bought **three** fewer failures, and **767** more
declarations checked. That ratio is the lesson.

A failed declaration blocks every declaration that depends on it, and the
blocked ones are not wrong, only unread. So three root fixes released 764
leaves. The leverage of one hard declaration is enormous, and it means the right
place to look is always the **first** failure in the chain, never the last.

Our own report helps with that, because it names what each blocked declaration
waited for:

```text
block def   instAppendString
              `String.append` did not check
```

Follow that chain far enough and it ends at one real failure. For the whole
`String.append` tower of the prelude, it ended at
`List.toList_data_toByteArray`, and that one declaration is what §9.3 fixed.

---

## 9.13 What is left, and it is one thing

**642 declarations out of budget.** That is the whole remaining gap on this
input, and the cause is **well-founded recursion**. `WellFounded.fix` unfolds
through `Acc.rec`, each step grows the term, and the growth is what the budget
measures.

A bigger budget is not the honest fix, as §9.12 shows: five times the number
bought three declarations. The honest fix is the cache the real kernel has and
we do not.

The profile now says where it would go:

```text
drop_slow    9,677     dropping terms a reduction built and discarded
whnf         8,606
iota_step    8,107
infer_type   8,126
is_def_eq    6,123
```

`drop_slow` at the top means the checker spends its time **building terms and
throwing them away**. Every one of those frames is the same shape of waste: the
checker reduces a subterm, compares it, drops it, and later reduces the same
subterm again from scratch.

So the next step is a **cache on `whnf`**, and after it one on `is_def_eq`. Lean
has both. Caching needs a third number in every node, a structural hash, which
is exactly the pattern of §9.6 for a third time. And it needs one discipline the
first two caches did not: a cached answer must be **confirmed**, not trusted,
because two different terms can share a hash. A proof checker may not be
probably right.

That is the next chapter.
