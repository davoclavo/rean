# Chapter 12 — Ask the cheapest question first

Chapter 11 moved one call and took 455 failures away. It also left an
instruction: do the same thing again. Take **one** of the remaining failures,
cut its slice, sweep the budget, and let the number say what the fix is.

This chapter follows that instruction twice. The first answer was "no", and
that is the more useful half.

```sh
devbox run -- cargo test -p rean_kernel --test comparison
devbox run -- cargo test -p rean_kernel --test cache
```

---

## 12.1 The method said no

`Nat.mul_add_div._f` is the first of the 221 that remained. `tools/slice.py`
cuts it out, its slice holds 1,172 declarations, and the sweep looked nothing
like the one in chapter 11:

| budget | result | time for the slice |
|---|---|---|
| 20,000,000 | failed | 0 s |
| 2,000,000,000 | failed | 6 s |
| 20,000,000,000 | failed | 58 s |

More than **twenty billion** units and still no answer. In chapter 11 the sweep
found a declaration that wanted 500 million and spent them in a second. This
one is a different animal, and a bigger budget is not its fix.

So the next question is where the work goes, and the profile answers it with one
stack rather than a list:

```text
check_declaration -> infer_type -> is_def_eq -> spine_eq -> whnf -> iota_step
```

Every frame carries the same sample count, which means they are all on the stack
at once. Read it from the right: ι is reducing, inside a `whnf`, of an argument
that `spine_eq` is comparing.

**The heads already match.** The quick comparison of chapter 11 is working, and
the cost is in one argument that genuinely needs reduction.

That rules out the fix the roadmap had named next. Lean's **lazy δ by height**
unfolds only the taller of two **different** constant heads. Here the heads are
the same, so the rule has nothing to do.

A plan survives until a measurement meets it. This is the second plan this
project has retired without writing a line of it.

---

## 12.2 Reading the declaration, not guessing at it

So ask Lean what the declaration is.

```sh
echo '#print Nat.mul_add_div._f' > /tmp/q.lean
devbox run -- lean /tmp/q.lean
```

The answer is a proof, and its shape is the clue:

```lean
Eq.mpr (id (congrArg (fun _a => (_a + y) / m = x + 1 + y / m) (Nat.mul_succ m x)))
  (Eq.mpr (id (congrArg ... (Nat.add_assoc (m * x) m y)))
    (Eq.mpr (id (congrArg ... (x_1.1 (m + y))))
      (of_eq_true (Eq.trans ...))))
```

`Eq.mpr`, `id`, `congrArg`, `of_eq_true`, `Eq.trans`. Every one of those is a
**proof**, and every one of their arguments is a proof.

And the kernel never has to look at a proof. Two proofs of one proposition are
equal. That is **proof irrelevance**, and the checker has had it since chapter 2.

It was the **last** rule it tried.

---

## 12.3 Where proof irrelevance belongs

Here is the order `is_def_eq` used, written as the questions it asks:

1. Are these the same term? `alpha_eq`.
2. Same head, equal arguments? `spine_eq`. Chapter 11 moved this one up.
3. *Reduce both sides.*
4. Same literal, same sort, two binders, same spine, η, η for a structure, one
   term type.
5. **Do both sides prove the same proposition?**

Question 5 does not look at either term. It reads two types and compares them.
For a proof it is almost always the answer, and it sat behind a reduction that
can drag in the whole computation the proof speaks about.

So it moves to the front, before any reduction:

```rust
match self.proof_irrelevant(a, b) {
    Ok(true) => return Ok(true),
    Ok(false) => {}
    Err(error @ TypeError::OutOfFuel(_)) => return Err(error),
    Err(_) => {}
}
```

### Why two of those arms are not laziness

`proof_irrelevant` asks for a type, and asking can fail. At the end of the list
a failure was the final answer anyway. At the **front** of the list it is not:
the rule simply did not apply, and the rules below it still deserve their turn.

But one error must **not** be swallowed. If the budget ran out, that is the
truth about the declaration, and hiding it would make the report blame a type
mismatch for a cost problem. Chapter 10 §10.8 is the same lesson, and it was
expensive enough to learn once.

Tests: `two_proofs_of_one_proposition_need_no_reduction`, and the control
`two_terms_of_one_type_are_not_equal_for_free`, which gives the same shapes a
`Type` instead of a `Prop`. The two sides are genuinely different terms, so the
pair answers `true` in `Prop` and `false` in `Type`, and that difference is
exactly what proof irrelevance is.

That control used to assert a **budget exhaustion** instead, and chapter 15
§15.10 records why that was wrong: the terms it compared were equal all along,
and only an eager reduction made finding it expensive. A test that measures the
cost of a detour is a test that passes for the wrong reason.

---

## 12.4 The move alone made things worse

| | checked | failed | blocked |
|---|---|---|---|
| chapter 11 ended at | 39,066 | 229 | 18,217 |
| proof irrelevance first | 38,972 | **114** | 18,426 |

Failures **halved**, and 94 fewer declarations were checked.

Both are true, and the second is what matters. Chapter 10 §10.5 warned about
exactly this: a failure count alone can be improved by attempting less.

So: which declarations stopped passing? The answer was 227 of them, and every
one was now **blocked** rather than failed. Two new failures stood upstream of
all 227:

```text
FAIL  theorem  Std.IterM.DefaultConsumers.forIn'_eq_match_step
          this declaration needed more than 20000000 units of work
```

Both ran out of budget. Proof irrelevance is not free: it infers the type of
both sides. When it declines, that cost is spent for nothing, and for those two
declarations it was the cost that broke them.

**One root failure blocked 227 leaves.** That is the leverage this project keeps
meeting, and it is why the two counts have to be read together.

---

## 12.5 The fourth cache pays for the third rule

The waste is plain once named: `infer_type` now runs on both sides of every
comparison, and it ran from nothing every time. One term is typed many times
inside one declaration, and its type does not change there.

So the same pattern as chapter 10, a fourth time: a cache keyed by the cached
hash, confirmed with `alpha_eq`, cleared for each declaration and around each
mutual group.

With one exception, and it is a small lesson of its own:

```rust
if matches!(e, Expr::BVar(_) | Expr::FVar(_) | Expr::MVar(_)
              | Expr::Sort(_) | Expr::Lit(_)) {
    return self.infer_type_uncached(e);
}
```

A leaf is cheaper to type than to look up. A `Sort` needs one `succ`, and a free
variable is one read of the context. Caching those would cost a hash and a
probe to save nothing — the same reasoning as `CACHE_MIN_SIZE` in chapter 10.

For the free variable there is a second reason to like it. Its type comes from
the context that holds it, so leaving it out of the cache removes the one entry
whose answer is not a function of the term alone.

Tests: `a_type_is_inferred_once_and_read_after_that`,
`a_free_variable_is_typed_from_the_context_and_not_the_cache`.

---

## 12.6 Together, not separately

| | checked | failed | blocked | time |
|---|---|---|---|---|
| chapter 11 ended at | 39,066 | 229 | 18,217 | 205 s |
| proof irrelevance first | 38,972 | 114 | 18,426 | 203 s |
| and the `infer_type` cache | **39,244** | **115** | 18,153 | **192 s** |

The last row beats the first on every column. And **no declaration that passed
before stopped passing**: 178 newly pass, 0 regressed.

Neither change is good on its own terms alone. The rule without the cache loses
178 declarations to a cost it introduced. The cache without the rule has much
less to cache, because nothing was asking for types that often. **The pair is
the unit of work, and so the pair is the unit of measurement.**

---

## 12.7 Where the kernel stands

| | checked of 57,512 | failed | time |
|---|---|---|---|
| start of chapter 9 | 33,539 | 742 | 198 s |
| now | **39,244** | **115** | **192 s** |

And the 115, by kind:

| kind | count |
|---|---|
| out of budget | 107 |
| unknown constant, from one rejected constructor | 8 |

Seven axioms, by name, unchanged throughout: `Classical.choice`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Quot.sound`,
`propext`, `sorryAx`.

**No declaration on this input fails for a rule the kernel lacks.** Everything
that remains is cost.

---

## 12.8 Which failure to work on next

**107 declarations out of budget**, and 18,153 blocked behind them. So the next
question is not "what is wrong" but **"which one of the 107 is worth the
trouble"**.

A blocked declaration is not wrong. It waits on something, and the report says
what:

```text
block def   instAppendString
              `String.append` did not check
```

Follow every chain to its end and count the leaves that each root holds up.
`tools/roots.py` does it:

```sh
./target/release/rean check full.ndjson > report.txt
python3 tools/roots.py report.txt
```

```text
115 failures block 18153 declarations

blocked  root failure
  15272  _private.Init.Prelude.0.isValidChar_UInt32
   1810  Nat.mul_add_div._f
    323  Lean.Grind.CommRing.Mon.revlexWF._unary._proof_2
    221  Char.utf8Size._proof_2
```

**One declaration holds up 15,272 of the 18,153.** That is 84% of everything
the checker did not read, behind a single private theorem of `Init.Prelude`
about whether a number is a valid character.

Had I worked down the failure list in order, that one is ninth. The first eight
are worth 1,810, 323, 221, and then rows of fifty. **Rank before you choose.**

---

## 12.9 And the budget is no longer the lever

Two measurements, on the same binary, say where the limit now is.

| budget | checked | failed | time |
|---|---|---|---|
| 20,000,000 | 39,244 | 115 | 192 s |
| 100,000,000 | 39,318 | 103 | 354 s |

Five times the budget buys **74 declarations**. Before the two reorderings of
chapters 11 and 12, five times the budget bought 1,094. The checker is no longer
budget-bound on this input; it is work-bound, and the work is real.

The one high-leverage declaration shows it exactly. On its slice,
`isValidChar_UInt32` fails at 2,000,000,000 and **passes at
20,000,000,000** — somewhere between two and twenty **billion** units for a
theorem that Lean checks without noticing. The profile of that run is one stack:

```text
infer_type (13 deep) -> is_def_eq -> spine_eq -> is_def_eq
                     -> whnf -> iota_step -> whnf -> iota_step -> whnf
                     -> beta_step -> instantiate -> drop
```

Nested ι, each step doing a β and a substitution, and then dropping the term it
built. That is not a missing shortcut. That is the eager shape of our `whnf`.

### One guess, measured and reverted

`iota_step` began with `rec.clone()`, which copies **every rule** of the
recursor, and a rule holds a term. ι runs on most steps of this workload, and
`drop_slow` was the heaviest frame that is not a stack frame. The story fits.

So I read only the shape of the recursor first, and cloned the one rule that
fires once it was known. The result:

| | 2 G budget | 20 G budget |
|---|---|---|
| before | 1,896 in 15 s | 1,897 in 103 s |
| after | 1,896 in 15 s | 1,897 in 103 s |

**Nothing.** Not one second, not one declaration. The story fitted and was
wrong, so the change is not in the tree: a new type for an unmeasurable gain is
a cost with no payment. The profile pointed at the drop of terms that
**reduction** builds, not at the drop of rules that the lookup copies.

This is the third plan this project has retired by measuring it, and the
cheapest of the three to retire.

---

## 12.10 What is left, honestly

One thing, and it is the job that chapters 10 and 11 both named and both
deferred.

Our `whnf` is **eager**. Each step builds a whole new term and drops the old
one, and the profile has said so under four different changes now. Lean's `whnf`
rebuilds nothing. That is a change to every rule, and it is the right size of
job to do on its own.

What would make it worth starting: the ranking above. One declaration is worth
15,272, and it is the same shape of work as the next three. Four fixes could be
worth 17,600 declarations, which is nearly everything that remains.

And the discipline these two chapters earned, stated once more, because it has
now worked three times and failed none:

1. Rank the failures by what they block. Work on the longest row.
2. Take that one declaration alone. `tools/slice.py` cuts it out.
3. Sweep `REAN_FUEL`. Passes at a larger budget in a second: the budget was the
   fault. Wants twenty billion units: the kernel is.
4. Profile, and read the **stack**, not the list of symbols.
5. Then change one thing and measure. A story that fits is not evidence.
