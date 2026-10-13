# Chapter 22 — What the others do

> **Where you are.** Chapter 22 of 28, in Part VI of [the guide](README.md). The
> lab notebook. Read it for the method.
>
> **Before this.** [A hundred million](21-a-hundred-million.md).
>
> **After it you can** name the two techniques that make a kernel fast, and say
> why reading another implementation beat another profile.

Thirteen chapters of this project were measurements of our own code. This one
starts somewhere else: **other people have written independent Lean kernels, and
some of them are much faster than Lean's own.**

Reading what they did was worth more per hour than any profile in this project
so far. It also found a rule we had wrong.

```sh
devbox run -- cargo test -p rean_kernel --test substitution
```

---

## 22.1 There is a scoreboard

The [Lean Kernel Arena](https://arena.lean-lang.org/) runs independent checkers
against mathlib, which is far larger than the prelude we use.

| checker | mathlib | the idea |
|---|---|---|
| sokonanoda | 1.4 min | **normalisation by evaluation** |
| mathgraph | 2.2 min | specialised |
| nanoclo | 8.2 min | **delayed instantiation** |
| Lean's own kernel | 32.3 min | — |

Read the last row twice. An independent checker can be **twenty times** faster
than the kernel it is checking against. So when our checker is slow, the answer
is not "a kernel is slow". Somebody else did it faster, and wrote down how.

Two of those write-ups applied to us directly.

---

## 22.2 A rule we had wrong, found by reading a bug report

[nanoda issue 44](https://github.com/ammkrn/nanoda_lib/issues/44) names two
faults in definitional equality. We had the first one.

Our `proof_irrelevant` returned a `bool`. So the caller could not tell these
two situations apart:

- `a` is **not a proof**, so this rule has nothing to say;
- `a` **is** a proof, and the two propositions are **not** equal.

It read both as "the rule did not apply", and carried on — to **unfolding the
two proofs**. No reduction can make two different propositions equal, so every
step of that is waste, and a prelude proof unfolds through structural recursion.
The issue measures the same mistake at 10⁵ to 10⁶ wasted unary steps, which is
the order of chapter 21's hundred million.

Lean's kernel returns a three-valued answer here for exactly this reason. Once
it knows one side is a proof, **the comparison of the two propositions is the
answer**, whichever way it goes.

```rust
match self.proof_irrelevant(a, b) {
    Ok(Some(answer)) => return Ok(answer),   // including false
    Ok(None) => {}                           // not a proof: carry on
    ...
}
```

### What it bought: nothing

54,187 checked and 136 failed, before and after. Our input does not happen to
contain the shape.

It is committed anyway, and that is a different judgement from the `rec.clone()`
change of chapter 20, which measured to nothing and was **reverted**. The
difference is what the change is made of. That one was plumbing: a type and a
copy, with no claim attached. This one is a **rule**, and the kernel now states
it correctly. A rule that is right only on the inputs we happen to own is not
right.

---

## 22.3 The one that paid: delayed instantiation

[nanoclo](https://github.com/sgraf812/nanoclo) states its idea in one sentence,
and the sentence is a bound:

> checking costs O(n) where substituting into the body at each binder costs
> O(n²).

Our β step was the O(n²) version. Here it is:

```rust
let first = *args.first()?;
let reduced = body.instantiate(first);
Some(reduced.apps(args[1..].iter().map(|arg| (*arg).clone())))
```

Take the first argument. Substitute it, which rebuilds every node of the
remaining term that mentions that binder. Leave the rest applied, and come back
for the next one. For a spine of **n** arguments that is n passes over the body.

A proof of the Lean prelude is made of long spines — `Eq.mpr` of `congrArg` of
`Eq.trans`, and recursor rules applied to every field at once. Chapter 21
measured one declaration building **84 million** nodes, and this is where they
went.

### One window, one pass

The n binders occupy a **window** of de Bruijn indices. Inside the window an
index reads one of the values. Above the window an index drops by the whole
width, because all of those binders disappear together.

```rust
Expr::BVar(index) if *index >= depth && *index < top => {
    let slot = (width - 1 - (index - depth)) as usize;
    Some(values[slot].lift(0, depth))
}
Expr::BVar(index) if *index >= top => Some(Expr::BVar(index - width)),
```

The reversal in `slot` is the part to read slowly. `values[0]` belongs to the
**outermost** binder, and index `depth` is the **innermost** one, so the two
orders run opposite ways.

There is a second saving that is easy to miss. A β step throws the binder
**type** away. Peeling n lambdas in one pass never touches those n types, and
the one-at-a-time version rebuilt every one of them on the way past.

### A nearly-right substitution is a soundness bug

This is the one change in this project where a subtle error would not show up as
a slow checker. It would show up as a checker that accepts the wrong thing.

So the old algorithm is still here, as the **reference in a test**, and the two
are compared directly:

```rust
fn one_at_a_time(term: &Expr) -> Option<Expr> { /* the old step */ }
```

Eleven shapes, each chosen because it could hide a different mistake: argument
order, an index above the window, a binder inside the body that lifts each value
as it goes past, a `let` with a binder of its own, fewer arguments than binders,
more arguments than binders, and a twelve-argument spine.

`the_arguments_keep_their_order` exists on its own because a differential test
can miss a reversal: if both algorithms reverse, they agree and both are wrong.
That test names the answer it wants.

---

## 22.4 And then my own last fix was the top frame

With the spine batched, a profile of the prelude said:

```text
whnf        27,360 samples
read_nat    26,860
alpha_eq     4,686
infer_type   2,257
```

`read_nat` is from chapter 21, and it was level with `whnf` itself.

It walks a `Nat.succ` tower, reducing as it goes, and `nat_step` tries it on
**every** step whose head is a `Nat` operation. So the same tower was walked
again, and again, and again.

The case chapter 21 needed was **one layer deep**:
`Nat.succ (OfNat.ofNat Nat 1 ..)`. So read a few layers and give up:

```rust
const SUCC_LIMIT: u32 = 16;
```

Giving up is only slower, never wrong. The kernel falls back to unfolding the
definition, which is what it did before chapter 21 existed.

Same counts, and **252 seconds instead of 317**.

**A fix can become the next bottleneck.** Chapter 21 said that about the trust
report, which was somebody else's code. This time it was the fix from the
chapter before.

---

## 22.5 What is left

| | checked of 57,512 | failed | time |
|---|---|---|---|
| chapter 21 ended at | 48,804 | 536 | 141 s |
| the honest budget, chapter 21 §21.6 | 54,187 | 136 | 291 s |
| a batched β spine | 54,308 | 115 | **252 s** |

And **one declaration blocks 2,690** of the 3,089 that remain, which is 87% of
them. It is `ByteArray.utf8DecodeChar?.assemble₄._proof_3`, a proof about
decoding UTF-8, and it passes at a budget of 800,000,000 in 30 seconds.

So the remaining question is not "can the checker do it" but "at what budget".

---

## 22.6 The budget the last declarations need

One declaration at a time, on its own slice, with `tools/slice.py`:

| declaration | budget it needs | time |
|---|---|---|
| `ByteArray.utf8DecodeChar?.assemble₄._proof_3` | 800,000,000 | 30 s |

That is forty times the default, for one proof about decoding UTF-8. It is also
only thirty seconds, which says the work is **large and cheap per unit** — the
same reading that chapter 21 turned into a thousandfold fix.

The default budget stays at 20,000,000, because a four-minute pass over the
whole prelude is what makes this project workable. `REAN_FUEL` is the knob, and
`REAN_STACK` is its partner: a larger budget reaches deeper terms, and our
`whnf` walks a term by recursion. At 1,000,000,000 the checker overflowed **four
gigabytes** of stack, which is how that coupling announces itself.

---

## 22.7 What we did not take, and the standard we hold it to

The two techniques from §22.1 that we have **not** taken are the answer beyond
the budget:

- **A shift in the representation.** `nanobruijn` keeps a term as a pointer and
  a shift, so lifting is O(1) and one cache entry serves every shifted variant
  of a term. Our cache misses each time the same subterm appears one binder
  deeper, because its indices differ and so does its hash.
- **Normalisation by evaluation**, which is what the fastest checker in the
  arena does.

Both change the representation of a term, which is the one change that would
cost this project its ergonomics. Neither is needed to read the prelude, and
that is the standard this chapter holds them to.

---

## 22.8 How other systems do it

The two techniques of section 22.7 are not new, and neither is from Lean.

- **Normalisation by evaluation.** Instead of rewriting a term into a new term,
  build a value in the host language, with a closure for a function, and read a
  term back out at the end. Every β step then becomes a call in Rust or in
  OCaml rather than a substitution over a tree. Grégoire and Leroy built a
  compiled version of this for Rocq in 2002, and it is what `vm_compute` and
  `native_compute` use there. The fastest checker in the arena uses the same
  idea.
- **Delayed instantiation.** Keep a term as a pointer plus a shift, so a lift
  costs nothing and one cache entry serves every shifted copy. This is an old
  idea from explicit substitution calculi, and `nanobruijn` is the Lean checker
  that applies it.

Three notes for a reader comparing checkers.

- **An independent checker can be faster than the kernel it checks.** That is
  not a scandal. Lean's kernel runs inside a compiler, against a user who
  edits a file, and it must be correct on every path. A checker reads a
  finished file in one pass and can choose a representation that suits only
  that job.
- **The arena is a conformance suite as well as a scoreboard.** It holds files
  that every checker must accept and files that every checker must refuse. A
  fast checker that accepts an invalid proof scores nothing.
- **Reading a bug report is a measurement.** Section 14.2 found a rule we had
  wrong by reading somebody else's issue. That cost an hour and no CPU time at
  all.

## 22.9 References

**Our code**

- `crates/rean_kernel/src/expr.rs`, the batched β step of section 22.3
- `crates/rean_kernel/src/typeck.rs`, the three-valued proof irrelevance
- `crates/rean_kernel/tests/substitution.rs`

**The other checkers**

- The Lean Kernel Arena, the scoreboard and the conformance suite.
  <https://arena.lean-lang.org/>
- The arena repository, for how a checker enters and what it must answer.
  <https://github.com/leanprover/lean-kernel-arena>
- nanoda, in Rust, and its issue 44, which named a rule we had wrong.
  <https://github.com/ammkrn/nanoda_lib> and
  <https://github.com/ammkrn/nanoda_lib/issues/44>
- trepplein, in Scala, the first independent checker.
  <https://github.com/gebner/trepplein>
- lean4lean, in Lean, with a proof about itself.
  <https://github.com/digama0/lean4lean> and <https://arxiv.org/abs/2403.14064>

**Read more**

- Grégoire and Leroy, *A compiled implementation of strong reduction*, 2002,
  for normalisation by evaluation as an implementation.
  <https://xavierleroy.org/publi/strong-reduction.pdf>
- Carneiro, *Lean4Less*, for what each definitional rule costs, measured by
  removing rules. <https://rish987.github.io/files/lean4less.pdf>

---

**Next:** [The last two hundred and forty-eight](23-the-last-two-hundred.md)
