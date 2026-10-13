# Ground truth fixtures

These files come from the real Lean. They are the checkpoint that our own
pipeline must meet. See `docs/ROADMAP.md`.

## How to generate a new fixture, now

`rean export` does every step of this page for you. See
[chapter 24](../../docs/24-the-front-door.md).

```sh
# a module, or one declaration and its closure
cargo run --release -p rean -- export Probe.lean --decl Tree --decl Forest --out fixtures/lean4export
```

It finds `lean` and `lean4export` in one toolchain, compiles the file, sets
`LEAN_PATH`, and writes the NDJSON. `REAN_LEAN` and `REAN_LEANEXPORT` name the
two binaries when the search does not find them.

The rest of this page is the history of the two committed fixtures, and it is
kept because it records **which** versions made each one and what went wrong on
the way.


## Nat.add_succ.ndjson

Source: the `examples/` directory of `lean4export`.

| Field | Value |
|---|---|
| Upstream | https://github.com/leanprover/lean4export |
| Upstream commit | `05d43a2bc773b40ecfdebb32294192a5ef756951` |
| License | Apache License 2.0, the same as this repository |
| Retrieved | 2026-10-09 |

The `meta` line of the file reports its own versions:

```json
{"meta":{"exporter":{"name":"lean4export","version":"3.0.0"},"format":{"version":"3.0.0"},"lean":{"githash":"2fcce7258eeb6e324366bc25f9058293b04b7547","version":"4.27.0-rc1"}}}
```

**Pin these three numbers.** The exporter, the format, and the Lean version are
each versioned on their own, and the format has already changed more than once.

### Contents

The file holds the full transitive closure of one theorem, `Nat.add_succ`.
That is 19 declarations, 103 names, 15 universe levels, and 434 terms in 572
lines.

```
inductive  Nat              ctors Nat.zero, Nat.succ   rec Nat.rec   2 iota rules
inductive  Eq               ctor  Eq.refl              rec Eq.rec    1 iota rule
inductive  HAdd, Add        the type classes
inductive  PUnit, PProd
def        outParam, HAdd.hAdd, Add.add, instHAdd, instAddNat, rfl
def        Nat.below, Nat.brecOn.go, Nat.brecOn, Nat.casesOn
def        Nat.add.match_1
def        Nat.add
theorem    Nat.add_succ    <- the target
```

This is a rich first target. It covers an inductive declaration, a recursor with
its iota rules, a projection, universe polymorphism, type class instances, and
the helper declarations that Lean generates on its own.

Note `Nat.add.match_1` and `Nat.brecOn`. Nobody wrote those. Lean generated
them when it compiled a `match` and a recursive definition. They are the reason
that checkpoint level 3 of the roadmap compares types and not terms.

## How to generate a new fixture

`lean4` is in `devbox.json`, so a Lean is available:

```sh
devbox run -- lake --version      # Lake 5.0.0-src+v4.30.0 (Lean 4.30.0)
```

But building `lean4export` from its master branch does **not** work with it.
Master pins a different toolchain:

```sh
cat lean-toolchain     # leanprover/lean4:v4.35.0-rc4
```

So one of three steps is needed:

1. Install `elan` and let it fetch the pinned toolchain.
2. Check out a `lean4export` commit whose `lean-toolchain` matches the devbox
   Lean.
3. Bump the devbox `lean4` version to match master.

**The first one is done.** `elan` carries `v4.35.0-rc3` with an exporter beside
it, and `rean export` finds the pair by itself. Chapter 24 reports the prelude
measured against that toolchain: 59,349 declarations, 345 MB, exported in 16
seconds.

## What this fixture does not cover

One real module exercises only the paths that one module needs. This one has:

- no mutual inductive declaration, so the ordering of the motives and the minor
  premises of a mutual recursor is **unvalidated**. See chapter 15, section 15.1.
- no nested inductive declaration
- no `Quot`
- no `letE`, no `mdata`, no literal
- no `axiom`, and no `opaque`

The first item is the one worth chasing. Everything else has a written test.

---

## shapes.ndjson

The second fixture, and this one we generated. It covers every shape that
`Nat.add_succ.ndjson` leaves out.

| Field | Value |
|---|---|
| Source | `fixtures/lean4export/shapes.lean`, exported by `lean4export` |
| Upstream commit | `a3e35a584f59b390667db7269cd37fca8575e4bf` |
| Toolchain | `leanprover/lean4:v4.30.0` |
| Format | 3.1.0 |
| Size | 964 lines, 63 declarations |

### What it covers

| Shape | Declaration |
|---|---|
| a **mutual** inductive group | `Tree` and `Forest`, with two recursors |
| a **nested** inductive | `Rose`, with `numNested = 1` and an auxiliary recursor |
| all four **quotient** constants | `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` |
| a **structure**, for eta | `Point` |
| `letE` | `withLet` |
| a `Nat` **literal** and arithmetic | `twoAddThree : 2 + 3 = 5` |
| `proj` | five of them |

### What it settled

Chapter 15 derived the shape of a mutual recursor from reading, with no ground
truth. This fixture confirms it:

```
rec Tree.rec   all=[Tree, Forest]  motives=2  minors=3  rules=[Tree.node]
rec Forest.rec all=[Tree, Forest]  motives=2  minors=3  rules=[Forest.nil, Forest.cons]
```

One motive per type in the group, one minor premise per constructor of **both**
types, and iota rules only for the type the recursor takes apart. That is
exactly what chapter 15 predicted, and `Tree.rec` and `Forest.rec` both pass.

It also showed one thing chapter 15 got **wrong**. For a nested declaration the
recursor speaks about an auxiliary type that Lean builds and never exports:

```
inductive Rose    nested=1  all=[Rose]
rec Rose.rec      all=[Rose]  motives=2   <- two motives, one type
rec Rose.rec_1    all=[Rose]  rules=[List.nil, List.cons]   <- not in its group
```

Every group check would fire on a correct declaration. So a nested recursor is
now **trusted**, and that is the one place the checker still takes a recursor on
faith.

## How to build the exporter

`lean4export` master pins a Lean that devbox does not carry. Commit
`a3e35a584f59b390667db7269cd37fca8575e4bf` pins `v4.30.0`, which devbox does.

```sh
git clone https://github.com/leanprover/lean4export
cd lean4export && git checkout a3e35a584f59b390667db7269cd37fca8575e4bf
lake build            # compiles, and then the link fails
```

The link fails with `ld: library 'c++' not found`, because Lean passes the nix
Apple SDK and that SDK carries no `libc++`. Point the link at the Xcode SDK
instead:

```sh
SDK=$(xcrun --show-sdk-path)
sed "s|-isysroot[^\"]*MacOSX.sdk|-isysroot$SDK|" \
  .lake/build/bin/lean4export.rsp > .lake/build/bin/patched.rsp
MACOSX_DEPLOYMENT_TARGET=14.0 cc -o .lake/build/bin/lean4export \
  @.lake/build/bin/patched.rsp
```

Then export a module, with an optional list of declarations after `--`:

```sh
lake env <path>/lean4export Probe -- Tree Forest Rose Point Q withLet twoAddThree
```

Without the list it exports the whole transitive closure. For this probe that is
340 MB and 6.4 million lines, which is a fine test input and far too big to
commit.

---

## A bigger input, for finding bugs rather than guarding them

The two fixtures above are committed because they are small and they guard
behaviour. A much bigger input is better for **finding** behaviour, and it is
not committed because it is 757 KB.

Take the declarations that a full prelude run reported as failures, and export
exactly those with their closure:

```sh
lake env <path>/lean4export Probe -- \
  Option.pbind_join DecidableEq Nat.noConfusionType Rat.den FloatSpec.float \
  String.utf8ByteSize_empty
```

That gives 487 declarations in 13,469 lines, and it runs in under a second. It
found three real problems in one sitting:

| Failure | Cause |
|---|---|
| `Option.pbind_join`, "bound variable #1 points outside the term" | **our bug.** The term as read is closed. `struct_eta_eq` asked for the type of an open term and the error escaped `is_def_eq`. |
| the same, after that guard | **our bug.** `eta_eq` left both sides open, so proof irrelevance could not fire. It now opens the binder into a free variable. |
| `String.utf8ByteSize_empty` | a **missing feature**: the kernel did not compute on a string literal. |

Each one now has a unit test in `crates/rean_kernel/tests/soundness.rs`, so the
757 KB file is not needed to keep them fixed.

A note on the method. Exporting a name that does not exist makes the exporter
**panic** part way through, leaving a truncated file with dangling indices. The
error names the constant, so take it out and run again.
