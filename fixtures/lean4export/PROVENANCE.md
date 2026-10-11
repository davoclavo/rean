# Ground truth fixtures

These files come from the real Lean. They are the checkpoint that our own
pipeline must meet. See `docs/ROADMAP.md`.

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

So one of three steps is needed, and none is done yet:

1. Install `elan` and let it fetch the pinned toolchain.
2. Check out a `lean4export` commit whose `lean-toolchain` matches the devbox
   Lean.
3. Bump the devbox `lean4` version to match master.

Until then, the committed example file is the ground truth. It is enough for
chapters 3 and 4 of the roadmap.

## What this fixture does not cover

One real module exercises only the paths that one module needs. This one has:

- no mutual inductive declaration, so the ordering of the motives and the minor
  premises of a mutual recursor is **unvalidated**. See chapter 7, section 7.1.
- no nested inductive declaration
- no `Quot`
- no `letE`, no `mdata`, no literal
- no `axiom`, and no `opaque`

The first item is the one worth chasing. Everything else has a written test.
MDEOF
echo ok