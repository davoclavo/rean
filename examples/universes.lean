/--
`Sort`, `Prop`, and `Type`. See `docs/00-introduction-to-the-kernel.md`.
-/

universe u v

-- `Prop` is `Sort 0`. `Type` is `Sort 1`. `Type n` is `Sort (n+1)`.
example : Prop := True
example : Type := Nat
example : Type 1 := Type

-- `Prop` and `Nat` are elements of the same universe, so one list holds both.
example : List Type := [Nat, Prop, Bool]

-- An element of `Prop` is also a type, so it has elements of its own.
def p : Prop := 2 = 2
theorem hp : p := rfl

-- A false proposition is still a good element of `Prop`.
def q : Prop := 2 + 2 = 5

-- Universe polymorphism. The definition takes `u` as a parameter.
def idOf (α : Sort u) (a : α) : α := a

-- Impredicativity. The body is a `Prop`, so `imax` collapses the level to 0.
example : Prop := ∀ r : Prop, r → r

-- The trap. Here the body sits at the level of α, not at 0, so `imax` does
-- not collapse. This term is not a `Prop`.
-- ∀ α : Type u, α → α    lives at   Sort (imax (u+1) (u+1))

-- `Not` is data. Its type is `Prop → Prop`, which lives at `Type`.
#check Not

-- `Not False` reduces to `False → False`, and not to `True`.
#reduce Not False
