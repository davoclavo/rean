/-! Shapes that our fixture does not cover. -/

-- A mutual inductive group. Each recursor needs one motive per type and one
-- minor premise per constructor of BOTH types.
mutual
  inductive Tree where
    | node : Forest → Tree
  inductive Forest where
    | nil  : Forest
    | cons : Tree → Forest → Forest
end

-- A nested inductive: `Rose` sits inside `List`.
inductive Rose where
  | node : List Rose → Rose

-- A quotient.
def Same (a b : Nat) : Prop := a = b
def Q := Quot Same

-- A `let`, and arithmetic on literals.
def withLet : Nat := let n := 2; n + n
theorem twoAddThree : 2 + 3 = 5 := rfl

-- A structure, for eta.
structure Point where
  x : Nat
  y : Nat
