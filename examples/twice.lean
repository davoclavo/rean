/-- Apply a function to its own result. -/
def twice (f : Nat → Nat) : Nat → Nat :=
  fun x => f (f x)

-- A dotted name, a unicode name, and a numeral.
theorem twice_succ (n : Nat) : twice Nat.succ n = n + 2 := by
  simp [twice, Nat.add]

def «a name with spaces» : Nat := 0xff

def greeting : String := "hello\tworld\n"

/- A block comment /- holds another one -/ and then ends. -/
example : Prop := ∀ α : Type, α → α
