/--
Every token kind that `rean_lexer` knows.

Run `cargo run -p rean -- lex examples/tokens.lean` to see the stream.
-/

-- A line comment disappears.
/- A block comment /- holds another one -/ and then ends. -/

-- Identifiers. A dot joins the parts into one token.
def plain := 0
def dotted := Nat.succ.inj
def greek := α
def subscripts := h₂
def primed := x'
def «a name with spaces» := 1
def 𝒞 := 2
def ℕ := 3

-- Numbers in four bases, and two with an exponent.
def decimal := 10
def hex := 0xFF
def binary := 0b1010
def octal := 0o17
def point := 1.5
def exponent := 2e10
def negativeExponent := 3e-4

-- A dot before a digit stays a separate token, because `p.1` is a projection.
def projection := p.1
def range := 1..2

-- Strings and characters, with escapes.
def text := "tab\there\nand a quote \" and \x41 and α"
def letter := 'x'
def newline := '\n'

-- Symbols.
def arrows := fun x => x
def unicodeArrows : Nat → Nat := id
def logic := ∀ α, ∃ β, α ∧ β ∨ ¬ α ↔ β
def compare := 1 <= 2 ≤ 3 ≥ 2 >= 1 ≠ 0
def sets := a ∈ s ∪ t ∩ u ⊆ v
def pipes := x <| f |> g <;> h ++ k
def brackets := ⟨1, 2⟩
def products : Type := Nat × Nat ⊕ Nat

-- Commands that start with a hash.
#check Nat
#eval 2 + 2
