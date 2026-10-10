/--
Why the lexer cannot hold a fixed keyword list.

Each command below adds a token to the table while the compiler reads the
file. `rean_lexer` therefore reads its tokens from `TokenTable`, and the table
can grow. See `crates/rean_lexer/src/table.rs`.

This file does NOT lex cleanly yet, and that is the point. The three symbols
`⊹`, `⟪`, and `⟫` are not in `TokenTable::builtin`. A parser must read the
commands below and insert them. No parser exists, so `rean lex` reports three
errors for the three bare uses at the end.
-/

-- The symbol sits inside a string here, so the lexer sees one `str` token.
infixl:65 " ⊹ " => HAdd.hAdd
notation:max "⟪" a "⟫" => Prod.mk a a
syntax "mymacro" term : term

-- These three uses are bare, so the lexer must know the symbols already.
#check 1 ⊹ 2
#check ⟪3⟫
