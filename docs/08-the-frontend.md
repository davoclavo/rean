# Chapter 8 — The frontend

Chapters 0 to 7 are all about the kernel. This one is about the other end: how
text becomes something a kernel can read.

It is **independent of the kernel**, so read it whenever you like. A reader who
wants the logic first should skip it. A reader who wants to see where a compiler
begins should start here.

```sh
devbox run -- cargo run -p rean -- lex examples/tokens.lean
devbox run -- cargo test -p rean_lexer
```

---

## 8.1 Why the frontend is a separate story

A C compiler owns its grammar. The keywords are in the lexer, the precedence is
in the parser, and no program can change either.

Lean is not like that. A Lean file can **extend the language it is written in**:

```lean
infixl:65 " ⊹ " => HAdd.hAdd
```

After that line `⊹` is a token with a precedence. Before it, `⊹` is an unknown
character. So the frontend cannot hold a fixed grammar. It has to read the
grammar out of something that grows as the file does.

That single fact shapes everything in this chapter.

---

## 8.2 The shared vocabulary

Three types that every later stage speaks. They live in `rean_core`.

### `Name`: a hierarchical identifier

`Nat.succ` is not a string. It is a list of parts that grows at the front:

```rust
Name::from_dotted("Nat.succ")   // Str(Str(Anonymous, "Nat"), "succ")
```

Three reasons, and all three come up later:

- A `namespace` command only adds a prefix, so a list makes that cheap.
- The elaborator invents fresh names such as `_uniq.17`. A numeric part needs no
  string. And the real Lean export is full of them: `Nat.add.match_1`,
  `Nat.brecOn.go`.
- A `Syntax` node kind is **also** a `Name`. One type serves both jobs. See
  section 8.6.

### `Span`: a byte range

A position is one `u32` byte offset. A `Span` is therefore 8 bytes, so every
syntax node can hold one without thinking about it.

The line and the column are computed only when a message is printed.
`SourceFile` keeps a table of line start offsets for that, and finds the line
with a binary search:

```rust
let line_index = self.line_starts.partition_point(|start| *start <= offset) - 1;
```

One detail that is easy to get wrong: the **column counts characters, not
bytes**. A test holds that line, because `α → β` would otherwise report the
wrong column.

### `Diagnostic`: many errors in one run

No stage stops at the first error. It reports, repairs, and carries on:

```rust
bag.push(Diagnostic::error(span, "unexpected character"));
```

That one rule has a consequence that reaches all the way into the tree. If the
parser must carry on after an error, it needs something to put in the hole. That
is why `Syntax` has a `Missing` node. Section 8.6.

The renderer prints the source line and a caret bar under the span:

```
error: unknown identifier 'bogus'
  --> a.lean:1:10
  |
1 | def f := bogus
  |          ^^^^^
  note: did you mean 'bogon'?
```

A span that crosses a line break stops its caret bar at the end of the first
line. A test holds that too.

---

## 8.3 `TokenTable`: the lexer has no keyword list

This is the idea worth the chapter.

A C lexer holds its keywords in a `match`. A Lean lexer cannot, because of the
`infixl` line in section 8.1. So the lexer holds **no** keyword list. It asks a
table, and the table can grow:

```rust
let mut table = TokenTable::builtin();   // 58 keywords, 77 symbols
table.insert("⊹");                       // what a `notation` command does
```

The table answers one question: **what is the longest token in the table that
starts this text?**

```rust
pub fn longest_match(&self, text: &str) -> Option<Arc<str>> {
    let limit = self.max_len.min(text.len());
    for end in (1..=limit).rev() {
        if !text.is_char_boundary(end) { continue; }
        if let Some(found) = self.tokens.get(&text[..end]) { return Some(found.clone()); }
    }
    None
}
```

Three things in nine lines:

- **Longest match wins.** Without it, `:=` would lex as `:` and then `=`. The
  test is `the_longest_symbol_wins`, and it also covers `<;>` against `<`.
- **A slice must land on a character boundary.** `→` is three bytes. Slicing it
  at one byte would panic, so the loop skips a boundary that does not exist.
- **`max_len` bounds the loop.** The table knows its longest entry, so the
  search never looks further than it has to.

### The two tests that make the point

```rust
fn the_table_decides_what_is_a_keyword() {
    // With an empty table, `def` is only a name.
    let (tokens, _) = lex_raw("def x", &TokenTable::new());
    assert!(matches!(tokens[0].kind, TokenKind::Ident { .. }));

    // One insert turns the same text into a keyword.
    let mut table = TokenTable::new();
    table.insert("def");
    let (tokens, _) = lex_raw("def x", &table);
    assert!(tokens[0].kind.is_atom("def"));
}
```

```rust
fn a_notation_command_can_add_a_symbol() {
    let mut table = TokenTable::builtin();
    let (_, diags) = lex_raw("a ⊹ b", &table);
    assert_eq!(diags.error_count(), 1, "the symbol is unknown at first");

    table.insert(" ⊹ ");
    let (tokens, diags) = lex_raw("a ⊹ b", &table);
    assert!(diags.is_empty());
    assert!(tokens[1].kind.is_atom("⊹"));
}
```

The same text, two answers, and the only difference is the table. That is the
whole design in one test.

### And an example that fails on purpose

`examples/notation.lean` declares three symbols and then uses them:

```
error: unexpected character '⊹'
error: unexpected character '⟪'
error: unexpected character '⟫'
3 error(s)
```

Those errors are **correct**. A parser must read the `notation` commands and
call `insert`, and there is no parser yet. So the file records the gap rather
than hiding it, and `tests/examples.rs` locks the count at three. A third test
adds the symbols and watches the count drop to zero.

---

## 8.4 Which characters make a name

Lean lets you write `α`, `Γ₀`, and `𝒞` as ordinary identifiers, so the lexer
needs explicit Unicode ranges:

```rust
pub fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}
```

`is_letter_like` lists the ranges: lower case Greek, upper case Greek, accented
and polytonic Greek, letter like symbols such as `ℕ`, script and double struck
Latin such as `𝒞`, ligatures, CJK, and Hangul Jamo.

Three characters are **cut out** of those ranges on purpose:

| Character | Why |
|---|---|
| `λ` | Lean reserves it for a lambda |
| `Π` | reserved for a function type |
| `Σ` | reserved for a sigma type |

So `λ x` lexes as a symbol and a name, and `α` lexes as one name. Both have
tests.

`is_id_rest` is wider. It adds the digits, the prime, and the subscripts, so
`x'`, `h₂`, and `f1` are single identifiers. That is why `is_id_first` and
`is_id_rest` are two functions and not one.

---

## 8.5 The lexer, and the rule that no error stops it

`rean_lexer` produces ten kinds of token:

| Kind | Example |
|---|---|
| `Ident` | `Nat.succ`, `«a name with spaces»` |
| `Keyword` | `def`, from the table |
| `Symbol` | `:=`, `→`, from the table |
| `Nat` | `10`, `0xFF`, `0b1010`, `0o17` |
| `Scientific` | `1.5`, `2e10`, `3e-4` |
| `Str` | `"a\tb"`, after the escapes are decoded |
| `Char` | `'x'`, `'\n'` |
| `DocComment` | `/-- … -/`, which Lean keeps as part of the program |
| `Unknown` | a character that fits no rule |
| `Eof` | always last |

Four decisions in there are worth naming.

**A dotted name is one token.** `Nat.succ.inj` is a single `Ident` with a
hierarchical `Name`. But the name only continues over a dot when a name part
follows it:

```rust
if self.peek() == Some('.') && self.next_part_follows_dot() {
```

So `p.1` lexes as three tokens, because `1` is not a name part and `p.1` is a
projection. The test is `a_dot_before_a_digit_stays_separate`.

**A number keeps its digits as text.** `Nat { radix, digits: Arc<str> }`, not a
machine integer, because a Lean `Nat` has no upper bound. Chapter 4 found out
how much that choice matters, and the export format made the same one.

**A doc comment is a token, and a block comment is not.** Both nest. The
difference is that `/-- … -/` is documentation, so Lean keeps it, and `/- … -/`
disappears. One edge case needs a guard: `/--/` is an **empty block comment**,
not the start of a doc comment.

**No error stops the lexer.** Every error path reports a diagnostic, repairs the
hole, and carries on to `Eof`. `tests/errors.rs` has 22 tests, and every one of
them asserts both halves:

```rust
assert!(
    tokens.last().is_some_and(Token::is_eof),
    "the lexer must always reach the end of {text:?}"
);
```

The paths are: an unterminated block comment, doc comment, escaped identifier,
string, and character literal; a radix number with no digit; an unknown escape;
a hex escape with too few digits; and an escape that is not a character. One
test puts four separate problems in one file and asserts that it finds all four,
not only the first.

---

## 8.6 `Syntax`: one lossless tree

Most compilers give each construct its own struct. Lean has **one** tree type
with four cases:

```rust
pub enum Syntax {
    Missing,
    Atom  { span: Span, value: Arc<str> },
    Ident { span: Span, raw: Arc<str>, name: Name },
    Node  { kind: Name, span: Span, args: Vec<Syntax> },
}
```

Three things follow from that shape.

**The node kind is a `Name`.** Not an enum. `Rean.Parser.Term.app`, built the
same way `Nat.succ` is. The macro system forces this: a `syntax` command
declares a new node kind at run time, and a fixed set of Rust variants could
never hold one. A `Name` can.

**The tree keeps everything.** Every keyword, every bracket, every literal as
its source text. So the tree is **lossless** and a pretty printer or a language
server can work from it. `rean demo` shows the shape:

```
(Rean.Parser.Command.def
  "def"
  (ident twice)
  (Rean.Parser.Binder
    "("
    (ident f)
    ":"
    (Rean.Parser.Term.arrow (ident Nat) "→" (ident Nat))
    ")"
  )
  ...
)
```

Note the `"("` and the `")"`. A tree that threw them away could not print the
program back.

**`Missing` is the repair.** Section 8.2 said no stage stops at the first error.
This is where that lands. The parser reports a diagnostic, puts `Missing` in the
hole, and carries on. Then `has_missing` walks the tree:

```rust
pub fn has_missing(&self) -> bool {
    match self {
        Syntax::Missing => true,
        Syntax::Node { args, .. } => args.iter().any(Syntax::has_missing),
        _ => false,
    }
}
```

The elaborator calls it. It must not report a type error for a tree the parser
already failed to read.

The price of one tree type is that a later stage **cannot trust the shape of a
node**. The elaborator has to check it itself. That is the trade: the frontend
stays open to extension, and the elaborator carries the cost.

---

## 8.7 What is missing

| Missing | Effect |
|---|---|
| **the parser** | nothing turns a `Vec<Token>` into a `Syntax` tree |
| trivia on a token | the lexer drops whitespace, so a `do` block has no column and a printer has no spacing |
| the precedence table | a `notation` command sets a precedence, and nothing stores it |

The first row is the one that matters. **The lexer and the kernel are two
islands, and nothing crosses between them.** Nothing you write in a `.lean`
file reaches `infer_type`. The kernel's input comes from a `lean4export` file,
which chapter 3 explains, or from Rust written by hand.

That is why `rean demo` labels its stage 2 output "hand built". It shows the
shape a parser must produce. It is not a parser.

```
examples/universes.lean
        |
        v
   [ lexer ]   works
        |
   Vec<Token>  a flat list, 90 tokens
        |
        X      nothing consumes a token list
```

---

## 8.8 Exercises

1. `is_id_first` and `is_id_rest` are two functions. Give a name that needs the
   difference, and say what breaks if there is only one function.
2. `longest_match` skips an index that is not a character boundary. Give the
   input that panics without that guard.
3. The lexer continues a name over a dot only when a name part follows. What
   breaks in `p.1` if it always continues?
4. `/--/` is an empty block comment and not the start of a doc comment. Write
   the three characters the lexer reads before it can tell.
5. `Syntax` keeps `"("` and `")"` as atoms. Name two tools that need them.
6. `TokenTable::builtin` holds 58 keywords and 77 symbols. Explain why that
   number is not part of the language.

### Answers

1. `h₂'`. The subscript and the prime are in `is_id_rest` and not in
   `is_id_first`. With one function, `₂` could start a name, and worse, `'`
   could, so `'x'` would lex as a name instead of a character literal.
2. `→ β`, or any text starting with a multi byte character whose first byte is
   also the start of a shorter table entry. Slicing `→` at one byte is not a
   character boundary and panics.
3. `p.1` would become one identifier with a numeric part, and the projection
   would disappear. The parser would never see the `.` it needs.
4. `/`, `-`, `-`. At that point both readings are open. The fourth character
   decides: a `/` means the block comment closes at once, and anything else
   means a doc comment begins.
5. A pretty printer, which has to put them back, and a language server, which
   has to map a cursor position to a node.
6. Because the table is the **starting** set, not the language. A `notation` or
   `syntax` command adds to it while the file is read, so the number is only
   what Lean's own prelude would have inserted before any user code runs. See
   section 8.3.

## 8.9 References

- `crates/rean_core/src/name.rs`, `source.rs`, `diag.rs`
- `crates/rean_lexer/src/table.rs`, `chars.rs`, `lexer.rs`, `token.rs`
- `crates/rean_syntax/src/lib.rs`, `kind.rs`
- `crates/rean_lexer/tests/lex.rs`, 25 tests;
  `tests/errors.rs`, 22 tests; `tests/examples.rs`, 3 tests
- `examples/tokens.lean` and `examples/notation.lean`
- *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages*,
  Ullrich and de Moura, for why the frontend is extensible at all
