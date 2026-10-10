//! Tests for the lexer.

use rean_core::{DiagnosticBag, SourceMap};
use rean_lexer::{Token, TokenKind, TokenTable, tokenize};

/// Lexes `text` with the builtin table and asserts that no diagnostic appeared.
fn lex(text: &str) -> Vec<Token> {
    let (tokens, diags) = lex_raw(text, &TokenTable::builtin());
    assert!(diags.is_empty(), "unexpected diagnostics for {text:?}");
    tokens
}

/// Lexes `text` and returns the tokens together with the diagnostics.
fn lex_raw(text: &str, table: &TokenTable) -> (Vec<Token>, DiagnosticBag) {
    let mut map = SourceMap::new();
    let id = map.add("test.lean", text);
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(map.file(id), table, &mut diags);
    (tokens, diags)
}

/// Renders each token as `label:text`, so a test can compare one string.
fn shape(text: &str) -> String {
    lex(text)
        .iter()
        .map(|t| format!("{}:{}", t.kind.label(), t.kind))
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn an_empty_file_gives_only_eof() {
    let tokens = lex("");
    assert_eq!(tokens.len(), 1);
    assert!(tokens[0].is_eof());
}

#[test]
fn a_definition_lexes_into_five_tokens() {
    assert_eq!(
        shape("def two : Nat := 2"),
        "keyword:def ident:two symbol:: ident:Nat symbol::= nat:2 eof:<eof>"
    );
}

#[test]
fn a_dotted_name_is_one_token() {
    assert_eq!(shape("Nat.succ.inj"), "ident:Nat.succ.inj eof:<eof>");
}

#[test]
fn a_dot_before_a_digit_stays_separate() {
    // `p.1` is a projection, not a name with a numeric part.
    assert_eq!(shape("p.1"), "ident:p symbol:. nat:1 eof:<eof>");
}

#[test]
fn french_quotes_escape_a_name_part() {
    assert_eq!(
        shape("Foo.«has space».bar"),
        "ident:Foo.has space.bar eof:<eof>"
    );
}

#[test]
fn unicode_names_and_symbols_lex() {
    assert_eq!(
        shape("fun α => α → α"),
        "keyword:fun ident:α symbol:=> ident:α symbol:→ ident:α eof:<eof>"
    );
}

#[test]
fn subscripts_and_primes_stay_in_the_name() {
    assert_eq!(shape("h₂' x"), "ident:h₂' ident:x eof:<eof>");
}

#[test]
fn lambda_is_a_symbol_and_not_a_name() {
    assert_eq!(shape("λ x"), "symbol:λ ident:x eof:<eof>");
}

#[test]
fn the_longest_symbol_wins() {
    assert_eq!(shape("a <;> b"), "ident:a symbol:<;> ident:b eof:<eof>");
    assert_eq!(shape("a <= b"), "ident:a symbol:<= ident:b eof:<eof>");
}

#[test]
fn line_and_block_comments_disappear() {
    assert_eq!(
        shape("a -- gone\n/- also /- nested -/ gone -/ b"),
        "ident:a ident:b eof:<eof>"
    );
}

#[test]
fn a_doc_comment_is_a_token() {
    let tokens = lex("/-- The number two. -/\ndef two := 2");
    match &tokens[0].kind {
        TokenKind::DocComment(text) => assert_eq!(text.trim(), "The number two."),
        other => panic!("expected a doc comment, got {other:?}"),
    }
    assert!(tokens[1].kind.is_atom("def"));
}

#[test]
fn an_empty_block_comment_is_not_a_doc_comment() {
    assert_eq!(shape("a /--/ b"), "ident:a ident:b eof:<eof>");
}

#[test]
fn numbers_lex_in_every_base() {
    assert_eq!(
        shape("10 0xff 0b1010 0o17"),
        "nat:10 nat:ff (base 16) nat:1010 (base 2) nat:17 (base 8) eof:<eof>"
    );
}

#[test]
fn a_point_or_an_exponent_gives_a_scientific_number() {
    assert_eq!(
        shape("1.5 2e10 3e-4"),
        "scientific:1.5 scientific:2e10 scientific:3e-4 eof:<eof>"
    );
}

#[test]
fn an_e_without_a_digit_is_not_an_exponent() {
    assert_eq!(shape("2either"), "nat:2 ident:either eof:<eof>");
}

#[test]
fn a_range_keeps_both_dots() {
    assert_eq!(shape("1..2"), "nat:1 symbol:.. nat:2 eof:<eof>");
}

#[test]
fn string_escapes_decode() {
    let tokens = lex(r#""a\tb\n\x41α\\""#);
    match &tokens[0].kind {
        TokenKind::Str(value) => assert_eq!(&**value, "a\tb\nAα\\"),
        other => panic!("expected a string, got {other:?}"),
    }
}

#[test]
fn a_character_literal_lexes() {
    assert_eq!(lex("'x'")[0].kind, TokenKind::Char('x'));
    assert_eq!(lex(r"'\n'")[0].kind, TokenKind::Char('\n'));
}

#[test]
fn spans_point_back_at_the_source() {
    let text = "def two := 2";
    let tokens = lex(text);
    assert_eq!(&text[tokens[0].span.range()], "def");
    assert_eq!(&text[tokens[1].span.range()], "two");
    assert_eq!(&text[tokens[3].span.range()], "2");
}

#[test]
fn the_table_decides_what_is_a_keyword() {
    // With an empty table, `def` is only a name and `:=` does not exist.
    let (tokens, diags) = lex_raw("def x", &TokenTable::new());
    assert!(matches!(tokens[0].kind, TokenKind::Ident { .. }));
    assert!(diags.is_empty());

    // A new table entry turns the same text into a keyword.
    let mut table = TokenTable::new();
    table.insert("def");
    let (tokens, _) = lex_raw("def x", &table);
    assert!(tokens[0].kind.is_atom("def"));
}

#[test]
fn a_notation_command_can_add_a_symbol() {
    let mut table = TokenTable::builtin();
    let (_, diags) = lex_raw("a ⊹ b", &table);
    assert_eq!(diags.error_count(), 1, "the symbol is unknown at first");

    table.insert(" ⊹ ");
    let (tokens, diags) = lex_raw("a ⊹ b", &table);
    assert!(diags.is_empty());
    assert!(tokens[1].kind.is_atom("⊹"));
}

#[test]
fn an_unterminated_string_reports_one_error() {
    let (tokens, diags) = lex_raw("\"oops\n", &TokenTable::builtin());
    assert_eq!(diags.error_count(), 1);
    assert!(matches!(tokens[0].kind, TokenKind::Str(_)));
    // The lexer still reaches the end of the file.
    assert!(tokens.last().unwrap().is_eof());
}

#[test]
fn an_unterminated_block_comment_reports_one_error() {
    let (tokens, diags) = lex_raw("a /- oops", &TokenTable::builtin());
    assert_eq!(diags.error_count(), 1);
    assert!(tokens.last().unwrap().is_eof());
}

#[test]
fn an_unknown_character_does_not_stop_the_lexer() {
    let (tokens, diags) = lex_raw("a ∰ b", &TokenTable::builtin());
    assert_eq!(diags.error_count(), 1);
    assert_eq!(tokens.len(), 4, "two names, one unknown, and eof");
    assert!(matches!(tokens[1].kind, TokenKind::Unknown('∰')));
}

#[test]
fn every_span_covers_the_file_in_order() {
    let text = "def f (x : Nat) : Nat := x + 1\n#eval f 2\n";
    let (tokens, _) = lex_raw(text, &TokenTable::builtin());
    let mut last = 0;
    for token in &tokens {
        assert!(token.span.start >= last, "spans must not go backwards");
        assert!(token.span.end <= text.len() as u32);
        last = token.span.end;
    }
}
