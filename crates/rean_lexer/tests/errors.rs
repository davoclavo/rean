//! Every way a file can be lexically wrong.
//!
//! The lexer never stops at the first error. It reports, repairs, and carries
//! on to the end of the file. So every test here asserts two things: the error
//! appeared, and the token list still reached `Eof`.

use rean_core::{DiagnosticBag, SourceMap};
use rean_lexer::{Token, TokenKind, TokenTable, tokenize};

/// Lexes `text` and returns the tokens with the diagnostics.
fn lex(text: &str) -> (Vec<Token>, DiagnosticBag) {
    let mut map = SourceMap::new();
    let id = map.add("t.lean", text);
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(map.file(id), &TokenTable::builtin(), &mut diags);
    assert!(
        tokens.last().is_some_and(Token::is_eof),
        "the lexer must always reach the end of {text:?}"
    );
    (tokens, diags)
}

/// Lexes `text` and asserts exactly `count` errors with a message about `hint`.
fn expect_errors(text: &str, count: usize, hint: &str) -> Vec<Token> {
    let (tokens, diags) = lex(text);
    assert_eq!(diags.error_count(), count, "for {text:?}");
    let mut map = SourceMap::new();
    let id = map.add("t.lean", text);
    let rendered = diags.render(map.file(id));
    assert!(
        rendered.contains(hint),
        "for {text:?} the message must mention {hint:?}, and it said:\n{rendered}"
    );
    tokens
}

// --- comments -------------------------------------------------------------

#[test]
fn an_unterminated_block_comment_is_one_error() {
    expect_errors("a /- oops", 1, "unterminated block comment");
}

#[test]
fn an_unterminated_nested_block_comment_is_one_error() {
    expect_errors(
        "a /- outer /- inner -/ still open",
        1,
        "unterminated block comment",
    );
}

#[test]
fn an_unterminated_doc_comment_still_gives_a_token() {
    let tokens = expect_errors("/-- oops", 1, "unterminated doc comment");
    match &tokens[0].kind {
        TokenKind::DocComment(text) => assert!(text.contains("oops")),
        other => panic!("expected a doc comment, got {other:?}"),
    }
}

#[test]
fn a_doc_comment_can_hold_a_block_comment() {
    let (tokens, diags) = lex("/-- outer /- inner -/ still doc -/ def");
    assert!(diags.is_empty(), "this one is well formed");
    match &tokens[0].kind {
        TokenKind::DocComment(text) => {
            assert!(text.contains("outer"));
            assert!(text.contains("still doc"));
        }
        other => panic!("expected a doc comment, got {other:?}"),
    }
    assert!(tokens[1].kind.is_atom("def"));
}

// --- identifiers ----------------------------------------------------------

#[test]
fn an_unterminated_escaped_identifier_is_one_error() {
    let tokens = expect_errors("def «never closed", 1, "unterminated escaped identifier");
    // The name still carries the text that was there.
    match &tokens[1].kind {
        TokenKind::Ident { name, .. } => assert_eq!(name.to_string(), "never closed"),
        other => panic!("expected an identifier, got {other:?}"),
    }
}

#[test]
fn an_escaped_part_can_sit_in_the_middle_of_a_name() {
    let (tokens, diags) = lex("A.«b c».d");
    assert!(diags.is_empty());
    match &tokens[0].kind {
        TokenKind::Ident { name, .. } => assert_eq!(name.to_string(), "A.b c.d"),
        other => panic!("expected an identifier, got {other:?}"),
    }
}

// --- numbers --------------------------------------------------------------

#[test]
fn a_radix_number_with_no_digit_is_one_error() {
    expect_errors("def x := 0x", 1, "needs at least one digit");
    expect_errors("def x := 0b", 1, "needs at least one digit");
    expect_errors("def x := 0o", 1, "needs at least one digit");
}

#[test]
fn an_underscore_separates_the_digits_of_a_radix_number() {
    let (tokens, diags) = lex("0xFF_FF");
    assert!(diags.is_empty());
    match &tokens[0].kind {
        TokenKind::Nat { radix, digits } => {
            assert_eq!(*radix, 16);
            assert_eq!(&**digits, "FFFF", "the underscore must go away");
        }
        other => panic!("expected a number, got {other:?}"),
    }
}

#[test]
fn an_upper_case_radix_prefix_works() {
    for text in ["0XFF", "0B1010", "0O17"] {
        let (tokens, diags) = lex(text);
        assert!(diags.is_empty(), "{text}");
        assert!(matches!(tokens[0].kind, TokenKind::Nat { .. }), "{text}");
    }
}

#[test]
fn an_exponent_with_a_plus_sign_works() {
    let (tokens, diags) = lex("2e+10");
    assert!(diags.is_empty());
    assert!(matches!(tokens[0].kind, TokenKind::Scientific(_)));
}

// --- strings and characters ----------------------------------------------

#[test]
fn an_unterminated_string_at_the_end_of_the_file_is_one_error() {
    expect_errors("\"oops", 1, "unterminated string");
}

#[test]
fn an_unterminated_string_at_a_line_break_is_one_error() {
    expect_errors("\"oops\nnext", 1, "unterminated string");
}

#[test]
fn an_unknown_escape_is_one_error() {
    expect_errors(r#""a\qb""#, 1, "unknown escape");
}

#[test]
fn a_hex_escape_with_too_few_digits_is_one_error() {
    expect_errors(r#""\x4""#, 1, "needs 2 hex digits");
    expect_errors(r#""\u00""#, 1, "needs 4 hex digits");
}

#[test]
fn an_escape_that_is_not_a_character_is_one_error() {
    // A surrogate code point is not a character.
    expect_errors(r#""\ud800""#, 1, "is not a character");
}

#[test]
fn every_simple_escape_decodes() {
    let (tokens, diags) = lex(r#""\n\t\r\\\"\'\x41é""#);
    assert!(diags.is_empty());
    match &tokens[0].kind {
        TokenKind::Str(value) => assert_eq!(&**value, "\n\t\r\\\"'Aé"),
        other => panic!("expected a string, got {other:?}"),
    }
}

#[test]
fn an_unterminated_character_literal_is_one_error() {
    expect_errors("'a", 1, "unterminated character literal");
    expect_errors("'", 1, "unterminated character literal");
}

#[test]
fn a_character_literal_with_an_escape_works() {
    for (text, want) in [(r"'\n'", '\n'), (r"'\x41'", 'A'), (r"'\\'", '\\')] {
        let (tokens, diags) = lex(text);
        assert!(diags.is_empty(), "{text}");
        assert_eq!(tokens[0].kind, TokenKind::Char(want), "{text}");
    }
}

#[test]
fn a_bad_escape_in_a_character_literal_gives_a_placeholder() {
    let tokens = expect_errors(r"'\q'", 1, "unknown escape");
    // The lexer must still give one token, so the parser can carry on.
    assert!(matches!(tokens[0].kind, TokenKind::Char(_)));
}

// --- several errors in one file ------------------------------------------

#[test]
fn the_lexer_reports_every_error_in_one_run() {
    // Four separate problems. The lexer must find all four, not only the first.
    let text = "0x ∰ \"open\n«never";
    let (_, diags) = lex(text);
    assert_eq!(diags.error_count(), 4, "{:#?}", diags.items());
}

// --- the token kind labels ------------------------------------------------

#[test]
fn every_token_kind_has_a_label_and_a_display() {
    let (tokens, _) = lex("/-- d -/ def x 1 1.5 \"s\" 'c' ∰ :=");
    let labels: Vec<&str> = tokens.iter().map(|t| t.kind.label()).collect();
    for wanted in [
        "doc",
        "keyword",
        "ident",
        "nat",
        "scientific",
        "str",
        "char",
        "unknown",
        "symbol",
        "eof",
    ] {
        assert!(labels.contains(&wanted), "no token had the label {wanted}");
    }
    for token in &tokens {
        assert!(!token.kind.to_string().is_empty() || token.is_eof());
        // `atom_text` answers only for a keyword or a symbol.
        let is_atom = matches!(token.kind, TokenKind::Keyword(_) | TokenKind::Symbol(_));
        assert_eq!(token.kind.atom_text().is_some(), is_atom);
    }
}

#[test]
fn a_base_other_than_ten_prints_its_base() {
    let (tokens, _) = lex("0xFF 10");
    assert_eq!(tokens[0].kind.to_string(), "FF (base 16)");
    assert_eq!(tokens[1].kind.to_string(), "10");
}
