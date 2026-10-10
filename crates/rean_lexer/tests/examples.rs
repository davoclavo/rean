//! Lexes every file in `examples/`.
//!
//! The examples are documentation, so they must keep working. This test fails
//! if an example stops lexing, or if somebody adds an example and tests none
//! of it.

use rean_core::{DiagnosticBag, SourceMap};
use rean_lexer::{TokenTable, tokenize};
use std::path::PathBuf;

/// The number of errors that each example must produce.
///
/// `notation.lean` is the one file that must fail. It uses three symbols that
/// `TokenTable::builtin` does not hold, and a parser has to insert them. No
/// parser exists yet, so the errors stand as a record of the gap.
const EXPECTED: &[(&str, usize)] = &[
    ("twice.lean", 0),
    ("tokens.lean", 0),
    ("universes.lean", 0),
    ("notation.lean", 3),
];

/// The symbols that `notation.lean` declares.
const DECLARED_SYMBOLS: &[&str] = &["⊹", "⟪", "⟫"];

fn examples_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

/// Lexes one example and returns the token count and the error count.
fn lex_example(name: &str, table: &TokenTable) -> (usize, usize) {
    let path = examples_dir().join(name);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|err| {
        panic!("cannot read {}: {err}", path.display());
    });

    let mut map = SourceMap::new();
    let id = map.add(name, text);
    let file = map.file(id);
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(file, table, &mut diags);

    // The lexer must always reach the end of the file.
    assert!(
        tokens.last().is_some_and(|token| token.is_eof()),
        "{name}: the token list must end with eof"
    );
    // Every span must move forward and must stay inside the text.
    let mut last = 0;
    for token in &tokens {
        assert!(token.span.start >= last, "{name}: a span runs backwards");
        assert!(
            token.span.end as usize <= file.text().len(),
            "{name}: a span runs past the end of the file"
        );
        last = token.span.end;
    }
    (tokens.len(), diags.error_count())
}

#[test]
fn every_example_lexes_with_the_expected_error_count() {
    let table = TokenTable::builtin();
    for (name, expected) in EXPECTED {
        let (tokens, errors) = lex_example(name, &table);
        assert!(tokens > 1, "{name}: the file produced no token");
        assert_eq!(errors, *expected, "{name}: wrong number of errors");
    }
}

#[test]
fn the_list_above_covers_every_example_file() {
    let mut found: Vec<String> = std::fs::read_dir(examples_dir())
        .expect("the examples directory must exist")
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            if path.extension()?.to_str()? == "lean" {
                Some(path.file_name()?.to_str()?.to_string())
            } else {
                None
            }
        })
        .collect();
    found.sort();

    let mut listed: Vec<String> = EXPECTED.iter().map(|(name, _)| name.to_string()).collect();
    listed.sort();

    assert_eq!(
        found, listed,
        "add every new example to the EXPECTED list in this file"
    );
}

#[test]
fn inserting_the_declared_symbols_clears_the_errors() {
    // This is the whole point of `TokenTable`. A `notation` command inserts a
    // symbol, and the same text then lexes with no error.
    let mut table = TokenTable::builtin();
    for symbol in DECLARED_SYMBOLS {
        table.insert(symbol);
    }
    let (_, errors) = lex_example("notation.lean", &table);
    assert_eq!(
        errors, 0,
        "the table now holds every symbol that the file uses"
    );
}
