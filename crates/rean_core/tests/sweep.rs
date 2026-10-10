//! One test per accessor, so that no claim goes unchecked.

use rean_core::{Diagnostic, DiagnosticBag, FileId, LineCol, Name, Severity, SourceMap, Span};

// --- Span ----------------------------------------------------------------

#[test]
fn a_span_answers_every_question() {
    let span = Span::new(3, 9);
    assert_eq!(span.start, 3);
    assert_eq!(span.end, 9);
    assert_eq!(span.len(), 6);
    assert!(!span.is_empty());
    assert_eq!(span.range(), 3..9);
    assert_eq!(format!("{span:?}"), "3..9");

    let empty = Span::empty(4);
    assert_eq!(empty.len(), 0);
    assert!(empty.is_empty());
    assert_eq!(empty, Span::new(4, 4));

    // Joining works in either order.
    assert_eq!(Span::new(1, 2).to(Span::new(8, 9)), Span::new(1, 9));
    assert_eq!(Span::new(8, 9).to(Span::new(1, 2)), Span::new(1, 9));
}

#[test]
fn a_line_and_column_print_together() {
    let at = LineCol { line: 4, col: 12 };
    assert_eq!(at.to_string(), "4:12");
    assert_eq!(at, LineCol { line: 4, col: 12 });
}

// --- SourceFile and SourceMap -------------------------------------------

#[test]
fn a_source_file_answers_every_question() {
    let mut map = SourceMap::new();
    let id = map.add("a.lean", "def f :=\n  1\n");
    let file = map.file(id);
    assert_eq!(file.id(), id);
    assert_eq!(file.path(), "a.lean");
    assert_eq!(file.text(), "def f :=\n  1\n");
    assert_eq!(file.slice(Span::new(4, 5)), "f");
    assert_eq!(file.line_count(), 3);
    assert_eq!(file.line_text(1), Some("def f :="));
    assert_eq!(file.line_text(0), None, "lines count from 1");
    assert_eq!(file.line_text(99), None);
    assert_eq!(map.files().len(), 1);
    assert_eq!(FileId(0), id);
}

#[test]
fn an_offset_past_the_end_clamps() {
    let mut map = SourceMap::new();
    let id = map.add("a.lean", "ab");
    let file = map.file(id);
    // A span that runs past the text must not panic.
    assert_eq!(file.line_col(99).to_string(), "1:3");
}

#[test]
fn a_map_holds_more_than_one_file() {
    let mut map = SourceMap::default();
    let first = map.add("a.lean", "a");
    let second = map.add("b.lean", "bb");
    assert_ne!(first, second);
    assert_eq!(map.file(second).path(), "b.lean");
    assert_eq!(map.files().len(), 2);
}

// --- Diagnostic ----------------------------------------------------------

#[test]
fn every_severity_has_a_label() {
    assert_eq!(Severity::Info.label(), "info");
    assert_eq!(Severity::Warning.label(), "warning");
    assert_eq!(Severity::Error.label(), "error");
    // The order matters for a report that sorts by seriousness.
    assert!(Severity::Info < Severity::Warning);
    assert!(Severity::Warning < Severity::Error);
}

#[test]
fn a_bag_starts_empty_and_fills() {
    let mut bag = DiagnosticBag::default();
    assert!(bag.is_empty());
    assert_eq!(bag.len(), 0);
    assert_eq!(bag.error_count(), 0);
    assert!(!bag.has_errors());
    assert!(bag.items().is_empty());

    bag.push(Diagnostic::warning(Span::empty(0), "careful"));
    assert_eq!(bag.len(), 1);
    assert!(!bag.has_errors());
    bag.push(Diagnostic::error(Span::empty(0), "wrong"));
    assert!(bag.has_errors());
    assert_eq!(bag.error_count(), 1);
    assert_eq!(bag.items().len(), 2);
}

#[test]
fn a_bag_renders_every_item() {
    let mut map = SourceMap::new();
    let id = map.add("a.lean", "one\ntwo\n");
    let mut bag = DiagnosticBag::new();
    bag.push(Diagnostic::error(Span::new(0, 3), "first"));
    bag.push(Diagnostic::warning(Span::new(4, 7), "second").with_note("a hint"));
    let text = bag.render(map.file(id));
    assert!(text.contains("error: first"));
    assert!(text.contains("warning: second"));
    assert!(text.contains("note: a hint"));
    assert!(text.contains("a.lean:1:1"));
    assert!(text.contains("a.lean:2:1"));
}

#[test]
fn a_span_that_crosses_a_line_break_gets_a_bar_to_the_line_end() {
    let mut map = SourceMap::new();
    let id = map.add("a.lean", "one\ntwo\n");
    // The span starts at column 2 of line 1 and ends on line 2. The caret bar
    // must stop at the end of line 1, so it covers the two characters `ne`.
    let diag = Diagnostic::error(Span::new(1, 6), "across");
    let text = diag.render(map.file(id));
    assert!(text.contains(" ^^\n"), "{text}");
}

// --- Name ---------------------------------------------------------------

#[test]
fn a_name_answers_every_question() {
    let anonymous = Name::anonymous();
    assert!(anonymous.is_anonymous());
    assert!(anonymous.is_empty());
    assert_eq!(anonymous.len(), 0);
    assert!(anonymous.prefix().is_none());
    assert!(anonymous.last_str().is_none());
    assert_eq!(anonymous.to_string(), "[anonymous]");
    assert_eq!(Name::default(), anonymous);
    assert_eq!(Name::from_dotted(""), anonymous);

    let nat = Name::from("Nat");
    assert_eq!(nat.to_string(), "Nat");
    assert_eq!(format!("{nat:?}"), "`Nat");
    assert!(!nat.is_empty());
    assert_eq!(nat.prefix(), Some(&anonymous));

    // A numeric part has no string.
    let fresh = nat.num(9);
    assert_eq!(fresh.to_string(), "Nat.9");
    assert!(fresh.last_str().is_none());
    assert_eq!(fresh.len(), 2);
    assert_eq!(fresh.prefix(), Some(&nat));

    // Append with the anonymous name on either side is the identity.
    assert_eq!(nat.append(&anonymous), nat);
    assert_eq!(anonymous.append(&nat), nat);
    // Append walks a numeric part too.
    assert_eq!(nat.append(&Name::anonymous().num(3)).to_string(), "Nat.3");
}

#[test]
fn a_prefix_test_handles_both_answers() {
    let nat = Name::from_dotted("Nat");
    let succ = Name::from_dotted("Nat.succ");
    let other = Name::from_dotted("Int.succ");
    assert!(nat.is_prefix_of(&succ));
    assert!(nat.is_prefix_of(&nat));
    assert!(!succ.is_prefix_of(&nat));
    assert!(!nat.is_prefix_of(&other));
    assert!(Name::anonymous().is_prefix_of(&succ));
}
