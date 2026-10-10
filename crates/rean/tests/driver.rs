//! Tests for the driver.
//!
//! Each command returns a value, so a test can read it. That is the whole
//! reason the driver is a library and not only a binary.

use rean::{USAGE, check_export, demo, lex_file, prove};

const FIXTURE: &str = "../../fixtures/lean4export/Nat.add_succ.ndjson";

// --- lex -------------------------------------------------------------------

#[test]
fn lex_reads_a_clean_example() {
    let report = lex_file("../../examples/twice.lean").expect("the file must read");
    assert_eq!(report.error_count, 0);
    assert!(report.token_count > 50);
    assert!(report.diagnostics.is_empty());
    // Each line carries a position, a kind, and the text.
    assert!(report.lines[0].contains("1:1"));
    assert!(report.lines.iter().any(|l| l.contains("keyword")));
}

#[test]
fn lex_reports_the_three_unknown_symbols() {
    // `notation.lean` fails on purpose. See its own doc comment.
    let report = lex_file("../../examples/notation.lean").expect("the file must read");
    assert_eq!(report.error_count, 3);
    assert!(report.diagnostics.contains("unexpected character"));
}

#[test]
fn lex_reports_a_missing_file() {
    let err = lex_file("../../examples/does-not-exist.lean").unwrap_err();
    assert!(err.contains("cannot read"), "{err}");
}

// --- check -----------------------------------------------------------------

#[test]
fn check_passes_the_whole_fixture() {
    let report = check_export(FIXTURE).expect("the fixture must read");
    assert_eq!(
        report.meta,
        "lean4export 3.0.0, format 3.0.0, Lean 4.27.0-rc1"
    );
    assert_eq!(report.outcomes.len(), 32);
    assert_eq!(report.failed(), 0, "{:#?}", first_failure(&report));
    assert_eq!(report.passed(), 32);
    assert_eq!(report.score(), "level 1: checked 32 of 32 declarations");
}

#[test]
fn check_names_every_kind_of_declaration() {
    let report = check_export(FIXTURE).unwrap();
    let kinds: std::collections::BTreeSet<&str> = report.outcomes.iter().map(|o| o.kind).collect();
    assert!(kinds.contains("inductive"));
    assert!(kinds.contains("ctor"));
    assert!(kinds.contains("rec"));
    assert!(kinds.contains("def"));
    assert!(kinds.contains("theorem"));
    assert_eq!(report.outcomes.last().unwrap().name, "Nat.add_succ");
}

#[test]
fn check_reports_a_missing_file() {
    let err = check_export("../../fixtures/nope.ndjson").unwrap_err();
    assert!(err.contains("cannot read"), "{err}");
}

#[test]
fn check_reports_a_bad_file() {
    let err = check_export("../../examples/twice.lean").unwrap_err();
    assert!(err.contains("invalid JSON"), "{err}");
}

fn first_failure(report: &rean::CheckReport) -> Option<String> {
    report
        .outcomes
        .iter()
        .find(|o| o.error.is_some())
        .map(|o| format!("{}: {}", o.name, o.error.clone().unwrap()))
}

// --- prove -----------------------------------------------------------------

#[test]
fn prove_accepts_the_identity() {
    let report = prove();
    assert_eq!(report.proof, "fun (α : Prop) => fun (h : α) => h");
    assert_eq!(report.proposition, "(α : Prop) → α → α");
    assert_eq!(report.inferred, "(α : Prop) → α → α");
    assert!(report.rejected.is_none(), "{:?}", report.rejected);
    // `imax 1 0 = 0`, so the proposition is a `Prop` and not a `Type`.
    assert_eq!(report.lives_in, "Prop");
}

#[test]
fn prove_rejects_the_wrong_proof() {
    let report = prove();
    assert!(report.bad_proof_message.contains("type mismatch"));
    assert!(report.bad_proof_message.contains("expected"));
}

#[test]
fn prove_says_what_still_needs_an_environment() {
    let report = prove();
    assert_eq!(report.needs_environment.len(), 2);
    assert!(report.needs_environment[0].contains("unknown constant"));
}

// --- demo and usage --------------------------------------------------------

#[test]
fn demo_walks_all_four_stages() {
    let out = demo();
    for heading in [
        "== source ==",
        "== stage 1: tokens ==",
        "== stage 2: syntax tree",
        "== stage 3: kernel term ==",
        "== stage 4: one beta step ==",
        "== universe levels ==",
    ] {
        assert!(out.contains(heading), "missing {heading}");
    }
    // Stage 2 must produce a tree with no hole in it.
    assert!(out.contains("has a parse error: false"));
    // Stage 4 must show the beta step working.
    assert!(out.contains("after    : fun (x : Nat) => Nat.succ (Nat.succ x)"));
}

#[test]
fn the_usage_text_lists_every_command() {
    for command in ["lex", "check", "prove", "demo", "help"] {
        assert!(USAGE.contains(command), "usage must mention {command}");
    }
}
