//! Tests for the driver.
//!
//! Each command returns a value, so a test can read it. That is the whole
//! reason the driver is a library and not only a binary.

use rean::{DEFAULT_STACK_MIB, USAGE, check_export, demo, lex_file, prove, stack_bytes};

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
    assert_eq!(report.blocked(), 0);
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
        .find(|o| o.verdict != rean::Verdict::Ok)
        .map(|o| format!("{}: {:?}", o.name, o.verdict))
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

// --- the two knobs, and why they are coupled -----------------------------

#[test]
fn the_stack_size_reads_a_number_of_mebibytes() {
    assert_eq!(stack_bytes(Some("1024")), 1024 * 1024 * 1024);
    // Whitespace comes free with a shell variable.
    assert_eq!(stack_bytes(Some(" 64 ")), 64 * 1024 * 1024);
}

#[test]
fn a_stack_size_nobody_wrote_is_the_default() {
    let default = DEFAULT_STACK_MIB * 1024 * 1024;
    // Not set at all.
    assert_eq!(stack_bytes(None), default);
    // A typo in a variable must not stop a sweep, and must not be read as a
    // number nobody wrote.
    assert_eq!(stack_bytes(Some("lots")), default);
    assert_eq!(stack_bytes(Some("")), default);
    // Zero would be a stack of no size.
    assert_eq!(stack_bytes(Some("0")), default);
}

#[test]
fn the_usage_text_names_both_knobs_and_their_coupling() {
    // A reader who raises the budget and then meets a stack overflow has been
    // failed by this text. See chapter 17, section 17.8.
    assert!(USAGE.contains("REAN_FUEL"), "{USAGE}");
    assert!(USAGE.contains("REAN_STACK"), "{USAGE}");
    assert!(USAGE.contains("needs more stack to reduce"), "{USAGE}");
    // And the kernel's answer to running out: a report, not a crash.
    assert!(USAGE.contains("rather than crashing"), "{USAGE}");
}

#[test]
fn the_usage_text_names_the_three_kinds_of_target() {
    // The front door of chapter 24. A reader who does not know that `prelude`
    // is a target will never type it.
    assert!(USAGE.contains(".ndjson"), "{USAGE}");
    assert!(USAGE.contains("Demo.lean"), "{USAGE}");
    assert!(USAGE.contains("prelude"), "{USAGE}");
    assert!(USAGE.contains("--decl"), "{USAGE}");
    // And it must say whose elaborator did the work, or the reader will think
    // this project has a parser.
    assert!(USAGE.contains("stage 4 is ours"), "{USAGE}");
}
