//! Tests that run the real binary.
//!
//! `main.rs` is pure printing, so no unit test can reach it. These tests spawn
//! the built binary instead, which is the only way to cover a `main`.

use std::process::{Command, Output};

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rean"))
        .args(args)
        .output()
        .expect("the binary must run")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn no_argument_prints_the_usage() {
    let out = run(&[]);
    assert!(out.status.success());
    assert!(stdout(&out).contains("usage:"));
}

#[test]
fn help_prints_the_usage() {
    for flag in ["help", "--help", "-h"] {
        let out = run(&[flag]);
        assert!(out.status.success(), "{flag} must succeed");
        assert!(stdout(&out).contains("rean - a Lean compiler in Rust"));
    }
}

#[test]
fn an_unknown_command_fails_with_the_usage() {
    let out = run(&["wat"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("unknown command `wat`"));
    assert!(stderr(&out).contains("usage:"));
}

#[test]
fn lex_prints_the_tokens_of_a_clean_file() {
    let out = run(&["lex", "../../examples/tokens.lean"]);
    assert!(out.status.success());
    let text = stdout(&out);
    assert!(text.contains("tokens, no error"));
    assert!(text.contains("keyword"));
    assert!(text.contains("nat"));
}

#[test]
fn lex_fails_on_the_file_that_fails_on_purpose() {
    let out = run(&["lex", "../../examples/notation.lean"]);
    assert!(!out.status.success(), "notation.lean must report errors");
    assert!(stdout(&out).contains("3 error(s)"));
}

#[test]
fn lex_without_a_path_fails() {
    let out = run(&["lex"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("lex needs a path"));
}

#[test]
fn lex_with_a_missing_file_fails() {
    let out = run(&["lex", "../../nope.lean"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("cannot read"));
}

#[test]
fn check_passes_the_fixture() {
    let out = run(&["check", "../../fixtures/lean4export/Nat.add_succ.ndjson"]);
    assert!(out.status.success(), "{}", stdout(&out));
    let text = stdout(&out);
    assert!(text.contains("level 1: checked 32 of 32 declarations"));
    assert!(text.contains("ok    theorem    Nat.add_succ"));
    assert!(text.contains("lean4export 3.0.0"));
}

#[test]
fn check_without_a_path_fails() {
    let out = run(&["check"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("check needs a path"));
}

#[test]
fn check_with_a_bad_file_fails() {
    let out = run(&["check", "../../examples/twice.lean"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("cannot read"));
}

#[test]
fn prove_accepts_the_identity() {
    let out = run(&["prove"]);
    assert!(out.status.success());
    let text = stdout(&out);
    assert!(text.contains("accepted. The proposition holds."));
    assert!(text.contains("the proposition lives in : Prop"));
    assert!(text.contains("type mismatch"));
}

#[test]
fn demo_walks_the_stages() {
    let out = run(&["demo"]);
    assert!(out.status.success());
    let text = stdout(&out);
    assert!(text.contains("== stage 1: tokens =="));
    assert!(text.contains("== stage 4: one beta step =="));
}

#[test]
fn check_reports_a_declaration_that_fails() {
    // A file whose one declaration cannot check. The report must name it, show
    // the reason, and exit with a failure.
    let meta = r#"{"meta":{"exporter":{"name":"x","version":"3.0.0"},"format":{"version":"3.0.0"},"lean":{"version":"4"}}}"#;
    // Term 0 is a loose bound variable, which is not a type.
    let text = format!(
        "{meta}\n\
         {{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"Broken\"}}}}\n\
         {{\"ie\":0,\"bvar\":0}}\n\
         {{\"axiom\":{{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}}}\n"
    );
    let path = std::env::temp_dir().join("rean-cli-broken.ndjson");
    std::fs::write(&path, text).expect("the temporary file must write");

    let out = run(&["check", path.to_str().unwrap()]);
    assert!(
        !out.status.success(),
        "a failing declaration must fail the run"
    );
    let text = stdout(&out);
    assert!(text.contains("FAIL  axiom      Broken"), "{text}");
    assert!(text.contains("points outside the term"), "{text}");
    assert!(
        text.contains("level 1: checked 0 of 1 declarations"),
        "{text}"
    );

    let _ = std::fs::remove_file(&path);
}
