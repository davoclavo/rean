//! The front door, driven for real: a `.lean` file, and a verdict.
//!
//! Every other test of this workspace runs on data that the repository holds.
//! This one needs the real Lean and `lean4export`, because the thing it tests
//! is the handover between them and us.
//!
//! So it **skips itself** when they are not installed, and prints why. A reader
//! who cloned this repository and has no Lean must still see a green run. A
//! test that fails for a missing tool teaches the reader to ignore a red test,
//! which is worse than no test.

use rean::export::Toolchain;
use std::path::PathBuf;
use std::process::{Command, Output};

/// One declaration, and a proof about it that the kernel must check by
/// computing. `twice 2` is `2 + 2`, so `rfl` only holds if δ, ι and the `Nat`
/// literal rule all work.
const SOURCE: &str = "def twice (n : Nat) : Nat := n + n\n\
                      \n\
                      theorem twice_two : twice 2 = 4 := rfl\n";

/// A directory of this test's own.
///
/// The name carries the test, and not only the process id. The three tests of
/// this file run in parallel in one process, and a shared directory made one
/// of them delete the file that another was still writing.
fn work_dir(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rean-frontdoor-{}-{test}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("the work directory must be there");
    dir
}

fn run(args: &[&str], dir: &PathBuf) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rean"))
        .args(args)
        .current_dir(dir)
        .output()
        .expect("the binary must run")
}

#[test]
fn a_lean_file_reaches_our_kernel() {
    let Ok(tools) = Toolchain::find() else {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    };
    let dir = work_dir("reaches");
    std::fs::write(dir.join("Demo.lean"), SOURCE).expect("the source must be written");

    // `--decl` keeps the export to this theorem and what it rests on. Without
    // it the exporter writes the whole prelude closure, which is 345 MB and
    // four minutes, and a test may not cost that.
    let out = run(
        &["check", "Demo.lean", "--decl", "twice_two", "--out", "."],
        &dir,
    );
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let errors = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(out.status.success(), "stdout:\n{text}\nstderr:\n{errors}");

    // The export line names the toolchain, because a measurement without a
    // version is not a measurement.
    assert!(text.contains("export: Demo ->"), "{text}");
    assert!(text.contains("by Lean "), "{text}");
    // Lean's own `Nat`, `HAdd` and `OfNat` come with it, and our kernel checks
    // every one of them. An independent checker that trusted them would be
    // checking nothing.
    assert!(text.contains("ok    theorem    twice_two"), "{text}");
    assert!(text.contains("ok    inductive  Nat"), "{text}");
    let score = text
        .lines()
        .find(|line| line.starts_with("level 1:"))
        .unwrap_or_default();
    assert!(score.contains("declarations"), "{text}");
    assert!(
        !score.contains("failed") && !score.contains("blocked"),
        "every declaration of this closure must check: {score}"
    );
    // Nothing here rests on an axiom, and the trust line must say so rather
    // than stay silent.
    assert!(
        text.contains("trust: no accepted declaration rests on an axiom"),
        "{text}"
    );

    // The export file stays. `rean check Demo.lean` exports again every time,
    // on purpose, because a stale export is a lie about the source; the file
    // is kept so that `rean check <that file>.ndjson` needs no Lean at all.
    assert!(dir.join("Demo.ndjson").is_file());
    assert!(tools.lean.is_file());
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn lean_refuses_a_bad_file_and_we_pass_its_message_on() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("refuses");
    std::fs::write(dir.join("Bad.lean"), "def bad : Nat := \"not a number\"\n")
        .expect("the source must be written");

    let out = run(&["check", "Bad.lean", "--out", "."], &dir);
    assert!(!out.status.success());
    let errors = String::from_utf8_lossy(&out.stderr).into_owned();
    // Lean's message, not ours. Our checker never saw the file, and a message
    // of our own would only hide the one that says what is wrong.
    assert!(errors.contains("lean refused"), "{errors}");
    assert!(errors.contains("Type mismatch"), "{errors}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn export_writes_the_file_and_checks_nothing() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("exports");
    std::fs::write(dir.join("Demo.lean"), SOURCE).expect("the source must be written");

    let out = run(
        &["export", "Demo.lean", "--decl", "twice_two", "--out", "."],
        &dir,
    );
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(out.status.success(), "{text}");
    assert!(text.contains("export: Demo ->"), "{text}");
    // No verdict, because nothing was checked.
    assert!(!text.contains("level 1:"), "{text}");
    assert!(dir.join("Demo.ndjson").is_file());
    let _ = std::fs::remove_dir_all(&dir);
}
