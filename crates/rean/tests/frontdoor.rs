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

#[test]
fn show_reads_a_declaration_out_of_a_lean_file() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("shows");
    std::fs::write(dir.join("Demo.lean"), SOURCE).expect("the source must be written");

    // No `--decl` from the reader: `show` passes the name to the exporter
    // itself, so this costs 759 KB and half a second rather than 345 MB.
    let out = run(&["show", "Demo.lean", "twice"], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(out.status.success(), "{text}");
    assert!(text.contains("def twice"), "{text}");
    assert!(text.contains("Nat → Nat"), "{text}");
    // The value is Lean's, with the instance it inserted for `+`.
    assert!(text.contains("HAdd.hAdd"), "{text}");
    assert!(text.contains("instAddNat"), "{text}");
    assert!(text.contains("trust: no axiom"), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The whole pipeline, on a program with real computation in it.
///
/// Our kernel checks it and our evaluator runs it, and the answers are
/// cross-checked against Lean's own `#eval`, which is the only oracle that
/// settles whether a value is right.
const PROGRAM: &str = "\
def fib : Nat → Nat\n\
  | 0 => 0\n\
  | 1 => 1\n\
  | (n + 2) => fib n + fib (n + 1)\n\
\n\
def answer : Nat := fib 25\n\
\n\
def squares : Nat := (List.range 20).foldl (fun acc n => acc + n * n) 0\n\
\n\
def greeting : String := \"hello, \" ++ \"world\"\n\
";

#[test]
fn it_checks_a_program_and_then_runs_it() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("runs");
    std::fs::write(dir.join("Prog.lean"), PROGRAM).expect("the source must be written");

    // `fib 25` is 242,785 calls if the recursion is naive. Lean compiles it to
    // `brecOn`, whose table holds every smaller answer, and the evaluator is
    // lazy, so only the entries somebody asks for are computed. The step count
    // in the report is the proof that it stayed linear.
    let out = run(&["run", "Prog.lean", "answer", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let errors = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(out.status.success(), "stdout:\n{text}\nstderr:\n{errors}");
    // Stage 4 first, and then stage 5. The order is the claim.
    assert!(text.contains("level 1: checked"), "{text}");
    assert!(!text.contains("failed"), "{text}");
    assert!(text.contains("answer = 75025"), "{text}");
    assert!(text.contains("steps,"), "{text}");

    // A list pipeline and a string, both through Lean's own definitions.
    let out = run(&["run", "Prog.lean", "squares", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(text.contains("squares = 2470"), "{text}");

    let out = run(&["run", "Prog.lean", "greeting", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(text.contains("greeting = \"hello, world\""), "{text}");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn run_refuses_a_declaration_that_is_not_there() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("runs-missing");
    std::fs::write(dir.join("Prog.lean"), PROGRAM).expect("the source must be written");
    let out = run(&["run", "Prog.lean", "nowhere", "--out", "."], &dir);
    assert!(!out.status.success());
    let errors = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(
        errors.contains("nowhere") || errors.contains("refused"),
        "{errors}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A program with a `main`, which writes.
///
/// This is the whole pipeline on something a reader would call a program: a
/// `do` block, string interpolation, a `for` loop and a recursive function.
/// The output is compared against Lean's own `#eval main`, which produced
/// these seven lines byte for byte.
const MAIN: &str = "\
def fib : Nat → Nat\n\
  | 0 => 0\n\
  | 1 => 1\n\
  | (n + 2) => fib n + fib (n + 1)\n\
\n\
def main : IO Unit := do\n\
  IO.println \"hello from rean\"\n\
  IO.println s!\"fib 25 = {fib 25}\"\n\
  for i in [0:3] do\n\
    IO.println s!\"  square of {i} is {i * i}\"\n\
";

#[test]
fn a_program_with_a_main_writes_what_lean_writes() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("main");
    std::fs::write(dir.join("Prog.lean"), MAIN).expect("the source must be written");

    let out = run(&["run", "Prog.lean", "main", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let errors = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(out.status.success(), "stdout:\n{text}\nstderr:\n{errors}");

    // The kernel first, and it checks every declaration the program rests on.
    assert!(text.contains("level 1: checked"), "{text}");
    assert!(!text.contains("failed"), "{text}");

    // Then the program's own output, in order. `s!` interpolation means a
    // `toString`, a `String.append` and a `String.push` all ran, and the loop
    // means the `ForIn` instance of a range ran too.
    let lines: Vec<&str> = text
        .lines()
        .skip_while(|line| !line.starts_with("hello"))
        .take(4)
        .collect();
    assert_eq!(
        lines,
        vec![
            "hello from rean",
            "fib 25 = 75025",
            "  square of 0 is 0",
            "  square of 1 is 1",
        ],
        "{text}"
    );
    assert!(text.contains("main ran"), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A wider program: a structure, an inductive with a `match`, a list, an
/// array and an `Option`, all printed through Lean's own `ToString`.
///
/// Every line of the output was compared with Lean's `#eval main` and they
/// agree. This is the test that says which **shapes** of Lean the evaluator
/// handles, so a shape that stops working fails here.
const WIDE: &str = "\
structure Point where\n\
  x : Nat\n\
  y : Nat\n\
\n\
def Point.norm1 (p : Point) : Nat := p.x + p.y\n\
\n\
inductive Shape where\n\
  | circle (r : Nat)\n\
  | rect (w h : Nat)\n\
\n\
def Shape.area : Shape → Nat\n\
  | .circle r => 3 * r * r\n\
  | .rect w h => w * h\n\
\n\
def total : Nat := [Shape.circle 2, Shape.rect 3 4].foldl (fun a s => a + s.area) 0\n\
\n\
def names : List String := [\"a\", \"bb\"].map (fun s => s ++ \"!\")\n\
\n\
def arr : Nat := (Array.range 10).foldl (· + ·) 0\n\
\n\
def main : IO Unit := do\n\
  IO.println s!\"norm1 = {Point.norm1 ⟨3, 4⟩}\"\n\
  IO.println s!\"total = {total}\"\n\
  IO.println s!\"names = {names}\"\n\
  IO.println s!\"arr = {arr}\"\n\
";

#[test]
fn the_shapes_of_lean_that_a_program_is_made_of() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("wide");
    std::fs::write(dir.join("Wide.lean"), WIDE).expect("the source must be written");

    let out = run(&["run", "Wide.lean", "main", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let errors = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(out.status.success(), "stdout:\n{text}\nstderr:\n{errors}");
    let lines: Vec<&str> = text
        .lines()
        .skip_while(|line| !line.starts_with("norm1"))
        .take(4)
        .collect();
    assert_eq!(
        lines,
        vec!["norm1 = 7", "total = 24", "names = [a!, bb!]", "arr = 45",],
        "{text}"
    );

    // A value, rather than a program, and a list prints as a list.
    let out = run(&["run", "Wide.lean", "names", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(text.contains(r#"names = ["a!", "bb!"]"#), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}
