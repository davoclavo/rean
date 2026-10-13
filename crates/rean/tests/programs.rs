//! Real programs, run end to end.
//!
//! `frontdoor.rs` tests the handover between Lean and us. This tests the thing
//! the handover is **for**: a program somebody would write, with an algorithm
//! in it, checked by our kernel and run by our evaluator.
//!
//! Every expected line was compared with Lean's own `#eval main`. That is the
//! only oracle that settles whether a value is right, and chapter 19 says so.
//!
//! The file skips itself when no Lean is installed, for the reason the front
//! door tests give: a test that fails for a missing tool teaches a reader to
//! ignore a red test.

use rean::export::Toolchain;
use std::path::PathBuf;
use std::process::{Command, Output};

/// Insertion sort, a binary search tree, and primes by trial division.
///
/// Nothing here is written for the evaluator. It is the way anybody writes
/// these, which is the point: `if`, `match`, `++`, `filter`, `all`, `&&`, `%`,
/// `foldl`, a `do` block and `s!` interpolation all have to work.
const PROGRAM: &str = r#"
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (sort xs)

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

def Tree.insert (t : Tree) (x : Nat) : Tree :=
  match t with
  | .leaf => .node .leaf x .leaf
  | .node l v r => if x < v then .node (l.insert x) v r else .node l v (r.insert x)

def Tree.toList : Tree → List Nat
  | .leaf => []
  | .node l v r => l.toList ++ v :: r.toList

def numbers : List Nat := [37, 2, 19, 5, 23, 11, 3, 29, 7, 13]

def sorted : List Nat := sort numbers

def viaTree : List Nat := (numbers.foldl Tree.insert .leaf).toList

def primesUnder (n : Nat) : List Nat :=
  (List.range n).filter (fun k => k ≥ 2 && (List.range k).all (fun d => d < 2 || k % d != 0))

def main : IO Unit := do
  IO.println s!"sorted   = {sorted}"
  IO.println s!"viaTree  = {viaTree}"
  IO.println s!"primes   = {primesUnder 30}"
  IO.println s!"sum      = {numbers.foldl (· + ·) 0}"
  IO.println s!"length   = {sorted.length}"
"#;

fn work_dir(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rean-programs-{}-{test}", std::process::id()));
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
fn a_program_with_algorithms_in_it() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("algorithms");
    std::fs::write(dir.join("Real.lean"), PROGRAM).expect("the source must be written");

    let out = run(&["run", "Real.lean", "main", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let errors = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(out.status.success(), "stdout:\n{text}\nstderr:\n{errors}");

    // Our kernel checked every declaration the program rests on, and none of
    // them failed. A program that runs on an unchecked term is not what this
    // project is for.
    assert!(text.contains("level 1: checked"), "{text}");
    assert!(!text.contains("failed"), "{text}");

    let lines: Vec<&str> = text
        .lines()
        .skip_while(|line| !line.starts_with("sorted"))
        .take(5)
        .collect();
    assert_eq!(
        lines,
        vec![
            "sorted   = [2, 3, 5, 7, 11, 13, 19, 23, 29, 37]",
            "viaTree  = [2, 3, 5, 7, 11, 13, 19, 23, 29, 37]",
            "primes   = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]",
            "sum      = 149",
            "length   = 10",
        ],
        "{text}"
    );
    assert!(text.contains("main ran"), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_value_and_not_a_program_prints_its_value() {
    if Toolchain::find().is_err() {
        eprintln!("skipped: no lean and lean4export. See the module comment.");
        return;
    }
    let dir = work_dir("value");
    std::fs::write(dir.join("Real.lean"), PROGRAM).expect("the source must be written");

    // `sorted` has no `IO` in its type, so it is a value: nothing is run
    // against a world, and the list is printed.
    let out = run(&["run", "Real.lean", "sorted", "--out", "."], &dir);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(out.status.success(), "{text}");
    assert!(
        text.contains("sorted = [2, 3, 5, 7, 11, 13, 19, 23, 29, 37]"),
        "{text}"
    );
    assert!(!text.contains("ran"), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}
