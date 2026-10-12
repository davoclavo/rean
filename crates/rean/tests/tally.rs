//! The tally, switched on, over a committed fixture.
//!
//! `rean_kernel::tally` is off in a normal test run, so its own unit tests can
//! only check the shape of the thing. This file sets the variable and runs the
//! real binary, which is the only way to see a count come out.
//!
//! The chapters have written an instrument three times and deleted it three
//! times. This is the test that the fourth one keeps.

use std::process::{Command, Output};

/// Runs the driver over the shapes fixture with a budget too small to finish.
///
/// A tally is printed for a declaration that **failed**, and every declaration
/// of the fixture passes at the normal budget. So the budget is cut to two
/// hundred units, which fails on the recursors and prints the rules that fired
/// before it ran out. The number is not the point; the rows are.
fn run_with_a_tiny_budget(tally: bool) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_rean"));
    command
        .args(["check", "../../fixtures/lean4export/shapes.ndjson"])
        .env("REAN_FUEL", "200");
    if tally {
        command.env("REAN_TALLY", "1");
    } else {
        command.env_remove("REAN_TALLY");
    }
    command.output().expect("the binary must run")
}

#[test]
fn the_tally_names_the_rules_that_fired() {
    let out = run_with_a_tiny_budget(true);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    // The budget is spent, so there is a failure to report the tally of.
    assert!(text.contains("units of work"), "{text}");
    // A recursor check reduces, and most of those steps fire no rule. The
    // tally names that too, because a rule that never fires is an answer: it
    // says the cost is elsewhere.
    assert!(text.contains("no rule applies"), "{text}");
    // And the stack line, which says how close the other limit came.
    assert!(text.contains("most stack used:"), "{text}");
}

#[test]
fn a_run_without_the_variable_prints_no_tally() {
    let out = run_with_a_tiny_budget(false);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    // The failure is still reported. Only the rows are gone.
    assert!(text.contains("units of work"), "{text}");
    assert!(!text.contains("no rule applies"), "{text}");
    assert!(!text.contains("most stack used:"), "{text}");
}
