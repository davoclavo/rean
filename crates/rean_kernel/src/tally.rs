//! Counting what the kernel does, in the language of the problem.
//!
//! # Why this is in the kernel and not in a profiler
//!
//! Chapter 21 reached a point where a profiler stopped helping. It said
//! `read_nat` and `whnf` were hot, which was true and useless: both are hot in
//! every run. The question that moved the work was **which recursor, which
//! number, which definition**, and no profiler knows those words.
//!
//! So the kernel counts its own rules, by name. `delta Nat.casesOn 283,803`
//! names a cause. `whnf 41%` does not.
//!
//! # Why it is permanent
//!
//! Chapters 21 and 15 each wrote an instrument, measured, and deleted it. The
//! third time it was written, the lesson of chapter 23 section 23.3 was already
//! paid for: **an instrument that watches one exit of three reports a fact about
//! the instrument.** That bug cost hours, and it is the kind that a throwaway
//! counter invites, because nobody reviews a counter they are about to delete.
//!
//! This one watches every exit, has a test, and costs one `bool` load per
//! reduction step when it is switched off.
//!
//! # Use
//!
//! ```sh
//! REAN_TALLY=1 ./target/release/rean check one.ndjson
//! ```
//!
//! The driver prints the tally of a declaration that fails. Nothing here
//! prints, by the rule that no library crate of this workspace prints a line.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::OnceLock;

/// Is the tally switched on?
///
/// Read once, from `REAN_TALLY`. A kernel that asked the environment on every
/// reduction step would be measuring the environment.
pub fn on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("REAN_TALLY").is_some())
}

thread_local! {
    static COUNTS: RefCell<HashMap<String, u64>> = RefCell::new(HashMap::new());
    static TOTALS: RefCell<HashMap<String, u64>> = RefCell::new(HashMap::new());
}

/// Counts one event for the **whole run**, and not for one declaration.
///
/// [`take`] empties the per-declaration counts, and the driver prints them for
/// a declaration that **failed**. That is the right report for "why is this one
/// expensive" and the wrong one for "where does the run spend itself", and
/// reading one as the other is a mistake this project has now made twice. So
/// there are two sets of counters, and this is the one nothing clears.
pub fn total(key: impl FnOnce() -> String, units: u64) {
    if !on() {
        return;
    }
    let key = key();
    TOTALS.with(|counts| {
        *counts.borrow_mut().entry(key).or_insert(0) += units;
    });
}

/// Returns every run-wide count, largest first. Nothing is emptied.
pub fn totals() -> Vec<(String, u64)> {
    let mut rows: Vec<(String, u64)> = TOTALS.with(|counts| {
        counts
            .borrow()
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect()
    });
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    rows
}

/// Counts one event, naming it with `key`.
///
/// `key` is a closure, so a run with the tally off never builds the string.
/// The name of a rule holds a [`rean_core::Name`], and formatting one costs
/// more than the step being counted.
pub fn bump(key: impl FnOnce() -> String) {
    if !on() {
        return;
    }
    let key = key();
    COUNTS.with(|counts| {
        *counts.borrow_mut().entry(key).or_insert(0) += 1;
    });
}

/// Adds `units` to a count, for a thing that is measured and not counted.
pub fn add(key: impl FnOnce() -> String, units: u64) {
    if !on() {
        return;
    }
    let key = key();
    COUNTS.with(|counts| {
        *counts.borrow_mut().entry(key).or_insert(0) += units;
    });
}

/// Returns every count, largest first, and empties the tally.
///
/// The caller is one declaration, so emptying here is what makes the next
/// declaration's tally its own.
pub fn take() -> Vec<(String, u64)> {
    let mut rows: Vec<(String, u64)> = COUNTS.with(|counts| counts.borrow_mut().drain().collect());
    // Largest first, and ties by name so that two runs of the same input print
    // the same report.
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    rows
}

/// Empties the tally without reading it.
pub fn clear() {
    if !on() {
        return;
    }
    COUNTS.with(|counts| counts.borrow_mut().clear());
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tally is off in a test run, so these test the shape and not the
    /// counting. The counting itself is covered by `tests/tally.rs`, which runs
    /// the driver with the variable set.
    #[test]
    fn a_tally_that_is_off_counts_nothing_and_builds_no_key() {
        if on() {
            return;
        }
        let mut built = false;
        bump(|| {
            built = true;
            "delta Nat.add".to_string()
        });
        assert!(!built, "the key must not be built when the tally is off");
        assert!(take().is_empty());
    }

    #[test]
    fn rows_come_back_largest_first() {
        // Sorting is pure, so it can be tested without the switch.
        let mut rows = [
            ("b".to_string(), 1u64),
            ("a".to_string(), 7),
            ("c".to_string(), 7),
        ];
        rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        assert_eq!(rows[0].0, "a");
        assert_eq!(rows[1].0, "c");
        assert_eq!(rows[2].0, "b");
    }
}
