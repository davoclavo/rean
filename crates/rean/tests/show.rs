//! `rean show`, over the two committed fixtures.
//!
//! The command answers the question a reader of these chapters asks most:
//! **what does Lean actually hand the kernel?** `demo` shows a term that was
//! built by hand, and a hand built term is always tidier than a real one.
//!
//! It is also an instrument. Chapter 25 was stuck on why one signed integer
//! proof costs a billion units of work, and three `rean show` calls answered
//! it. One of them found a bug in `Name::from_dotted` that had been quietly
//! emptying the trust report.

use rean::show;

const FIXTURE: &str = "../../fixtures/lean4export/Nat.add_succ.ndjson";
const SHAPES: &str = "../../fixtures/lean4export/shapes.ndjson";

#[test]
fn a_definition_shows_its_type_and_its_value() {
    let report = show(FIXTURE, "Nat.add", false).expect("the fixture holds Nat.add");
    assert_eq!(report.kind, "def");
    assert_eq!(report.name, "Nat.add");
    assert_eq!(report.ty, "Nat → Nat → Nat");
    // Nobody wrote this value. Lean's equation compiler did, and that is the
    // lesson: `Nat.add` is `brecOn` over a `match` helper.
    let value = report.value.expect("a def has a value");
    assert!(value.contains("Nat.brecOn"), "{value}");
    assert!(value.contains("Nat.add.match_1"), "{value}");
    assert!(report.axioms.is_empty());
}

#[test]
fn a_universe_polymorphic_declaration_shows_its_parameters() {
    let report = show(FIXTURE, "Nat.rec", false).expect("the fixture holds Nat.rec");
    assert_eq!(report.kind, "rec");
    assert_eq!(report.levels, "{u}");
    // A recursor has no value. It is a rule, not a definition.
    assert!(report.value.is_none());
}

#[test]
fn an_inductive_type_has_no_value_and_a_sort_for_a_type() {
    let report = show(SHAPES, "Tree", false).expect("shapes holds Tree");
    assert_eq!(report.kind, "inductive");
    assert!(report.value.is_none());
    assert!(
        report.ty.contains("Type") || report.ty.contains("Sort"),
        "{}",
        report.ty
    );
}

#[test]
fn the_constants_a_declaration_rests_on_are_counted() {
    let report = show(FIXTURE, "Nat.add_succ", false).expect("the fixture holds the theorem");
    assert_eq!(report.kind, "theorem");
    // The target theorem of the fixture rests on real machinery, and the
    // count is the point: a one line theorem is never one line underneath.
    assert!(report.uses.len() > 3, "{:?}", report.uses);
    assert!(
        report.uses.iter().any(|used| used == "Eq"),
        "{:?}",
        report.uses
    );
}

#[test]
fn a_name_that_is_nearly_right_gets_the_nearest_few() {
    // The common mistake, and refusing without help is the unhelpful answer.
    let err = show(FIXTURE, "Nat.add_suc", false).unwrap_err();
    assert!(err.contains("Did you mean"), "{err}");
    assert!(err.contains("Nat.add_succ"), "{err}");
}

#[test]
fn a_name_with_nothing_near_it_is_refused_plainly() {
    let err = show(FIXTURE, "Zzz", false).unwrap_err();
    assert!(err.contains("holds no declaration"), "{err}");
    // Two letters are too few to guess from, so no list is offered.
    assert!(!err.contains("Did you mean"), "{err}");
}

#[test]
fn a_long_value_is_cut_and_the_report_says_by_how_much() {
    // `Nat.brecOn.go` of the fixture is large enough to be cut at the default
    // limit, and `--full` must give all of it back.
    let cut = show(FIXTURE, "Nat.brecOn.go", false).expect("the fixture holds it");
    let full = show(FIXTURE, "Nat.brecOn.go", true).expect("the fixture holds it");
    let shown = cut.value.expect("a def has a value");
    let whole = full.value.expect("a def has a value");
    assert_eq!(full.value_cut, 0);
    if cut.value_cut > 0 {
        assert!(shown.len() < whole.len());
        assert_eq!(whole.len() - shown.len(), cut.value_cut);
    }
}

#[test]
fn a_missing_file_is_an_error_and_not_a_panic() {
    let err = show("nowhere.ndjson", "Nat.add", false).unwrap_err();
    assert!(err.contains("cannot read"), "{err}");
}
