//! The second ground truth fixture, and the one that settled chapter 15.
//!
//! `Nat.add_succ.ndjson` is one real module, so it only covers what that one
//! module needed. `shapes.ndjson` was generated on purpose to cover the rest:
//! a mutual inductive group, a nested inductive, all four quotient constants,
//! a structure, a `let`, and a `Nat` literal.
//!
//! See `fixtures/lean4export/PROVENANCE.md` for how it was built.

use rean_core::Name;
use rean_export::read_module;
use rean_kernel::{Declaration, Environment, QuotKind, TypeChecker};

const FIXTURE: &str = "../../fixtures/lean4export/shapes.ndjson";

fn module() -> rean_export::Module {
    read_module(FIXTURE).expect("the fixture must read")
}

fn inductive_named(m: &rean_export::Module, name: &str) -> rean_kernel::InductiveVal {
    match m.env.get(&Name::from_dotted(name)) {
        Some(Declaration::Inductive(i)) => i.clone(),
        other => panic!("{name} must be an inductive, got {other:?}"),
    }
}

fn recursor_named(m: &rean_export::Module, name: &str) -> rean_kernel::RecursorVal {
    match m.env.get(&Name::from_dotted(name)) {
        Some(Declaration::Recursor(r)) => r.clone(),
        other => panic!("{name} must be a recursor, got {other:?}"),
    }
}

#[test]
fn the_fixture_uses_the_newer_format_version() {
    let m = module();
    assert_eq!(m.meta.format_version, "3.1.0");
    assert_eq!(m.meta.lean_version, "4.30.0");
    // 3.1.0 spells the inductive fields `types`, `ctors`, and `recs`, where
    // 3.0.0 spells them `inductiveVals` and so on. The reader takes either,
    // and both fixtures prove it.
    assert_eq!(m.order.len(), 63);
}

/// **The test that settled chapter 15.**
///
/// Chapter 15 derived the shape of a mutual recursor by reading, with no ground
/// truth to check it against. This is that check.
#[test]
fn a_real_mutual_recursor_has_the_shape_chapter_7_predicted() {
    let m = module();
    let tree = inductive_named(&m, "Tree");
    let forest = inductive_named(&m, "Forest");

    // Both types name the whole group, in one order.
    let group: Vec<String> = tree.all.iter().map(ToString::to_string).collect();
    assert_eq!(group, vec!["Tree", "Forest"]);
    assert_eq!(forest.all, tree.all);
    assert_eq!(tree.ctors.len(), 1, "Tree.node");
    assert_eq!(forest.ctors.len(), 2, "Forest.nil and Forest.cons");

    for name in ["Tree.rec", "Forest.rec"] {
        let rec = recursor_named(&m, name);
        // One motive per type in the group.
        assert_eq!(rec.num_motives, 2, "{name}");
        // One minor premise per constructor of BOTH types, because the
        // induction is simultaneous.
        assert_eq!(rec.num_minors, 3, "{name}");
    }

    // Only the type it takes apart has iota rules, because only its
    // constructors can be the major premise.
    let tree_rec = recursor_named(&m, "Tree.rec");
    assert_eq!(tree_rec.rules.len(), 1);
    assert_eq!(tree_rec.rules[0].ctor.to_string(), "Tree.node");
    let forest_rec = recursor_named(&m, "Forest.rec");
    assert_eq!(forest_rec.rules.len(), 2);
}

/// And the shape that chapter 15 got **wrong**.
#[test]
fn a_nested_recursor_speaks_about_a_type_that_is_not_exported() {
    let m = module();
    let rose = inductive_named(&m, "Rose");
    assert_eq!(rose.num_nested, 1);
    // Its group lists one type.
    assert_eq!(rose.all.len(), 1);

    // And its recursor reports two motives. The second is for the auxiliary
    // type that Lean builds for the nesting and never exports.
    let rec = recursor_named(&m, "Rose.rec");
    assert_eq!(rec.num_motives, 2, "two motives for a group of one");
    assert_eq!(rec.all.len(), 1);

    // The second recursor has rules for `List`, which is in no type of its
    // own group.
    let aux = recursor_named(&m, "Rose.rec_1");
    let rule_owners: Vec<String> = aux.rules.iter().map(|r| r.ctor.to_string()).collect();
    assert_eq!(rule_owners, vec!["List.nil", "List.cons"]);
    assert!(!aux.all.iter().any(|n| n.to_string() == "List"));

    // So every group check of chapter 15 would fire on a correct declaration,
    // and a nested recursor is trusted instead. That is the one place the
    // checker still takes a recursor on faith.
}

#[test]
fn all_four_quotient_constants_arrive() {
    let m = module();
    let kind_of = |name: &str| match m.env.get(&Name::from_dotted(name)) {
        Some(Declaration::Quot(q)) => q.kind,
        other => panic!("{name} must be a quot, got {other:?}"),
    };
    assert_eq!(kind_of("Quot"), QuotKind::Type);
    assert_eq!(kind_of("Quot.mk"), QuotKind::Ctor);
    assert_eq!(kind_of("Quot.lift"), QuotKind::Lift);
    assert_eq!(kind_of("Quot.ind"), QuotKind::Ind);
}

#[test]
fn the_reader_keeps_a_mutual_group_on_one_line() {
    // A mutual group's members refer to each other, so a checker must see all
    // of them at once. The export format puts them on one line for that
    // reason, and the reader records the grouping.
    let m = module();
    let with_tree = m
        .groups
        .iter()
        .find(|group| group.iter().any(|n| n.to_string() == "Tree"))
        .expect("Tree must be in a group");
    let names: Vec<String> = with_tree.iter().map(ToString::to_string).collect();
    for wanted in [
        "Tree",
        "Forest",
        "Tree.node",
        "Forest.nil",
        "Forest.cons",
        "Tree.rec",
        "Forest.rec",
    ] {
        assert!(names.contains(&wanted.to_string()), "missing {wanted}");
    }
}

/// **The headline.** Our kernel checks every declaration of this module too.
#[test]
fn our_kernel_checks_every_declaration() {
    let m = module();
    let mut known = Environment::new();
    let mut failures = Vec::new();

    for group in &m.groups {
        let decls: Vec<Declaration> = group
            .iter()
            .filter_map(|name| m.env.get(name).cloned())
            .collect();
        let mut accepted = Vec::new();
        for name in group {
            let decl = m.env.get(name).expect("every name resolves");
            let mut tc = TypeChecker::new(&known);
            match tc.with_group(&decls, |tc| tc.check_declaration(decl)) {
                Ok(()) => accepted.push(decl.clone()),
                Err(err) => failures.push(format!("{name}: {}", err.render(tc.lctx()))),
            }
        }
        for decl in accepted {
            known.add(decl);
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} failed:\n{}",
        failures.len(),
        m.order.len(),
        failures.join("\n")
    );
}

#[test]
fn the_literal_theorem_checks() {
    // `theorem twoAddThree : 2 + 3 = 5 := rfl`. This needs δ through the
    // instance chain, ι on `Nat.rec`, a projection, and direct arithmetic on
    // two literals. Chapter 12 added the last piece.
    let m = module();
    let decl = m
        .env
        .get(&Name::from_dotted("twoAddThree"))
        .expect("the theorem is there");
    assert_eq!(decl.kind_label(), "theorem");
    let value = decl.value().expect("a theorem has a proof");
    // `check_declaration` would refuse this, because the environment already
    // holds the name. So check the proof against the proposition directly.
    let mut tc = TypeChecker::new(&m.env);
    tc.check(value, decl.ty())
        .unwrap_or_else(|err| panic!("2 + 3 = 5 must check: {}", err.render(tc.lctx())));
}

#[test]
fn nothing_in_this_module_rests_on_an_axiom() {
    let m = module();
    for name in &m.order {
        let axioms = m.env.axioms_of(name);
        assert!(axioms.is_empty(), "{name} rests on {axioms:?}");
    }
}
