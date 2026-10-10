//! The level 1 checkpoint of `docs/ROADMAP.md`.
//!
//! Our kernel checks the real Lean's output. If this file fails, either our
//! kernel is wrong or the fixture changed.

use rean_core::Name;
use rean_export::{ExportError, read_module, read_str};
use rean_kernel::{Declaration, Environment, Expr, TypeChecker};

const FIXTURE: &str = "../../fixtures/lean4export/Nat.add_succ.ndjson";

fn module() -> rean_export::Module {
    read_module(FIXTURE).expect("the fixture must read")
}

#[test]
fn the_meta_line_reports_three_versions() {
    let m = module();
    assert_eq!(m.meta.exporter_name, "lean4export");
    assert_eq!(m.meta.format_version, "3.0.0");
    assert_eq!(m.meta.lean_version, "4.27.0-rc1");
    assert_eq!(
        m.meta.to_string(),
        "lean4export 3.0.0, format 3.0.0, Lean 4.27.0-rc1"
    );
}

#[test]
fn the_fixture_holds_every_kind_of_declaration() {
    let m = module();
    assert_eq!(m.order.len(), 32);
    let mut counts = std::collections::BTreeMap::new();
    for name in &m.order {
        let decl = m.env.get(name).expect("every name resolves");
        *counts.entry(decl.kind_label()).or_insert(0) += 1;
    }
    assert_eq!(counts["inductive"], 6);
    assert_eq!(counts["ctor"], 7);
    assert_eq!(counts["rec"], 6);
    assert_eq!(counts["def"], 12);
    assert_eq!(counts["theorem"], 1);
}

#[test]
fn the_names_come_back_hierarchical() {
    let m = module();
    assert!(m.env.contains(&Name::from_dotted("Nat.add_succ")));
    assert!(m.env.contains(&Name::from_dotted("Nat.add.match_1")));
    assert!(m.env.contains(&Name::from_dotted("Nat.brecOn.go")));
    // `Nat.add_succ` is the last declaration, because it depends on the rest.
    assert_eq!(
        m.order.last().map(Name::to_string).as_deref(),
        Some("Nat.add_succ")
    );
}

#[test]
fn the_recursor_arrives_with_its_iota_rules() {
    let m = module();
    let Some(Declaration::Recursor(rec)) = m.env.get(&Name::from_dotted("Nat.rec")) else {
        panic!("Nat.rec must be a recursor");
    };
    assert_eq!(rec.num_motives, 1);
    assert_eq!(rec.num_minors, 2);
    assert_eq!(rec.major_index(), 3);
    assert_eq!(rec.rules.len(), 2);
    assert!(rec.rule_for(&Name::from_dotted("Nat.zero")).is_some());
    assert!(rec.rule_for(&Name::from_dotted("Nat.succ")).is_some());
    // `Eq.rec` is K-like. We do not use that yet, but the flag arrives.
    let Some(Declaration::Recursor(eq)) = m.env.get(&Name::from_dotted("Eq.rec")) else {
        panic!("Eq.rec must be a recursor");
    };
    assert!(eq.k);
}

/// **The headline test.** Our kernel checks every declaration that Lean wrote.
///
/// The environment grows one declaration at a time, so a declaration can only
/// use the ones before it. A circular definition cannot slip through.
#[test]
fn our_kernel_checks_every_declaration_that_lean_wrote() {
    let m = module();
    let mut known = Environment::new();
    let mut failures = Vec::new();

    for name in &m.order {
        let decl = m.env.get(name).expect("every name resolves");
        let mut tc = TypeChecker::new(&known);
        if let Err(err) = tc.check_declaration(decl) {
            failures.push(format!("{name}: {}", err.render(tc.lctx())));
        }
        known.add(decl.clone());
    }

    assert!(
        failures.is_empty(),
        "level 1 regression, {} of {} failed:\n{}",
        failures.len(),
        m.order.len(),
        failures.join("\n")
    );
}

// --- the reductions that the theorem needs --------------------------------

#[test]
fn the_base_case_of_addition_reduces() {
    // `Nat.add n Nat.zero` must reduce to `n`. That needs δ then ι.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let n = Expr::FVar(tc.push_local("n", Expr::const_("Nat", vec![])));
    let term = Expr::const_("Nat.add", vec![]).apps([n.clone(), Expr::const_("Nat.zero", vec![])]);
    let reduced = tc.whnf(&term).expect("it must reduce");
    assert!(reduced.alpha_eq(&n), "got {}", tc.lctx().pretty(&reduced));
}

#[test]
fn the_step_case_of_addition_is_definitionally_equal() {
    // `n + Nat.succ m ≡ Nat.succ (n + m)`.
    //
    // This one needs the whole chain: δ through `HAdd.hAdd`, `instHAdd`,
    // `Add.add`, `instAddNat`, and `Nat.add`; then ι on `Nat.rec` inside
    // `Nat.brecOn`; then a projection out of a `PProd`.
    //
    // It is also the regression test for a projection at the head of an
    // application spine. Without that case in `is_def_eq`, this fails.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let nat = Expr::const_("Nat", vec![]);
    let n = Expr::FVar(tc.push_local("n", nat.clone()));
    let k = Expr::FVar(tc.push_local("m", nat));
    let succ = |x: Expr| Expr::const_("Nat.succ", vec![]).app(x);
    let add = |a: Expr, b: Expr| Expr::const_("Nat.add", vec![]).apps([a, b]);

    let left = add(n.clone(), succ(k.clone()));
    let right = succ(add(n, k));
    assert!(
        tc.is_def_eq(&left, &right).expect("no error"),
        "the two sides must be definitionally equal"
    );
}

#[test]
fn two_different_sums_are_not_equal() {
    // The checker must also say no. `n + succ m` is not `n + m`.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let nat = Expr::const_("Nat", vec![]);
    let n = Expr::FVar(tc.push_local("n", nat.clone()));
    let k = Expr::FVar(tc.push_local("m", nat));
    let succ = |x: Expr| Expr::const_("Nat.succ", vec![]).app(x);
    let add = |a: Expr, b: Expr| Expr::const_("Nat.add", vec![]).apps([a, b]);
    assert!(
        !tc.is_def_eq(&add(n.clone(), succ(k.clone())), &add(n, k))
            .expect("no error")
    );
}

#[test]
fn a_projection_out_of_a_constructor_reduces() {
    // `(PProd.mk α β a b).1` must reduce to `a`.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let nat = Expr::const_("Nat", vec![]);
    let a = Expr::FVar(tc.push_local("a", nat.clone()));
    let b = Expr::FVar(tc.push_local("b", nat.clone()));
    let one = rean_kernel::Level::of_nat(1);
    let pair =
        Expr::const_("PProd.mk", vec![one.clone(), one]).apps([nat.clone(), nat, a.clone(), b]);
    let first = Expr::Proj(rean_kernel::Proj {
        structure: Name::from_dotted("PProd"),
        index: 0,
        value: std::sync::Arc::new(pair),
    });
    let reduced = tc.whnf(&first).expect("it must reduce");
    assert!(reduced.alpha_eq(&a), "got {}", tc.lctx().pretty(&reduced));
}

// --- the reader refuses a bad file ----------------------------------------

#[test]
fn a_file_with_no_meta_line_is_refused() {
    let err = read_str("{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Nat\"}}\n").unwrap_err();
    assert_eq!(err, ExportError::NoMeta);
}

#[test]
fn an_unknown_format_version_is_refused() {
    let meta = r#"{"meta":{"exporter":{"name":"lean4export","version":"9.9.9"},"format":{"version":"9.9.9"},"lean":{"version":"9.9.9"}}}"#;
    let err = read_str(meta).unwrap_err();
    assert!(
        matches!(err, ExportError::UnknownFormat { .. }),
        "the reader must not guess at a format it does not know: {err}"
    );
    assert!(err.to_string().contains("3.0.0"));
}

#[test]
fn a_line_that_is_not_json_is_refused() {
    let err = read_str("not json\n").unwrap_err();
    assert!(matches!(err, ExportError::BadJson { line: 1, .. }), "{err}");
}

#[test]
fn a_reference_to_a_missing_index_is_refused() {
    let meta = r#"{"meta":{"exporter":{"name":"x","version":"3.0.0"},"format":{"version":"3.0.0"},"lean":{"version":"4"}}}"#;
    let text = format!("{meta}\n{{\"in\":1,\"str\":{{\"pre\":77,\"str\":\"Nat\"}}}}\n");
    let err = read_str(&text).unwrap_err();
    assert_eq!(
        err,
        ExportError::MissingIndex {
            line: 2,
            kind: "name",
            index: 77
        }
    );
}

#[test]
fn an_unknown_line_shape_is_refused() {
    let meta = r#"{"meta":{"exporter":{"name":"x","version":"3.0.0"},"format":{"version":"3.0.0"},"lean":{"version":"4"}}}"#;
    let err = read_str(&format!("{meta}\n{{\"wat\":1}}\n")).unwrap_err();
    assert!(
        matches!(err, ExportError::UnknownShape { line: 2, .. }),
        "{err}"
    );
}

#[test]
fn index_zero_is_implicit_for_names_and_levels() {
    // No line defines name 0 or level 0. The reader pre-populates both.
    let meta = r#"{"meta":{"exporter":{"name":"x","version":"3.0.0"},"format":{"version":"3.0.0"},"lean":{"version":"4"}}}"#;
    let text = format!(
        "{meta}\n\
         {{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"Nat\"}}}}\n\
         {{\"il\":1,\"succ\":0}}\n\
         {{\"ie\":0,\"sort\":1}}\n\
         {{\"axiom\":{{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}}}\n"
    );
    let m = read_str(&text).expect("it must read");
    let decl = m.env.get(&Name::from_dotted("Nat")).expect("Nat is there");
    // `succ 0` is level 1, and `Sort 1` prints as `Type`.
    assert_eq!(decl.ty().pretty(), "Type");
}
