//! Every line shape of the export format, and every way a file can be wrong.
//!
//! The fixture of chapter 3 is one real module, so it only uses the shapes that
//! one module needed. It has no `letE`, no `mdata`, no literal, no `axiom`, no
//! `opaque`, and no `quot`. This file covers the rest, so that a shape we never
//! met in the wild still has a test.

use rean_core::Name;
use rean_export::{ExportError, read_str};
use rean_kernel::{Declaration, QuotKind, ReducibilityHints};

const META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.0.0"},"format":{"version":"3.0.0"},"lean":{"version":"4.27.0-rc1"}}}"#;

/// Builds a file from the `meta` line and the lines that follow.
fn file(lines: &[&str]) -> String {
    let mut out = String::from(META);
    out.push('\n');
    for line in lines {
        out.push_str(line);
        out.push('\n');
    }
    // A blank line must be skipped and not refused.
    out.push('\n');
    out
}

/// Names 1 to 6, then levels 1 to 4, then the terms that the tests reuse.
const PRELUDE: &[&str] = &[
    // names
    r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
    r#"{"in":2,"str":{"pre":0,"str":"u"}}"#,
    r#"{"in":3,"str":{"pre":1,"str":"succ"}}"#,
    r#"{"in":4,"num":{"pre":1,"i":7}}"#,
    r#"{"in":5,"str":{"pre":0,"str":"x"}}"#,
    r#"{"in":6,"str":{"pre":0,"str":"Thing"}}"#,
    // levels
    r#"{"il":1,"succ":0}"#,
    r#"{"il":2,"param":2}"#,
    r#"{"il":3,"max":[1,2]}"#,
    r#"{"il":4,"imax":[1,2]}"#,
    // terms
    r#"{"ie":0,"sort":1}"#,
    r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
    r#"{"ie":2,"bvar":0}"#,
    r#"{"ie":3,"app":{"fn":1,"arg":1}}"#,
    r#"{"ie":4,"lam":{"name":5,"type":1,"body":2,"binderInfo":"default"}}"#,
    r#"{"ie":5,"forallE":{"name":5,"type":1,"body":1,"binderInfo":"implicit"}}"#,
    r#"{"ie":6,"natVal":"42"}"#,
    r#"{"ie":7,"strVal":"hi"}"#,
    r#"{"ie":8,"letE":{"name":5,"type":1,"value":6,"body":2,"nondep":true}}"#,
    r#"{"ie":9,"mdata":{"expr":1,"data":{}}}"#,
    r#"{"ie":10,"sort":2}"#,
    r#"{"ie":11,"sort":3}"#,
    r#"{"ie":12,"sort":4}"#,
    r#"{"ie":13,"forallE":{"name":5,"type":1,"body":0,"binderInfo":"strictImplicit"}}"#,
    r#"{"ie":14,"forallE":{"name":5,"type":1,"body":0,"binderInfo":"instImplicit"}}"#,
    r#"{"ie":15,"proj":{"typeName":6,"idx":0,"struct":1}}"#,
    // A `const` with universe arguments.
    r#"{"ie":16,"const":{"name":1,"us":[1,2]}}"#,
];

fn with(extra: &[&str]) -> String {
    let mut lines: Vec<&str> = PRELUDE.to_vec();
    lines.extend_from_slice(extra);
    file(&lines)
}

// --- every term shape reads ------------------------------------------------

#[test]
fn every_term_shape_reads() {
    let m = read_str(&with(&[
        r#"{"axiom":{"name":6,"levelParams":[],"type":0,"isUnsafe":false}}"#,
    ]))
    .expect("the file must read");
    assert_eq!(m.order.len(), 1);
    assert_eq!(m.meta.exporter_version, "3.0.0");
}

#[test]
fn a_numeric_name_part_reads() {
    // `{"num":{"pre":1,"i":7}}` is `Nat.7`. The elaborator makes names like it.
    let m = read_str(&with(&[
        r#"{"axiom":{"name":4,"levelParams":[],"type":0,"isUnsafe":false}}"#,
    ]))
    .unwrap();
    assert_eq!(m.order[0].to_string(), "Nat.7");
}

#[test]
fn mdata_is_dropped_and_the_inner_term_stays() {
    // Term 9 is `mdata` around term 1, which is the constant `Nat`.
    let m = read_str(&with(&[
        r#"{"axiom":{"name":6,"levelParams":[],"type":9,"isUnsafe":false}}"#,
    ]))
    .unwrap();
    let decl = m.env.get(&Name::from_dotted("Thing")).unwrap();
    assert_eq!(decl.ty().pretty(), "Nat");
}

#[test]
fn a_let_term_reads() {
    let m = read_str(&with(&[
        r#"{"axiom":{"name":6,"levelParams":[],"type":8,"isUnsafe":false}}"#,
    ]))
    .unwrap();
    let decl = m.env.get(&Name::from_dotted("Thing")).unwrap();
    assert_eq!(decl.ty().pretty(), "let x : Nat := 42; x");
}

#[test]
fn the_literals_read() {
    let m = read_str(&with(&[
        r#"{"axiom":{"name":6,"levelParams":[],"type":6,"isUnsafe":false}}"#,
        r#"{"axiom":{"name":5,"levelParams":[],"type":7,"isUnsafe":false}}"#,
    ]))
    .unwrap();
    assert_eq!(
        m.env
            .get(&Name::from_dotted("Thing"))
            .unwrap()
            .ty()
            .pretty(),
        "42"
    );
    assert_eq!(
        m.env.get(&Name::from_dotted("x")).unwrap().ty().pretty(),
        "\"hi\""
    );
}

#[test]
fn the_four_binder_kinds_read() {
    let m = read_str(&with(&[
        r#"{"axiom":{"name":5,"levelParams":[],"type":5,"isUnsafe":false}}"#,
        r#"{"axiom":{"name":6,"levelParams":[],"type":13,"isUnsafe":false}}"#,
    ]))
    .unwrap();
    // `implicit` prints with braces, `strictImplicit` with french brackets.
    assert!(
        m.env
            .get(&Name::from_dotted("x"))
            .unwrap()
            .ty()
            .pretty()
            .contains('{')
    );
    assert!(
        m.env
            .get(&Name::from_dotted("Thing"))
            .unwrap()
            .ty()
            .pretty()
            .contains('⦃')
    );
}

#[test]
fn the_level_shapes_read() {
    let m = read_str(&with(&[
        r#"{"axiom":{"name":5,"levelParams":[2],"type":10,"isUnsafe":false}}"#,
        r#"{"axiom":{"name":6,"levelParams":[2],"type":11,"isUnsafe":false}}"#,
    ]))
    .unwrap();
    assert_eq!(
        m.env.get(&Name::from_dotted("x")).unwrap().ty().pretty(),
        "Sort u"
    );
    assert_eq!(
        m.env
            .get(&Name::from_dotted("Thing"))
            .unwrap()
            .ty()
            .pretty(),
        "Sort max 1 u"
    );
}

// --- every declaration shape reads ----------------------------------------

#[test]
fn a_definition_reads_every_hint_and_safety() {
    let m = read_str(&with(&[
        r#"{"def":[{"name":1,"levelParams":[],"type":0,"value":1,"hints":"abbrev","safety":"safe","all":[1]}]}"#,
        r#"{"def":{"name":3,"levelParams":[],"type":0,"value":1,"hints":{"regular":3},"safety":"unsafe","all":[]}}"#,
        r#"{"def":{"name":5,"levelParams":[],"type":0,"value":1,"hints":"opaque","safety":"partial","all":[]}}"#,
    ]))
    .expect("both the array form and the object form must read");
    assert_eq!(m.order.len(), 3);
    let Some(Declaration::Definition(d)) = m.env.get(&Name::from_dotted("Nat")) else {
        panic!("Nat must be a definition");
    };
    assert_eq!(d.hints, ReducibilityHints::Abbrev);
    let Some(Declaration::Definition(d)) = m.env.get(&Name::from_dotted("Nat.succ")) else {
        panic!("Nat.succ must be a definition");
    };
    assert_eq!(d.hints, ReducibilityHints::Regular(3));
    let Some(Declaration::Definition(d)) = m.env.get(&Name::from_dotted("x")) else {
        panic!("x must be a definition");
    };
    assert_eq!(d.hints, ReducibilityHints::Opaque);
}

#[test]
fn a_theorem_and_an_opaque_read() {
    let m = read_str(&with(&[
        r#"{"thm":[{"name":1,"levelParams":[],"type":0,"value":1,"all":[1]}]}"#,
        r#"{"opaque":{"name":5,"levelParams":[],"type":0,"value":1,"isUnsafe":true,"all":[]}}"#,
    ]))
    .unwrap();
    assert_eq!(
        m.env.get(&Name::from_dotted("Nat")).unwrap().kind_label(),
        "theorem"
    );
    let decl = m.env.get(&Name::from_dotted("x")).unwrap();
    assert_eq!(decl.kind_label(), "opaque");
    // The δ rule must not unfold an opaque value.
    assert!(decl.unfoldable_value().is_none());
}

#[test]
fn the_four_quotient_kinds_read() {
    let m = read_str(&with(&[
        r#"{"quot":{"name":1,"levelParams":[2],"type":0,"kind":"type"}}"#,
        r#"{"quot":{"name":3,"levelParams":[2],"type":0,"kind":"ctor"}}"#,
        r#"{"quot":{"name":5,"levelParams":[2],"type":0,"kind":"lift"}}"#,
        r#"{"quot":{"name":6,"levelParams":[2],"type":0,"kind":"ind"}}"#,
    ]))
    .unwrap();
    let kind_of = |name: &str| {
        let Some(Declaration::Quot(q)) = m.env.get(&Name::from_dotted(name)) else {
            panic!("{name} must be a quot");
        };
        q.kind
    };
    assert_eq!(kind_of("Nat"), QuotKind::Type);
    assert_eq!(kind_of("Nat.succ"), QuotKind::Ctor);
    assert_eq!(kind_of("x"), QuotKind::Lift);
    assert_eq!(kind_of("Thing"), QuotKind::Ind);
}

#[test]
fn the_other_spelling_of_an_inductive_line_reads() {
    // The format document on master says `types`, `ctors`, and `recs`. The
    // fixture says `inductiveVals`, `constructorVals`, and `recursorVals`. The
    // reader takes either.
    let inductive = r#"{"inductive":{"types":[{"name":6,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[6],"ctors":[3],"numNested":0,"isRec":false,"isUnsafe":false,"isReflexive":false}],"ctors":[{"name":3,"levelParams":[],"type":1,"induct":6,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false}],"recs":[{"name":5,"levelParams":[],"type":0,"all":[6],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":1,"rules":[{"ctor":3,"nfields":0,"rhs":1}],"k":true,"isUnsafe":false}]}}"#;
    let m = read_str(&with(&[inductive])).expect("the other spelling must read");
    assert_eq!(m.order.len(), 3);
    assert_eq!(
        m.env.get(&Name::from_dotted("Thing")).unwrap().kind_label(),
        "inductive"
    );
    let Some(Declaration::Recursor(rec)) = m.env.get(&Name::from_dotted("x")) else {
        panic!("x must be a recursor");
    };
    assert!(rec.k);
    assert_eq!(rec.rules.len(), 1);
    // An inductive with no `numNested` field defaults to 0.
    assert!(m.env.sole_ctor(&Name::from_dotted("Thing")).is_some());
}

// --- every way a file can be wrong ----------------------------------------

#[test]
fn an_unknown_binder_kind_is_refused() {
    let err = read_str(&with(&[
        r#"{"ie":17,"lam":{"name":5,"type":1,"body":2,"binderInfo":"wat"}}"#,
    ]))
    .unwrap_err();
    assert!(
        matches!(
            err,
            ExportError::BadField {
                field: "binderInfo",
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn an_unknown_quotient_kind_is_refused() {
    let err = read_str(&with(&[
        r#"{"quot":{"name":1,"levelParams":[],"type":0,"kind":"wat"}}"#,
    ]))
    .unwrap_err();
    assert!(
        matches!(
            err,
            ExportError::BadField {
                field: "quot.kind",
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn a_missing_level_index_is_refused() {
    let err = read_str(&with(&[r#"{"ie":17,"sort":99}"#])).unwrap_err();
    assert!(
        matches!(
            err,
            ExportError::MissingIndex {
                kind: "level",
                index: 99,
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn a_missing_term_index_is_refused() {
    let err = read_str(&with(&[r#"{"ie":17,"app":{"fn":99,"arg":1}}"#])).unwrap_err();
    assert!(
        matches!(
            err,
            ExportError::MissingIndex {
                kind: "term",
                index: 99,
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn a_level_pair_that_is_not_a_pair_is_refused() {
    let err = read_str(&with(&[r#"{"il":5,"max":[1]}"#])).unwrap_err();
    assert!(
        matches!(err, ExportError::BadField { field: "max", .. }),
        "{err}"
    );
    let err = read_str(&with(&[r#"{"il":5,"imax":["a","b"]}"#])).unwrap_err();
    assert!(
        matches!(err, ExportError::BadField { field: "imax", .. }),
        "{err}"
    );
}

#[test]
fn a_field_of_the_wrong_type_is_refused() {
    let err = read_str(&with(&[r#"{"ie":17,"app":{"fn":"one","arg":1}}"#])).unwrap_err();
    assert!(
        matches!(err, ExportError::BadField { field: "fn", .. }),
        "{err}"
    );
    let err = read_str(&with(&[r#"{"in":17,"str":{"pre":0,"str":7}}"#])).unwrap_err();
    assert!(
        matches!(
            err,
            ExportError::BadField {
                field: "str.str",
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn a_level_list_that_is_not_a_list_is_refused() {
    let err = read_str(&with(&[
        r#"{"axiom":{"name":1,"levelParams":7,"type":0,"isUnsafe":false}}"#,
    ]))
    .unwrap_err();
    assert!(
        matches!(
            err,
            ExportError::BadField {
                field: "levelParams",
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn an_unknown_name_shape_is_refused() {
    let err = read_str(&with(&[r#"{"in":17,"wat":1}"#])).unwrap_err();
    assert!(matches!(err, ExportError::UnknownShape { .. }), "{err}");
}

#[test]
fn an_unknown_level_shape_is_refused() {
    let err = read_str(&with(&[r#"{"il":5,"wat":1}"#])).unwrap_err();
    assert!(matches!(err, ExportError::UnknownShape { .. }), "{err}");
}

#[test]
fn an_unknown_term_shape_is_refused() {
    let err = read_str(&with(&[r#"{"ie":17,"wat":1}"#])).unwrap_err();
    assert!(matches!(err, ExportError::UnknownShape { .. }), "{err}");
}

#[test]
fn a_meta_line_with_no_version_is_refused() {
    let err = read_str(r#"{"meta":{"exporter":{"name":"x"}}}"#).unwrap_err();
    assert!(
        matches!(err, ExportError::BadField { field: "meta", .. }),
        "{err}"
    );
}

#[test]
fn every_error_has_a_message() {
    // A reader that fails silently is worse than one that does not read.
    let cases: Vec<String> = vec![
        read_str("oops").unwrap_err().to_string(),
        read_str(r#"{"in":1,"str":{"pre":0,"str":"a"}}"#)
            .unwrap_err()
            .to_string(),
        read_str(&with(&[r#"{"ie":17,"sort":99}"#]))
            .unwrap_err()
            .to_string(),
        read_str(&with(&[r#"{"ie":17,"wat":1}"#]))
            .unwrap_err()
            .to_string(),
        read_str(&with(&[r#"{"ie":17,"app":{"fn":"x","arg":1}}"#]))
            .unwrap_err()
            .to_string(),
    ];
    for message in &cases {
        assert!(!message.is_empty(), "every error needs a message");
    }
    assert!(cases[0].contains("invalid JSON"));
    assert!(cases[1].contains("meta"));
}

// --- the last corners of the reader ---------------------------------------

#[test]
fn an_absent_level_list_is_an_empty_list() {
    // The field is optional. No `levelParams` key means no parameters.
    let m = read_str(&with(&[
        r#"{"axiom":{"name":6,"type":0,"isUnsafe":false}}"#,
    ]))
    .expect("the field is optional");
    assert!(
        m.env
            .get(&Name::from_dotted("Thing"))
            .unwrap()
            .level_params()
            .is_empty()
    );
}

#[test]
fn a_nat_literal_written_as_a_json_number_reads() {
    // The format writes the digits as a string, because a Lean `Nat` has no
    // upper bound. A plain JSON number still reads.
    let m = read_str(&with(&[
        r#"{"ie":17,"natVal":42}"#,
        r#"{"axiom":{"name":6,"levelParams":[],"type":17,"isUnsafe":false}}"#,
    ]))
    .unwrap();
    assert_eq!(
        m.env
            .get(&Name::from_dotted("Thing"))
            .unwrap()
            .ty()
            .pretty(),
        "42"
    );
}

#[test]
fn a_nat_literal_of_the_wrong_json_type_is_refused() {
    let err = read_str(&with(&[r#"{"ie":17,"natVal":[1]}"#])).unwrap_err();
    assert!(
        matches!(
            err,
            ExportError::BadField {
                field: "natVal",
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn a_line_that_is_not_an_object_is_refused() {
    // A bare number is valid JSON and not a valid line.
    let err = read_str(&with(&["42"])).unwrap_err();
    assert!(matches!(err, ExportError::UnknownShape { .. }), "{err}");
    assert!(err.to_string().contains("42"));
}

#[test]
fn a_definition_with_no_hints_field_reads() {
    let m = read_str(&with(&[
        r#"{"def":{"name":6,"levelParams":[],"type":0,"value":1,"safety":"safe","all":[]}}"#,
    ]))
    .expect("the field is optional");
    let Some(Declaration::Definition(d)) = m.env.get(&Name::from_dotted("Thing")) else {
        panic!("Thing must be a definition");
    };
    assert_eq!(d.hints, ReducibilityHints::Regular(0));
}
