//! Red team tests. Can a crafted input make the checker accept a lie?
//!
//! Every test here failed before these checks existed. The first one is the
//! reason the rest matter: our checker accepted a proof of `False`.

use rean_core::Name;
use rean_kernel::{
    AxiomVal, ConstructorVal, Declaration, Environment, Expr, InductiveVal, Level, Proj,
    RecursorRule, RecursorVal, TheoremVal, TypeChecker, TypeError,
};
use std::sync::Arc;

fn u() -> Expr {
    Expr::const_("U", vec![])
}

fn uu() -> Expr {
    Expr::const_("U.u", vec![])
}

fn inductive(name: &str, ty: Expr, ctors: &[&str]) -> Declaration {
    Declaration::Inductive(InductiveVal {
        name: Name::from_dotted(name),
        level_params: Vec::new(),
        ty,
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted(name)],
        ctors: ctors.iter().map(|c| Name::from_dotted(c)).collect(),
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    })
}

fn constructor(name: &str, induct: &str, ty: Expr) -> Declaration {
    Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted(name),
        level_params: Vec::new(),
        ty,
        induct: Name::from_dotted(induct),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    })
}

/// `inductive False : Prop` with no constructor, and `inductive U : Type` with
/// one.
fn base() -> Environment {
    let mut env = Environment::new();
    env.add(inductive("False", Expr::prop(), &[]));
    env.add(inductive("U", Expr::type_(0), &["U.u"]));
    env.add(constructor("U.u", "U", u()));
    env
}

/// `{motive : U → Sort v} → motive U.u → (t : U) → motive t`
fn honest_recursor_type() -> Expr {
    Expr::forall(
        "motive",
        Expr::arrow(u(), Expr::sort(Level::param("v"))),
        Expr::forall(
            "minor",
            Expr::bvar(0).app(uu()),
            Expr::forall("t", u(), Expr::bvar(2).app(Expr::bvar(0))),
        ),
    )
}

/// Builds `U.rec` with the given type and the given right hand side.
fn recursor(ty: Expr, rhs: Expr, motives: u32) -> Declaration {
    Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("U.rec"),
        level_params: vec![Name::from_dotted("v")],
        ty,
        all: vec![Name::from_dotted("U")],
        num_params: 0,
        num_indices: 0,
        num_motives: motives,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: Name::from_dotted("U.u"),
            num_fields: 0,
            rhs,
        }],
        k: false,
        is_unsafe: false,
    })
}

/// `fun motive minor => minor`, which is the correct rule.
fn honest_rhs() -> Expr {
    Expr::lam(
        "motive",
        Expr::arrow(u(), Expr::sort(Level::param("v"))),
        Expr::lam("minor", Expr::bvar(0).app(uu()), Expr::bvar(0)),
    )
}

// --- the headline -------------------------------------------------------

#[test]
fn a_recursor_cannot_smuggle_in_an_axiom() {
    // The lie. A recursor whose declared type is `U → False`. No real recursor
    // could have that type, and before this check nothing looked.
    //
    // Accept it and `U.rec U.u` is a proof of `False`, with no axiom and no
    // other mistake anywhere.
    let env = base();
    let liar = recursor(Expr::arrow(u(), Expr::const_("False", vec![])), uu(), 0);
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&liar).unwrap_err();
    assert!(matches!(err, TypeError::BadRecursor { .. }), "{err}");
    assert!(err.to_string().contains("at least one motive"), "{err}");
}

#[test]
fn a_refused_recursor_never_enters_the_environment() {
    // This is the second half of the protection. The check refuses the
    // recursor, so the driver must not add it, so the proof of `False` cannot
    // even be written down.
    let env = base();
    let oops = Declaration::Theorem(TheoremVal {
        name: Name::from_dotted("oops"),
        level_params: Vec::new(),
        ty: Expr::const_("False", vec![]),
        value: Expr::const_("U.rec", vec![]).app(uu()),
        all: Vec::new(),
    });
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&oops).unwrap_err();
    assert_eq!(err, TypeError::UnknownConstant(Name::from_dotted("U.rec")));
}

#[test]
fn an_honest_recursor_is_accepted() {
    // A check that refuses correct code is worse than no check at all.
    let env = base();
    let honest = recursor(honest_recursor_type(), honest_rhs(), 1);
    let mut tc = TypeChecker::new(&env);
    tc.check_declaration(&honest)
        .unwrap_or_else(|err| panic!("an honest recursor must pass: {err}"));
}

#[test]
fn a_rule_that_delivers_the_wrong_type_is_refused() {
    // The shape is right and one rule lies. Its right hand side returns a `U`
    // where the recursor type promises `motive U.u`.
    //
    // That is the property that makes ι sound: a rule must deliver the type
    // that the recursor promises. Without it you can move a term into a type
    // it does not inhabit.
    let env = base();
    let liar = recursor(
        honest_recursor_type(),
        Expr::lam(
            "motive",
            Expr::arrow(u(), Expr::sort(Level::param("v"))),
            Expr::lam("minor", Expr::bvar(0).app(uu()), uu()),
        ),
        1,
    );
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&liar).unwrap_err();
    assert!(matches!(err, TypeError::BadRecursor { .. }), "{err}");
    assert!(err.to_string().contains("delivers"), "{err}");
}

#[test]
fn a_rule_for_a_constructor_that_does_not_exist_is_refused() {
    let env = base();
    let Declaration::Recursor(mut rec) = recursor(honest_recursor_type(), honest_rhs(), 1) else {
        panic!("it is a recursor");
    };
    rec.rules[0].ctor = Name::from_dotted("U.nope");
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&Declaration::Recursor(rec))
        .unwrap_err();
    assert!(err.to_string().contains("no rule for `U.u`"), "{err}");
}

#[test]
fn the_wrong_number_of_rules_is_refused() {
    let env = base();
    let Declaration::Recursor(mut rec) = recursor(honest_recursor_type(), honest_rhs(), 1) else {
        panic!("it is a recursor");
    };
    rec.rules.clear();
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&Declaration::Recursor(rec))
        .unwrap_err();
    assert!(err.to_string().contains("0 rules"), "{err}");
}

#[test]
fn a_rule_that_claims_the_wrong_field_count_is_refused() {
    let env = base();
    let Declaration::Recursor(mut rec) = recursor(honest_recursor_type(), honest_rhs(), 1) else {
        panic!("it is a recursor");
    };
    rec.rules[0].num_fields = 3;
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&Declaration::Recursor(rec))
        .unwrap_err();
    assert!(err.to_string().contains("3 fields"), "{err}");
}

#[test]
fn the_wrong_parameter_or_index_count_is_refused() {
    let env = base();
    let Declaration::Recursor(mut rec) = recursor(honest_recursor_type(), honest_rhs(), 1) else {
        panic!("it is a recursor");
    };
    rec.num_indices = 2;
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&Declaration::Recursor(rec))
        .unwrap_err();
    assert!(err.to_string().contains("indices"), "{err}");
}

// --- the elimination universe -------------------------------------------

#[test]
fn a_prop_with_two_elements_must_not_eliminate_into_type() {
    // `Prop` carries no information beyond the fact that it holds. Let a
    // two constructor `Prop` eliminate into `Type` and you can read which
    // constructor a proof used, which breaks proof irrelevance.
    let mut env = Environment::new();
    env.add(inductive("Or2", Expr::prop(), &["Or2.l", "Or2.r"]));
    let or2 = || Expr::const_("Or2", vec![]);
    env.add(constructor("Or2.l", "Or2", or2()));
    env.add(constructor("Or2.r", "Or2", or2()));

    let into = |sort: Expr| {
        Declaration::Recursor(RecursorVal {
            name: Name::from_dotted("Or2.rec"),
            level_params: vec![Name::from_dotted("v")],
            ty: Expr::forall(
                "motive",
                Expr::arrow(or2(), sort),
                Expr::forall(
                    "minor",
                    Expr::bvar(0).app(Expr::const_("Or2.l", vec![])),
                    Expr::forall("t", or2(), Expr::bvar(2).app(Expr::bvar(0))),
                ),
            ),
            all: vec![Name::from_dotted("Or2")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![
                RecursorRule {
                    ctor: Name::from_dotted("Or2.l"),
                    num_fields: 0,
                    rhs: Expr::prop(),
                },
                RecursorRule {
                    ctor: Name::from_dotted("Or2.r"),
                    num_fields: 0,
                    rhs: Expr::prop(),
                },
            ],
            k: false,
            is_unsafe: false,
        })
    };
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&into(Expr::sort(Level::param("v"))))
        .unwrap_err();
    assert!(
        err.to_string().contains("must not"),
        "a large eliminator for a two element Prop must be refused: {err}"
    );
}

// --- universe hygiene ---------------------------------------------------

#[test]
fn an_undeclared_universe_parameter_is_refused() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let open = Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("Open"),
        level_params: Vec::new(),
        ty: Expr::sort(Level::param("u")),
        is_unsafe: false,
    });
    let err = tc.check_declaration(&open).unwrap_err();
    assert_eq!(
        err,
        TypeError::UndeclaredUniverse {
            declaration: Name::from_dotted("Open"),
            param: Name::from_dotted("u"),
        }
    );
    assert!(err.to_string().contains("does not declare it"));
}

#[test]
fn a_universe_parameter_used_in_a_value_must_be_declared() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let open = Declaration::Theorem(TheoremVal {
        name: Name::from_dotted("Open"),
        level_params: Vec::new(),
        ty: Expr::type_(4),
        // The type declares nothing and the value smuggles `u` in.
        value: Expr::sort(Level::param("u")),
        all: Vec::new(),
    });
    assert!(matches!(
        tc.check_declaration(&open),
        Err(TypeError::UndeclaredUniverse { .. })
    ));
}

#[test]
fn a_repeated_universe_parameter_is_refused() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let twice = Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("Twice"),
        level_params: vec![Name::from_dotted("u"), Name::from_dotted("u")],
        ty: Expr::sort(Level::param("u")),
        is_unsafe: false,
    });
    let err = tc.check_declaration(&twice).unwrap_err();
    assert!(matches!(err, TypeError::RepeatedUniverse { .. }), "{err}");
}

#[test]
fn a_declared_universe_parameter_is_fine() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let good = Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("Good"),
        level_params: vec![Name::from_dotted("u")],
        ty: Expr::sort(Level::param("u")),
        is_unsafe: false,
    });
    assert!(tc.check_declaration(&good).is_ok());
}

// --- one name, one declaration ------------------------------------------

#[test]
fn a_duplicate_declaration_is_refused() {
    // A second declaration under one name could shadow the first, and then a
    // proof checked against one meaning would be used with the other.
    let mut env = Environment::new();
    env.add(inductive("X", Expr::prop(), &[]));
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&inductive("X", Expr::type_(0), &[]))
        .unwrap_err();
    assert_eq!(err, TypeError::DuplicateDeclaration(Name::from_dotted("X")));
}

// --- structure eta ------------------------------------------------------

#[test]
fn a_structure_is_the_same_as_its_fields_rebuilt() {
    // `S.mk p.1` and `p` are the same term, because a structure has one
    // constructor and no index, so its fields determine it.
    let mut env = Environment::new();
    env.add(inductive("S", Expr::type_(0), &["S.mk"]));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("S.mk"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::prop(), Expr::const_("S", vec![])),
        induct: Name::from_dotted("S"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    }));
    let mut tc = TypeChecker::new(&env);
    let p = Expr::FVar(tc.push_local("p", Expr::const_("S", vec![])));
    let rebuilt = Expr::const_("S.mk", vec![]).app(Expr::Proj(Proj {
        structure: Name::from_dotted("S"),
        index: 0,
        value: Arc::new(p.clone()),
    }));
    assert!(tc.is_def_eq(&rebuilt, &p).unwrap());
    assert!(tc.is_def_eq(&p, &rebuilt).unwrap(), "and in either order");

    // It must not fire for a different field value. The field type is `Prop`,
    // so a well formed other value is some other proposition.
    let q = Expr::FVar(tc.push_local("q", Expr::prop()));
    let other = Expr::const_("S.mk", vec![]).app(q);
    assert!(!tc.is_def_eq(&other, &p).unwrap());
}

#[test]
fn a_projection_needs_a_type_with_one_constructor() {
    // With two constructors the fields do not determine the term, so a
    // projection out of it has no meaning and the kernel refuses the term
    // before eta is ever asked about it.
    let mut env = Environment::new();
    env.add(inductive("E", Expr::type_(0), &["E.a", "E.b"]));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("E.a"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::prop(), Expr::const_("E", vec![])),
        induct: Name::from_dotted("E"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    }));
    env.add(constructor("E.b", "E", Expr::const_("E", vec![])));
    let mut tc = TypeChecker::new(&env);
    let p = Expr::FVar(tc.push_local("p", Expr::const_("E", vec![])));
    let projection = Expr::Proj(Proj {
        structure: Name::from_dotted("E"),
        index: 0,
        value: Arc::new(p),
    });
    let err = tc.infer_type(&projection).unwrap_err();
    assert!(matches!(err, TypeError::NotAStructure { .. }), "{err}");
}
