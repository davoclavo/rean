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
    assert!(
        err.to_string().contains("`U.nope` is not a constructor"),
        "{err}"
    );
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
    // A recursor with no rule computes nothing, and `U` has a constructor.
    assert!(err.to_string().contains("no rules"), "{err}");
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
fn a_prop_that_is_not_a_subsingleton_must_not_eliminate_into_type() {
    // `Box : Prop` has one constructor and its field is a `Nat`, which is
    // data. So `Box` has more than one element, and reading the field out of a
    // proof of `Box` would break proof irrelevance.
    let mut env = Environment::new();
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("Nat"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    let boxed = || Expr::const_("Box", vec![]);
    let nat = || Expr::const_("Nat", vec![]);
    env.add(inductive("Box", Expr::prop(), &["Box.mk"]));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("Box.mk"),
        level_params: Vec::new(),
        ty: Expr::arrow(nat(), boxed()),
        induct: Name::from_dotted("Box"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    }));

    // `{motive : Box → Sort v} → ((n : Nat) → motive (Box.mk n)) → (t : Box) → motive t`
    let into = |sort: Expr| {
        Declaration::Recursor(RecursorVal {
            name: Name::from_dotted("Box.rec"),
            level_params: vec![Name::from_dotted("v")],
            ty: Expr::forall(
                "motive",
                Expr::arrow(boxed(), sort),
                Expr::forall(
                    "minor",
                    Expr::forall(
                        "n",
                        nat(),
                        Expr::bvar(1).app(Expr::const_("Box.mk", vec![]).app(Expr::bvar(0))),
                    ),
                    Expr::forall("t", boxed(), Expr::bvar(2).app(Expr::bvar(0))),
                ),
            ),
            all: vec![Name::from_dotted("Box")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: Name::from_dotted("Box.mk"),
                num_fields: 1,
                rhs: Expr::prop(),
            }],
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
        "a large eliminator for a Prop that carries data must be refused: {err}"
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

// --- the minor premises must be the ones induction needs -----------------

/// `inductive N : Type` with `N.z : N` and `N.s : N → N`.
fn peano() -> Environment {
    let mut env = Environment::new();
    let n = || Expr::const_("N", vec![]);
    env.add(inductive("N", Expr::type_(0), &["N.z", "N.s"]));
    env.add(constructor("N.z", "N", n()));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("N.s"),
        level_params: Vec::new(),
        ty: Expr::arrow(n(), n()),
        induct: Name::from_dotted("N"),
        cidx: 1,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    }));
    env
}

#[test]
fn a_minor_premise_with_an_extra_binder_is_refused() {
    // The rule stays type correct and the premise is not the one induction
    // needs. Induction over a constructor with no field needs
    // `motive U.u`, and this recursor asks for `(x : U) → motive U.u`.
    //
    // The old check passed this, because the rule really does deliver
    // `motive U.u`. Only a derived premise catches it.
    let env = base();
    let sort_v = || Expr::sort(Level::param("v"));
    // `minor : (x : U) → motive U.u`, with `motive` one binder out.
    let minor_type =
        |motive_depth: u32| Expr::forall("x", u(), Expr::bvar(motive_depth + 1).app(uu()));
    let ty = Expr::forall(
        "motive",
        Expr::arrow(u(), sort_v()),
        Expr::forall(
            "minor",
            minor_type(0),
            Expr::forall("t", u(), Expr::bvar(2).app(Expr::bvar(0))),
        ),
    );
    // `fun motive minor => minor U.u`, which really does deliver `motive U.u`.
    let rhs = Expr::lam(
        "motive",
        Expr::arrow(u(), sort_v()),
        Expr::lam("minor", minor_type(0), Expr::bvar(0).app(uu())),
    );
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&recursor(ty, rhs, 1)).unwrap_err();
    assert!(matches!(err, TypeError::BadRecursor { .. }), "{err}");
    assert!(
        err.to_string().contains("induction needs"),
        "the message must say what induction needs: {err}"
    );
}

#[test]
fn a_minor_premise_that_drops_the_induction_hypothesis_is_refused() {
    // This is the sharpest case. `N.s` has a recursive field, so induction
    // needs `(n : N) → motive n → motive (N.s n)`. This recursor asks only for
    // `(n : N) → motive (N.s n)`, with no hypothesis.
    //
    // Both rules are type correct, so every earlier check passes. What is left
    // is not an induction principle, and a recursor that is not an induction
    // principle is an axiom.
    let env = peano();
    let n = || Expr::const_("N", vec![]);
    let nz = || Expr::const_("N.z", vec![]);
    let ns = |x: Expr| Expr::const_("N.s", vec![]).app(x);
    let sort_v = || Expr::sort(Level::param("v"));
    let motive_type = || Expr::arrow(n(), sort_v());

    // `mz : motive N.z`, with `motive` at the given depth.
    let mz_type = |motive: u32| Expr::bvar(motive).app(nz());
    // `ms : (k : N) → motive (N.s k)`, with no hypothesis.
    let ms_type =
        |motive: u32| Expr::forall("k", n(), Expr::bvar(motive + 1).app(ns(Expr::bvar(0))));

    let ty = Expr::forall(
        "motive",
        motive_type(),
        Expr::forall(
            "mz",
            mz_type(0),
            Expr::forall(
                "ms",
                ms_type(1),
                Expr::forall("t", n(), Expr::bvar(3).app(Expr::bvar(0))),
            ),
        ),
    );

    // `fun motive mz ms => mz`
    let rhs_z = Expr::lam(
        "motive",
        motive_type(),
        Expr::lam("mz", mz_type(0), Expr::lam("ms", ms_type(1), Expr::bvar(1))),
    );
    // `fun motive mz ms k => ms k`, which delivers `motive (N.s k)`.
    let rhs_s = Expr::lam(
        "motive",
        motive_type(),
        Expr::lam(
            "mz",
            mz_type(0),
            Expr::lam(
                "ms",
                ms_type(1),
                Expr::lam("k", n(), Expr::bvar(1).app(Expr::bvar(0))),
            ),
        ),
    );

    let rec = Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("N.rec"),
        level_params: vec![Name::from_dotted("v")],
        ty,
        all: vec![Name::from_dotted("N")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        rules: vec![
            RecursorRule {
                ctor: Name::from_dotted("N.z"),
                num_fields: 0,
                rhs: rhs_z,
            },
            RecursorRule {
                ctor: Name::from_dotted("N.s"),
                num_fields: 1,
                rhs: rhs_s,
            },
        ],
        k: false,
        is_unsafe: false,
    });

    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&rec).unwrap_err();
    assert!(matches!(err, TypeError::BadRecursor { .. }), "{err}");
    let message = err.to_string();
    assert!(message.contains("induction needs"), "{message}");
    // The message must name the hypothesis that is absent.
    assert!(message.contains("N.s"), "{message}");
}

#[test]
fn the_wrong_number_of_minor_premises_is_refused() {
    // `N` has two constructors, so induction needs two premises. This recursor
    // offers one.
    let env = peano();
    let n = || Expr::const_("N", vec![]);
    let ty = Expr::forall(
        "motive",
        Expr::arrow(n(), Expr::sort(Level::param("v"))),
        Expr::forall(
            "mz",
            Expr::bvar(0).app(Expr::const_("N.z", vec![])),
            Expr::forall("t", n(), Expr::bvar(2).app(Expr::bvar(0))),
        ),
    );
    let rec = Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("N.rec"),
        level_params: vec![Name::from_dotted("v")],
        ty,
        all: vec![Name::from_dotted("N")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![
            RecursorRule {
                ctor: Name::from_dotted("N.z"),
                num_fields: 0,
                rhs: Expr::prop(),
            },
            RecursorRule {
                ctor: Name::from_dotted("N.s"),
                num_fields: 1,
                rhs: Expr::prop(),
            },
        ],
        k: false,
        is_unsafe: false,
    });
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&rec).unwrap_err();
    assert!(
        err.to_string().contains("minor premises"),
        "one premise per constructor: {err}"
    );
}

// --- the trust report ----------------------------------------------------

/// `axiom Choice : Prop`, plus a chain that reaches it.
fn with_an_axiom() -> Environment {
    let mut env = Environment::new();
    env.add(inductive("P", Expr::prop(), &[]));
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("Choice"),
        level_params: Vec::new(),
        ty: Expr::const_("P", vec![]),
        is_unsafe: false,
    }));
    // `def viaChoice : P := Choice`
    env.add(Declaration::Definition(rean_kernel::DefinitionVal {
        name: Name::from_dotted("viaChoice"),
        level_params: Vec::new(),
        ty: Expr::const_("P", vec![]),
        value: Expr::const_("Choice", vec![]),
        hints: rean_kernel::ReducibilityHints::Abbrev,
        safety: rean_kernel::DefinitionSafety::Safe,
        all: Vec::new(),
    }));
    // `theorem rests : P := viaChoice`
    env.add(Declaration::Theorem(TheoremVal {
        name: Name::from_dotted("rests"),
        level_params: Vec::new(),
        ty: Expr::const_("P", vec![]),
        value: Expr::const_("viaChoice", vec![]),
        all: Vec::new(),
    }));
    env
}

#[test]
fn an_axiom_is_reported_through_a_whole_chain() {
    // The kernel re-checks everything but an axiom, so a report that does not
    // name the axioms is not a trust report.
    let env = with_an_axiom();
    let names = |name: &str| {
        env.axioms_of(&Name::from_dotted(name))
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    };
    assert_eq!(names("Choice"), vec!["Choice"]);
    assert_eq!(names("viaChoice"), vec!["Choice"]);
    assert_eq!(
        names("rests"),
        vec!["Choice"],
        "it must reach through the def"
    );
    // A declaration that rests on nothing reports nothing.
    assert!(names("P").is_empty());
    // An unknown name reports nothing rather than panic.
    assert!(names("nope").is_empty());
}

#[test]
fn a_recursor_that_names_itself_does_not_loop() {
    // A recursor's rules call the recursor, so the dependency graph has a
    // cycle. The walk must still stop.
    let env = base();
    let mut with_rec = env;
    let Declaration::Recursor(mut rec) = recursor(honest_recursor_type(), honest_rhs(), 1) else {
        panic!("it is a recursor");
    };
    rec.rules[0].rhs = Expr::const_("U.rec", vec![Level::Zero]);
    with_rec.add(Declaration::Recursor(rec));
    assert!(with_rec.axioms_of(&Name::from_dotted("U.rec")).is_empty());
}

// --- unsafe may not reach into safe code ---------------------------------

#[test]
fn a_safe_declaration_may_not_use_an_unsafe_one() {
    // An unsafe declaration may not terminate. The kernel evaluates a term
    // while it checks it, and a term that does not terminate can be given any
    // type at all.
    let mut env = Environment::new();
    env.add(inductive("P", Expr::prop(), &[]));
    env.add(Declaration::Definition(rean_kernel::DefinitionVal {
        name: Name::from_dotted("risky"),
        level_params: Vec::new(),
        ty: Expr::const_("P", vec![]),
        value: Expr::const_("P", vec![]),
        hints: rean_kernel::ReducibilityHints::Opaque,
        safety: rean_kernel::DefinitionSafety::Partial,
        all: Vec::new(),
    }));
    let safe = Declaration::Theorem(TheoremVal {
        name: Name::from_dotted("leans"),
        level_params: Vec::new(),
        ty: Expr::const_("P", vec![]),
        value: Expr::const_("risky", vec![]),
        all: Vec::new(),
    });
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&safe).unwrap_err();
    assert_eq!(
        err,
        TypeError::UnsafeDependency {
            declaration: Name::from_dotted("leans"),
            dependency: Name::from_dotted("risky"),
        }
    );
    assert!(err.to_string().contains("may not terminate"));
}

#[test]
fn an_unsafe_declaration_may_use_an_unsafe_one() {
    // That is what the word means.
    let mut env = Environment::new();
    env.add(inductive("P", Expr::prop(), &[]));
    env.add(Declaration::Definition(rean_kernel::DefinitionVal {
        name: Name::from_dotted("risky"),
        level_params: Vec::new(),
        ty: Expr::prop(),
        value: Expr::const_("P", vec![]),
        hints: rean_kernel::ReducibilityHints::Opaque,
        safety: rean_kernel::DefinitionSafety::Unsafe,
        all: Vec::new(),
    }));
    let also = Declaration::Definition(rean_kernel::DefinitionVal {
        name: Name::from_dotted("alsoRisky"),
        level_params: Vec::new(),
        ty: Expr::prop(),
        value: Expr::const_("risky", vec![]),
        hints: rean_kernel::ReducibilityHints::Opaque,
        safety: rean_kernel::DefinitionSafety::Unsafe,
        all: Vec::new(),
    });
    let mut tc = TypeChecker::new(&env);
    assert!(tc.check_safety(&also).is_ok());
}

#[test]
fn a_safe_declaration_may_use_a_safe_one() {
    let env = with_an_axiom();
    let mut tc = TypeChecker::new(&env);
    // An axiom is trusted, not unsafe. Using one is fine, and the trust report
    // names it.
    let decl = env.get(&Name::from_dotted("rests")).unwrap();
    assert!(tc.check_safety(decl).is_ok());
}

// --- a mutual group -------------------------------------------------------

/// Two inductive types declared together, each with one constructor.
///
/// ```text
/// mutual
///   inductive A : Type | A.mk : A
///   inductive B : Type | B.mk : B
/// end
/// ```
///
/// A recursor over a mutual group takes **one motive per type**, in group
/// order, and **one minor premise per constructor of every type**, also in
/// group order. The induction is simultaneous.
fn mutual_group() -> Environment {
    let mut env = Environment::new();
    for name in ["A", "B"] {
        env.add(Declaration::Inductive(InductiveVal {
            name: Name::from_dotted(name),
            level_params: Vec::new(),
            ty: Expr::type_(0),
            num_params: 0,
            num_indices: 0,
            all: vec![Name::from_dotted("A"), Name::from_dotted("B")],
            ctors: vec![Name::from_dotted(&format!("{name}.mk"))],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }));
        env.add(constructor(
            &format!("{name}.mk"),
            name,
            Expr::const_(name, vec![]),
        ));
    }
    env
}

/// Builds `A.rec` over the mutual group, with the minors in the given order.
///
/// With `swapped` false this is the honest recursor. With `swapped` true the
/// two minor premises trade places, which is the shape that only an ordered
/// derivation can refuse.
fn mutual_recursor(swapped: bool) -> Declaration {
    let a = || Expr::const_("A", vec![]);
    let b = || Expr::const_("B", vec![]);
    let a_mk = || Expr::const_("A.mk", vec![]);
    let b_mk = || Expr::const_("B.mk", vec![]);
    let sort_v = || Expr::sort(Level::param("v"));

    // `motive_A A.mk`, with `motive_A` at the given de Bruijn depth.
    let for_a = |depth: u32| Expr::bvar(depth).app(a_mk());
    // `motive_B B.mk`.
    let for_b = |depth: u32| Expr::bvar(depth).app(b_mk());

    // At the first minor binder: motive_B is 0 and motive_A is 1.
    // At the second: the first minor is 0, motive_B is 1, motive_A is 2.
    let (first, second) = if swapped {
        (for_b(0), for_a(2))
    } else {
        (for_a(1), for_b(1))
    };

    let ty = Expr::forall(
        "motiveA",
        Expr::arrow(a(), sort_v()),
        Expr::forall(
            "motiveB",
            Expr::arrow(b(), sort_v()),
            Expr::forall(
                "minor1",
                first.clone(),
                Expr::forall(
                    "minor2",
                    second.clone(),
                    Expr::forall("t", a(), Expr::bvar(4).app(Expr::bvar(0))),
                ),
            ),
        ),
    );

    // `fun motiveA motiveB minor1 minor2 => <the one for A.mk>`
    let chosen = if swapped {
        Expr::bvar(0)
    } else {
        Expr::bvar(1)
    };
    let rhs = Expr::lam(
        "motiveA",
        Expr::arrow(a(), sort_v()),
        Expr::lam(
            "motiveB",
            Expr::arrow(b(), sort_v()),
            Expr::lam("minor1", first, Expr::lam("minor2", second, chosen)),
        ),
    );

    Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("A.rec"),
        level_params: vec![Name::from_dotted("v")],
        ty,
        all: vec![Name::from_dotted("A"), Name::from_dotted("B")],
        num_params: 0,
        num_indices: 0,
        num_motives: 2,
        num_minors: 2,
        rules: vec![RecursorRule {
            ctor: Name::from_dotted("A.mk"),
            num_fields: 0,
            rhs,
        }],
        k: false,
        is_unsafe: false,
    })
}

#[test]
fn a_mutual_recursor_is_accepted() {
    let env = mutual_group();
    let mut tc = TypeChecker::new(&env);
    tc.check_declaration(&mutual_recursor(false))
        .unwrap_or_else(|err| panic!("an honest mutual recursor must pass: {err}"));
}

#[test]
fn a_mutual_recursor_with_its_minors_in_the_wrong_order_is_refused() {
    // The premises are both present and each is type correct on its own. Only
    // an ordered derivation can see that they are the wrong way round.
    let env = mutual_group();
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&mutual_recursor(true)).unwrap_err();
    assert!(matches!(err, TypeError::BadRecursor { .. }), "{err}");
    assert!(err.to_string().contains("induction needs"), "{err}");
}

#[test]
fn a_mutual_recursor_needs_one_motive_per_type() {
    let env = mutual_group();
    let Declaration::Recursor(mut rec) = mutual_recursor(false) else {
        panic!("it is a recursor");
    };
    rec.num_motives = 1;
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&Declaration::Recursor(rec))
        .unwrap_err();
    assert!(err.to_string().contains("motives"), "{err}");
}

#[test]
fn a_mutual_recursor_needs_one_minor_per_constructor_of_the_whole_group() {
    let env = mutual_group();
    let Declaration::Recursor(mut rec) = mutual_recursor(false) else {
        panic!("it is a recursor");
    };
    rec.num_minors = 1;
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&Declaration::Recursor(rec))
        .unwrap_err();
    assert!(
        err.to_string().contains("2 constructors"),
        "the group has two constructors: {err}"
    );
}

#[test]
fn a_recursor_whose_rules_leave_its_own_group_is_refused() {
    let env = mutual_group();
    let Declaration::Recursor(mut rec) = mutual_recursor(false) else {
        panic!("it is a recursor");
    };
    rec.all = vec![Name::from_dotted("B")];
    rec.num_motives = 1;
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .check_declaration(&Declaration::Recursor(rec))
        .unwrap_err();
    assert!(
        err.to_string().contains("not in its own group"),
        "the rules are for `A.mk` and the group says `B`: {err}"
    );
}

#[test]
fn a_group_sees_its_own_members() {
    // Two recursors of a mutual group refer to each other, so neither is in
    // the environment when the other is checked. `with_group` makes them
    // visible to each other without adding them.
    let env = mutual_group();
    let mut tc = TypeChecker::new(&env);
    let group = vec![mutual_recursor(false)];
    let inside = tc.with_group(&group, |tc| {
        tc.infer_type(&Expr::const_("A.rec", vec![Level::of_nat(1)]))
            .is_ok()
    });
    assert!(inside, "a member of the group must be visible inside it");
    // And invisible outside it.
    assert!(
        tc.infer_type(&Expr::const_("A.rec", vec![Level::of_nat(1)]))
            .is_err(),
        "the group must not leak into the environment"
    );
}

// --- a nested inductive gets the weaker rule, not a free pass ------------

/// `inductive Tree | node : <field> → Tree`, declared as nested.
fn nested_tree(field: Expr) -> (Environment, ConstructorVal) {
    let mut env = Environment::new();
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("List"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::type_(0), Expr::type_(0)),
        is_unsafe: false,
    }));
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("False"),
        level_params: Vec::new(),
        ty: Expr::prop(),
        is_unsafe: false,
    }));
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Tree"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("Tree")],
        ctors: vec![Name::from_dotted("Tree.node")],
        num_nested: 1,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    }));
    let ctor = ConstructorVal {
        name: Name::from_dotted("Tree.node"),
        level_params: Vec::new(),
        ty: Expr::arrow(field, Expr::const_("Tree", vec![])),
        induct: Name::from_dotted("Tree"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    (env, ctor)
}

#[test]
fn a_nested_occurrence_is_accepted() {
    // `List Tree → Tree`. The strict rule refuses this, because `Tree` is an
    // argument of `List` and not the head. A nested declaration needs it.
    let tree = Expr::const_("Tree", vec![]);
    let (env, ctor) = nested_tree(Expr::const_("List", vec![]).app(tree));
    let mut tc = TypeChecker::new(&env);
    tc.check_positivity(&ctor)
        .unwrap_or_else(|err| panic!("a nested occurrence must pass: {err}"));
}

#[test]
fn a_nested_declaration_still_refuses_a_negative_occurrence() {
    // `(Tree → False) → Tree` is the shape that proves `False`. A nested
    // declaration gets a weaker rule, not a free pass.
    let tree = || Expr::const_("Tree", vec![]);
    let (env, ctor) = nested_tree(Expr::arrow(tree(), Expr::const_("False", vec![])));
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_positivity(&ctor).unwrap_err();
    assert!(matches!(err, TypeError::BadConstructor { .. }), "{err}");
}

// --- a constructor field must fit inside its inductive type --------------

#[test]
fn a_field_larger_than_its_inductive_type_is_refused() {
    // `inductive Small : Type` with a field in `Type 1`. The type would hold
    // something bigger than itself, which is the shape of Russell's paradox.
    let mut env = Environment::new();
    let small = || Expr::const_("Small", vec![]);
    env.add(inductive("Small", Expr::type_(0), &["Small.mk"]));
    let ctor = ConstructorVal {
        name: Name::from_dotted("Small.mk"),
        level_params: Vec::new(),
        // The field is `Type`, which lives in `Type 1`.
        ty: Expr::arrow(Expr::type_(0), small()),
        induct: Name::from_dotted("Small"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_field_universes(&ctor).unwrap_err();
    assert!(matches!(err, TypeError::FieldTooLarge { .. }), "{err}");
    assert!(err.to_string().contains("only reaches"), "{err}");
}

#[test]
fn a_prop_may_hold_anything() {
    // `Prop` is impredicative, so a proposition may quantify over any type.
    // See chapter 0, section 0.10.
    let mut env = Environment::new();
    env.add(inductive("P", Expr::prop(), &["P.mk"]));
    let ctor = ConstructorVal {
        name: Name::from_dotted("P.mk"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::type_(4), Expr::const_("P", vec![])),
        induct: Name::from_dotted("P"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let mut tc = TypeChecker::new(&env);
    assert!(tc.check_field_universes(&ctor).is_ok());
}

#[test]
fn the_level_order_decides_what_it_can_and_accepts_the_rest() {
    let u = Level::param("u");
    let v = Level::param("v");
    // Two closed levels compare by value, both ways.
    assert_eq!(Level::of_nat(1).is_leq(&Level::of_nat(2)), Some(true));
    assert_eq!(Level::of_nat(2).is_leq(&Level::of_nat(1)), Some(false));
    // The same level.
    assert_eq!(u.is_leq(&u), Some(true));
    // One branch of a `max` on the right is enough.
    assert_eq!(u.is_leq(&u.max(&v)), Some(true));
    assert_eq!(v.is_leq(&u.max(&v)), Some(true));
    // Every branch on the left must fit.
    assert_eq!(u.max(&v).is_leq(&u.max(&v)), Some(true));
    // Room to spare on the right.
    assert_eq!(u.is_leq(&u.succ()), Some(true));
    // `u+1 ≤ (max u v)+1` because `u ≤ max u v`.
    assert_eq!(u.succ().is_leq(&u.max(&v).succ()), Some(true));
    // Two unrelated parameters cannot be ordered, and the answer is honest.
    assert_eq!(u.is_leq(&v), None);
}
