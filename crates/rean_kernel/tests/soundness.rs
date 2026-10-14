//! Red team tests. Can a crafted input make the checker accept a lie?
//!
//! Every test here failed before these checks existed. The first one is the
//! reason the rest matter: our checker accepted a proof of `False`.

use rean_core::Name;
use rean_kernel::{
    AxiomVal, ConstructorVal, Declaration, Environment, Expr, InductiveVal, Level, Proj, QuotKind,
    QuotVal, RecursorRule, RecursorVal, Sub, TheoremVal, TypeChecker, TypeError, quot,
};

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
        value: Sub::new(p.clone()),
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
        value: Sub::new(p),
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
fn a_field_in_an_unrelated_universe_is_refused() {
    // inductive Big.{u, v} : Sort v where | mk : Sort u -> Big
    //
    // The field `Sort u` lives in `u+1`, and the type promises `v`. No value
    // of `v` makes that hold for every `u`, so Lean refuses it and so must
    // we: `Big.{2, 1}` would put a `Type 1` inside a `Type 0`, which is
    // Russell's paradox again.
    let mut env = Environment::new();
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Big"),
        level_params: vec![Name::from_dotted("u"), Name::from_dotted("v")],
        ty: Expr::Sort(Level::param("v")),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("Big")],
        ctors: vec![Name::from_dotted("Big.mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    let ctor = ConstructorVal {
        name: Name::from_dotted("Big.mk"),
        level_params: vec![Name::from_dotted("u"), Name::from_dotted("v")],
        ty: Expr::arrow(
            Expr::Sort(Level::param("u")),
            Expr::const_("Big", vec![Level::param("u"), Level::param("v")]),
        ),
        induct: Name::from_dotted("Big"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_field_universes(&ctor).unwrap_err();
    assert!(matches!(err, TypeError::FieldTooLarge { .. }), "{err}");
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
    // Two unrelated parameters are **ordered**, and the answer is no: `u` is
    // not at most `v`, because `u` may be `1` while `v` is `0`.
    assert_eq!(u.is_leq(&v), Some(false));
    // A plain number needs the room on the right, and a parameter may be zero.
    assert_eq!(Level::of_nat(2).is_leq(&u.succ()), Some(false));
    assert_eq!(Level::of_nat(2).is_leq(&u.succ().succ()), Some(true));
    // `imax` is the shape that is left undecided, because it is two levels at
    // once: `imax u v` is zero when `v` is zero and `max u v` otherwise.
    assert_eq!(u.is_leq(&u.imax(&v)), None);
}

// --- the four quotient declarations -------------------------------------

/// An environment that holds Lean's `Quot`, `Quot.mk` and `Eq`.
///
/// The two quotient types come from the kernel's own table, and the arena
/// checks that table against the real Lean: six of its `good` tests declare
/// these four, and so does `fixtures/lean4export/shapes.ndjson`.
///
/// `Eq` is here because the type of `Quot.lift` speaks about it.
fn with_quot() -> Environment {
    let mut env = Environment::new();
    let u = vec![Name::from_dotted("u")];
    for kind in [QuotKind::Type, QuotKind::Ctor] {
        env.add(Declaration::Quot(QuotVal {
            name: Name::from_dotted(quot::name_of(kind)),
            level_params: u.clone(),
            ty: quot::declared_type(kind, &u).expect("the kernel knows this type"),
            kind,
        }));
    }
    // Eq.{u} : {α : Sort u} → α → α → Prop
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("Eq"),
        level_params: u,
        ty: Expr::forall(
            "α",
            Expr::Sort(Level::param("u")),
            Expr::arrow(Expr::bvar(0), Expr::arrow(Expr::bvar(0), Expr::prop())),
        ),
        is_unsafe: false,
    }));
    env
}

#[test]
fn a_quotient_declaration_with_a_type_of_its_own_is_refused() {
    // `quot_step` rewrites `Quot.ind p (Quot.mk r a)` to `p a` and **trusts
    // the result**, exactly as the ι rule trusts a recursor. So a `Quot.ind`
    // with another type is an untracked axiom. Here it is `{α : Sort u} → α`,
    // which proves anything at all.
    let env = with_quot();
    let forged = Declaration::Quot(QuotVal {
        name: Name::from_dotted("Quot.ind"),
        level_params: vec![Name::from_dotted("u")],
        ty: Expr::forall("α", Expr::Sort(Level::param("u")), Expr::bvar(0)),
        kind: QuotKind::Ind,
    });
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&forged).unwrap_err();
    assert!(matches!(err, TypeError::BadQuot { .. }), "{err}");
    assert!(err.to_string().contains("has the type"), "{err}");
}

#[test]
fn a_quotient_rule_under_another_name_is_refused() {
    // The rule belongs to `Quot.lift`, and the kernel finds it by the kind of
    // the declaration. Without the name, a file could declare `Evil.lift`
    // beside the real one and get a second eliminator, whose type it chooses.
    let env = with_quot();
    let levels = vec![Name::from_dotted("u"), Name::from_dotted("v")];
    let rogue = Declaration::Quot(QuotVal {
        name: Name::from_dotted("Evil.lift"),
        level_params: levels.clone(),
        ty: quot::declared_type(QuotKind::Lift, &levels).expect("the kernel knows this type"),
        kind: QuotKind::Lift,
    });
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&rogue).unwrap_err();
    assert!(matches!(err, TypeError::BadQuot { .. }), "{err}");
}

#[test]
fn the_real_quotient_declarations_are_accepted() {
    // The other direction, and the one that would break first if the table
    // were wrong.
    let env = with_quot();
    for (kind, levels) in [(QuotKind::Lift, vec!["u", "v"]), (QuotKind::Ind, vec!["u"])] {
        let levels: Vec<Name> = levels.into_iter().map(Name::from_dotted).collect();
        let decl = Declaration::Quot(QuotVal {
            name: Name::from_dotted(quot::name_of(kind)),
            level_params: levels.clone(),
            ty: quot::declared_type(kind, &levels).expect("the kernel knows this type"),
            kind,
        });
        let mut tc = TypeChecker::new(&env);
        tc.check_declaration(&decl)
            .unwrap_or_else(|err| panic!("{} must pass: {err}", quot::name_of(kind)));
    }
}

// --- eta on a dependent function, found in the Lean prelude --------------

/// An environment with `A : Type`, `P : A → Prop`, and `B : Type`.
fn dependent_env() -> Environment {
    let mut env = Environment::new();
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("A"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("B"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("P"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::const_("A", vec![]), Expr::prop()),
        is_unsafe: false,
    }));
    env
}

#[test]
fn eta_works_together_with_proof_irrelevance() {
    // `f` and `fun a h => f a (g a h)` are the same function.
    //
    // Eta strips the two binders, and then the second argument matches only
    // because `P a` is a proposition and all its proofs are equal. So this
    // needs **both** rules at once, and it needs them to work under a binder.
    //
    // The first version of `eta_eq` stayed in de Bruijn and left both sides
    // open, so proof irrelevance could not ask for a type and declined. That
    // made `Option.pbind_join` of the Lean prelude fail on a term that is
    // perfectly correct. `eta_eq` now opens the binder into a free variable.
    let env = dependent_env();
    let mut tc = TypeChecker::new(&env);
    let a_ty = || Expr::const_("A", vec![]);
    let p_of = |x: Expr| Expr::const_("P", vec![]).app(x);

    // `f : (a : A) → P a → B`
    let f = Expr::FVar(tc.push_local(
        "f",
        Expr::forall(
            "a",
            a_ty(),
            Expr::arrow(p_of(Expr::bvar(0)), Expr::const_("B", vec![])),
        ),
    ));
    // `g : (a : A) → P a → P a`, some other way to make the same proof.
    let g = Expr::FVar(tc.push_local(
        "g",
        Expr::forall(
            "a",
            a_ty(),
            Expr::arrow(p_of(Expr::bvar(0)), p_of(Expr::bvar(0))),
        ),
    ));

    // `fun a h => f a (g a h)`
    let wrapped = Expr::lam(
        "a",
        a_ty(),
        Expr::lam(
            "h",
            p_of(Expr::bvar(0)),
            f.clone()
                .app(Expr::bvar(1))
                .app(g.app(Expr::bvar(1)).app(Expr::bvar(0))),
        ),
    );

    assert!(
        tc.is_def_eq(&wrapped, &f).unwrap(),
        "eta and proof irrelevance together"
    );
    assert!(tc.is_def_eq(&f, &wrapped).unwrap(), "and in either order");
}

#[test]
fn eta_still_says_no_for_a_different_function() {
    let env = dependent_env();
    let mut tc = TypeChecker::new(&env);
    let a_ty = || Expr::const_("A", vec![]);
    let fun_ty = || Expr::arrow(a_ty(), Expr::const_("B", vec![]));
    let f = Expr::FVar(tc.push_local("f", fun_ty()));
    let other = Expr::FVar(tc.push_local("other", fun_ty()));
    // `fun a => f a` is `f`, and it is not `other`.
    let wrapped = Expr::lam("a", a_ty(), f.clone().app(Expr::bvar(0)));
    assert!(tc.is_def_eq(&wrapped, &f).unwrap());
    assert!(!tc.is_def_eq(&wrapped, &other).unwrap());
}

#[test]
fn a_comparison_helper_declines_rather_than_errors_on_an_open_term() {
    // `struct_eta_eq` asks for the type of one side, and a loose bound variable
    // has no type. Without a guard it returned an error, and that error left
    // `is_def_eq` entirely, so a whole declaration failed for a rule that did
    // not even apply.
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
    // A constructor application against an open term. The rule cannot apply,
    // and the answer must be `false` rather than an error.
    let built = Expr::const_("S.mk", vec![]).app(Expr::prop());
    let open = Expr::bvar(0);
    assert_eq!(tc.is_def_eq(&built, &open), Ok(false));
    assert_eq!(tc.is_def_eq(&open, &built), Ok(false));
}

// --- string literals -----------------------------------------------------

#[test]
fn the_kernel_computes_on_a_string_literal() {
    // `String.utf8ByteSize "" ≡ 0` is what `String.utf8ByteSize_empty` of the
    // Lean prelude needs.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let call = |name: &str, text: &str| Expr::const_(name, vec![]).app(Expr::str(text));
    assert_eq!(
        tc.whnf(&call("String.utf8ByteSize", "")).unwrap().pretty(),
        "0"
    );
    assert_eq!(
        tc.whnf(&call("String.utf8ByteSize", "abc"))
            .unwrap()
            .pretty(),
        "3"
    );
    // A character counts once and its bytes count separately. `α` is two bytes.
    assert_eq!(
        tc.whnf(&call("String.utf8ByteSize", "α")).unwrap().pretty(),
        "2"
    );
    assert_eq!(tc.whnf(&call("String.length", "α")).unwrap().pretty(), "1");
    assert_eq!(
        tc.whnf(&call("String.length", "abc")).unwrap().pretty(),
        "3"
    );
    // A function we do not compute stays stuck.
    let other = call("String.wat", "abc");
    assert!(tc.whnf(&other).unwrap().alpha_eq(&other));
    // And so does a call whose argument is not a literal.
    let open = Expr::const_("String.length", vec![]).app(Expr::prop());
    assert!(tc.whnf(&open).unwrap().alpha_eq(&open));
}

// --- chapter 28: the arena ----------------------------------------------
//
// Every test below is a declaration that this checker **accepted** until the
// Lean Kernel Arena said otherwise. Six of the fourteen it caught are here;
// the rest are in `tests/limits.rs` and in the arena harness itself.

/// `inductive Proof : Prop` with one constructor that carries `n` fields.
fn prop_structure(fields: &[Expr]) -> Environment {
    let mut env = Environment::new();
    env.add(inductive("U", Expr::type_(0), &["U.u"]));
    env.add(constructor("U.u", "U", u()));
    env.add(inductive("Proof", Expr::prop(), &["Proof.mk"]));
    let mut ty = Expr::const_("Proof", vec![]);
    for field in fields.iter().rev() {
        ty = Expr::forall("f", field.clone(), ty);
    }
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("Proof.mk"),
        level_params: Vec::new(),
        ty,
        induct: Name::from_dotted("Proof"),
        cidx: 0,
        num_params: 0,
        num_fields: fields.len() as u32,
        is_unsafe: false,
    }));
    env
}

/// `proj Proof index p`, where `p` is a free variable of type `Proof`.
fn project(tc: &mut TypeChecker, index: u32) -> Result<Expr, TypeError> {
    let p = Expr::FVar(tc.push_local("p", Expr::const_("Proof", vec![])));
    tc.infer_type(&Expr::Proj(Proj {
        structure: Name::from_dotted("Proof"),
        index,
        value: Sub::new(p),
    }))
}

#[test]
fn a_proof_may_not_be_asked_for_its_data() {
    // The lie, which is `bad/bugs/proj-of-imax-prop` of the arena. A `Prop`
    // with a data field, and a projection that reads the field out.
    //
    // Proof irrelevance makes any two proofs of `Proof` equal, so the two
    // values of the field would be equal as well, and that is `False` in four
    // more lines.
    let env = prop_structure(&[u()]);
    let mut tc = TypeChecker::new(&env);
    assert!(matches!(
        project(&mut tc, 0),
        Err(TypeError::ProofWithData { index: 0, .. })
    ));
}

#[test]
fn a_proof_may_be_asked_for_its_proofs() {
    // The same shape with a field that is itself a `Prop`. `And.left` is this
    // test, and refusing it would refuse the Lean prelude.
    let env = prop_structure(&[Expr::const_("Proof", vec![])]);
    let mut tc = TypeChecker::new(&env);
    assert!(project(&mut tc, 0).is_ok());
}

#[test]
fn the_fields_on_the_way_are_asked_as_well() {
    // The pair the arena spends six tests on, `tutorial/089` to `094`.
    //
    // Field 1 is a proof in both halves of this test, and its type is the same
    // `Proof` both times. What differs is field 0, which the walk steps over,
    // and whether anything after it mentions it.
    let data = u();

    // Nothing mentions field 0, so reaching field 1 substitutes nothing.
    let env = prop_structure(&[data.clone(), Expr::const_("Proof", vec![])]);
    let mut tc = TypeChecker::new(&env);
    assert!(project(&mut tc, 1).is_ok(), "nothing mentions field 0");

    // Now field 1 mentions field 0. Reaching field 1 means putting `p.0` into
    // its type, and `p.0` is the projection the test above refuses.
    let mentions = Expr::forall("_", Expr::bvar(0).app(Expr::bvar(0)), Expr::prop());
    let env = prop_structure(&[Expr::arrow(data, Expr::prop()), mentions]);
    let mut tc = TypeChecker::new(&env);
    assert!(
        matches!(
            project(&mut tc, 1),
            Err(TypeError::ProofWithData { index: 0, .. })
        ),
        "field 1 mentions field 0, which is data"
    );
}

#[test]
fn a_recursor_must_carry_the_name_of_its_own_type() {
    // `tutorial/136_misnamed_rec_user`. The recursor is correct in every other
    // way, and it is not the one Lean would have built, so in Lean's
    // environment the name `U.rec` is still free for a second rule.
    let mut env = base();
    let Declaration::Recursor(mut rec) = recursor(honest_recursor_type(), honest_rhs(), 1) else {
        unreachable!()
    };
    let mut tc = TypeChecker::new(&env);
    assert!(
        tc.check_recursor(&rec).is_ok(),
        "the honest one is accepted"
    );
    rec.name = Name::from_dotted("U.not_rec");
    let err = tc.check_recursor(&rec).unwrap_err();
    assert!(matches!(err, TypeError::BadRecursor { .. }), "{err:?}");
    env.add(Declaration::Recursor(rec));
}

#[test]
fn a_constructor_must_belong_to_the_type_it_names() {
    // `other/orphan-ctor`. `False` is declared with no constructors, and a
    // constructor of a type that is not in the file at all claims to build it.
    // Nothing in the term rules refuses that: the type of `rogue` **is**
    // `False`.
    let env = base();
    let rogue = Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("rogue"),
        level_params: Vec::new(),
        ty: Expr::const_("False", vec![]),
        induct: Name::from_dotted("Orphan"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    });
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&rogue).unwrap_err();
    assert!(
        matches!(err, TypeError::OrphanConstructor { .. }),
        "{err:?}"
    );
}

#[test]
fn a_theorem_must_state_a_proposition() {
    // `tutorial/012_nonPropThm`. The type is a good type and the value has
    // that type, and the pair is still wrong: nobody ever reads the value of a
    // theorem, because proof irrelevance says there is nothing to read.
    let env = base();
    let not_a_statement = Declaration::Theorem(TheoremVal {
        name: Name::from_dotted("nonPropThm"),
        level_params: Vec::new(),
        ty: Expr::prop(),
        value: Expr::forall("x", Expr::prop(), Expr::bvar(0)),
        all: Vec::new(),
    });
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&not_a_statement).unwrap_err();
    assert!(matches!(err, TypeError::NotAProposition { .. }), "{err:?}");
}

#[test]
fn a_declaration_may_not_be_its_own_proof() {
    // `tutorial/014_selfProof`, which is the whole attack:
    //
    // ```text
    // theorem selfProof : ∀ (p : Prop), p := selfProof
    // ```
    //
    // The group of a theorem is itself, and `with_group` makes a group visible
    // to its own members for the sake of a mutual inductive. So the proof was
    // in the environment while it was being checked.
    let env = base();
    let itself = Declaration::Theorem(TheoremVal {
        name: Name::from_dotted("selfProof"),
        level_params: Vec::new(),
        ty: Expr::forall("p", Expr::prop(), Expr::bvar(0)),
        value: Expr::const_("selfProof", vec![]),
        all: vec![Name::from_dotted("selfProof")],
    });
    let mut tc = TypeChecker::new(&env);
    let group = vec![itself.clone()];
    let err = tc
        .with_group(&group, |tc| tc.check_declaration(&itself))
        .unwrap_err();
    assert_eq!(
        err,
        TypeError::SelfReference(Name::from_dotted("selfProof"))
    );
}

#[test]
fn an_inductive_declaration_must_describe_a_type() {
    // Three lies in one test, and the arena has one test for each.
    let env = base();
    let mut tc = TypeChecker::new(&env);

    // `tutorial/139_DupConCon`: one name, listed as both constructors. The
    // count of constructors is what decides whether a type is a subsingleton
    // and whether it may eliminate into `Type`, so a type that reports two and
    // has one is a lie in both directions.
    let twice = inductive("Dup", Expr::prop(), &["Dup.mk", "Dup.mk"]);
    assert!(matches!(
        tc.check_declaration(&twice),
        Err(TypeError::BadInductive { .. })
    ));

    // `tutorial/049_inductTooFewParams`: two parameters and one binder.
    let Declaration::Inductive(mut val) = inductive("Few", Expr::prop(), &[]) else {
        unreachable!()
    };
    val.ty = Expr::forall("x", Expr::prop(), Expr::prop());
    val.num_params = 2;
    assert!(matches!(
        tc.check_declaration(&Declaration::Inductive(val.clone())),
        Err(TypeError::BadInductive { .. })
    ));

    // One parameter and one binder is the same declaration, told truthfully.
    val.num_params = 1;
    assert!(tc.check_declaration(&Declaration::Inductive(val)).is_ok());

    // `tutorial/047_inductBadNonSort2`: a type that ends in a term of type
    // `Sort 1` rather than in a `Sort`. Then the type is in no universe, and
    // the field check has no limit to compare a field against.
    env_with_an_axiom_ending(&env);
}

/// Checks the third lie of the test above, which needs one more declaration.
fn env_with_an_axiom_ending(base: &Environment) {
    let mut env = base.clone();
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("aType"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    let ends_in_a_term = inductive("NotASort", Expr::const_("aType", vec![]), &[]);
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&ends_in_a_term).unwrap_err();
    assert!(matches!(err, TypeError::BadInductive { .. }), "{err:?}");
}
