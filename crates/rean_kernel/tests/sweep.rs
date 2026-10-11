//! One test per arm.
//!
//! A `match` arm that no test reaches is a claim nobody checked. This file
//! walks every variant of `Expr`, `Level`, `Declaration`, and `TypeError`
//! through every operation that handles them.

use rean_core::Name;
use rean_kernel::positivity::{self, PositivityError};
use rean_kernel::{
    AxiomVal, ConstructorVal, Declaration, DefinitionSafety, DefinitionVal, Environment, Expr,
    FVarId, InductiveVal, Level, Literal, LocalContext, MVarId, OpaqueVal, Proj, QuotKind, QuotVal,
    RecursorRule, RecursorVal, ReducibilityHints, Sub, TheoremVal, TypeChecker, TypeError,
};

/// One term of every `Expr` variant, in a term that holds them all.
fn one_of_each() -> Vec<Expr> {
    let nat = Expr::const_("Nat", vec![]);
    vec![
        Expr::bvar(0),
        Expr::FVar(FVarId(3)),
        Expr::MVar(MVarId(4)),
        Expr::sort(Level::param("u")),
        Expr::const_("List", vec![Level::param("u")]),
        nat.clone().app(nat.clone()),
        Expr::lam("x", nat.clone(), Expr::bvar(0)),
        Expr::forall("x", nat.clone(), Expr::bvar(0)),
        Expr::let_("x", nat.clone(), nat.clone(), Expr::bvar(0)),
        Expr::nat("7"),
        Expr::str("hi"),
        Expr::Proj(Proj {
            structure: Name::from_dotted("Prod"),
            index: 1,
            value: Sub::new(nat),
        }),
    ]
}

#[test]
fn every_expr_variant_survives_every_operation() {
    let params = [Name::from_dotted("u")];
    let args = [Level::of_nat(2)];
    for term in one_of_each() {
        // Each operation must return something, and must not panic.
        let lifted = term.lift(0, 1);
        let instantiated = term.instantiate(&Expr::prop());
        let abstracted = term.abstract_fvar(FVarId(3));
        let with_levels = term.instantiate_levels(&params, &args);
        assert!(!term.pretty().is_empty());
        assert!(!lifted.pretty().is_empty());
        assert!(!instantiated.pretty().is_empty());
        assert!(!abstracted.pretty().is_empty());
        assert!(!with_levels.pretty().is_empty());
        // A term is always alpha equal to itself.
        assert!(term.alpha_eq(&term), "{}", term.pretty());
        // `lift` by zero is the identity.
        assert!(term.lift(0, 0).alpha_eq(&term));
        // `has_loose_bvars` must agree with `has_loose_bvar(0)` for index 0.
        if term.has_loose_bvar(0) {
            assert!(term.has_loose_bvars());
        }
    }
}

#[test]
fn alpha_eq_separates_every_pair_of_different_variants() {
    let terms = one_of_each();
    for (i, left) in terms.iter().enumerate() {
        for (j, right) in terms.iter().enumerate() {
            if i != j {
                assert!(
                    !left.alpha_eq(right),
                    "{} must differ from {}",
                    left.pretty(),
                    right.pretty()
                );
            }
        }
    }
}

#[test]
fn alpha_eq_looks_inside_every_variant() {
    let nat = Expr::const_("Nat", vec![]);
    let other = Expr::const_("Int", vec![]);
    // A difference deep inside each compound variant must show up.
    assert!(
        !nat.clone()
            .app(nat.clone())
            .alpha_eq(&nat.clone().app(other.clone()))
    );
    assert!(
        !Expr::lam("x", nat.clone(), Expr::bvar(0)).alpha_eq(&Expr::lam(
            "x",
            other.clone(),
            Expr::bvar(0)
        ))
    );
    assert!(
        !Expr::let_("x", nat.clone(), nat.clone(), Expr::bvar(0)).alpha_eq(&Expr::let_(
            "x",
            nat.clone(),
            other.clone(),
            Expr::bvar(0)
        ))
    );
    let proj = |index: u32, value: Expr| {
        Expr::Proj(Proj {
            structure: Name::from_dotted("Prod"),
            index,
            value: Sub::new(value),
        })
    };
    assert!(!proj(0, nat.clone()).alpha_eq(&proj(1, nat.clone())));
    assert!(!proj(0, nat.clone()).alpha_eq(&proj(0, other)));
    assert!(proj(0, nat).alpha_eq(&proj(0, Expr::const_("Nat", vec![]))));
    // A different universe argument count must differ.
    assert!(!Expr::const_("L", vec![]).alpha_eq(&Expr::const_("L", vec![Level::Zero])));
    assert!(!Expr::FVar(FVarId(1)).alpha_eq(&Expr::FVar(FVarId(2))));
    assert!(!Expr::MVar(MVarId(1)).alpha_eq(&Expr::MVar(MVarId(2))));
    assert!(!Expr::nat("1").alpha_eq(&Expr::nat("2")));
}

#[test]
fn instantiate_levels_reaches_every_variant() {
    let params = [Name::from_dotted("u")];
    let args = [Level::of_nat(1)];
    let open = Expr::sort(Level::param("u"));
    // The parameter must be gone from each compound shape.
    for term in [
        open.clone().app(open.clone()),
        Expr::lam("x", open.clone(), open.clone()),
        Expr::forall("x", open.clone(), open.clone()),
        Expr::let_("x", open.clone(), open.clone(), open.clone()),
        Expr::Proj(Proj {
            structure: Name::from_dotted("S"),
            index: 0,
            value: Sub::new(open.clone()),
        }),
        Expr::const_("L", vec![Level::param("u")]),
    ] {
        let done = term.instantiate_levels(&params, &args);
        // No open level may survive the substitution.
        let text = done.pretty();
        assert!(!text.contains("Sort u"), "{text}");
        assert!(!text.contains("{u}"), "{text}");
        assert_ne!(text, term.pretty(), "the term must change");
    }
    // With no parameter the term comes back untouched.
    assert!(open.instantiate_levels(&[], &[]).alpha_eq(&open));
}

#[test]
fn lift_and_instantiate_and_abstract_reach_every_binder() {
    let nat = Expr::const_("Nat", vec![]);
    let f = FVarId(9);
    let holder = Expr::let_(
        "x",
        Expr::FVar(f),
        Expr::FVar(f),
        Expr::lam(
            "y",
            Expr::FVar(f),
            Expr::Proj(Proj {
                structure: Name::from_dotted("S"),
                index: 0,
                value: Sub::new(Expr::FVar(f)),
            }),
        ),
    );
    // Every occurrence becomes a bound variable.
    let closed = holder.abstract_fvar(f);
    assert_eq!(closed.pretty().matches("_f9").count(), 0);
    // And comes back with `instantiate`.
    let open = closed.instantiate(&Expr::FVar(f));
    assert!(open.alpha_eq(&holder), "{}", open.pretty());
    // `lift` walks the same shapes.
    assert!(!holder.lift(0, 2).pretty().is_empty());
    assert!(!nat.lift(0, 2).pretty().is_empty());

    // `holder` is closed, so `lift` answers "nothing changed" before it reaches
    // the `let` or the projection. A term with a **loose** variable in each of
    // those places makes it walk them.
    let open = Expr::let_(
        "x",
        Expr::bvar(0),
        Expr::bvar(0),
        Expr::Proj(Proj {
            structure: Name::from_dotted("S"),
            index: 0,
            value: Sub::new(Expr::bvar(1)),
        }),
    );
    // Index 0 of the value becomes 2. The body is under the `let` binder, so
    // its index 1 counts from one deeper and becomes 3.
    assert_eq!(open.lift(0, 2).pretty(), "let x : #2 := #2; #3.1");
}

#[test]
fn a_subterm_reports_its_cached_numbers() {
    // Every subterm carries two numbers, and both come from its children. See
    // chapter 9.
    let nat = Expr::const_("Nat", vec![]);
    let leaf = Sub::new(nat.clone());
    assert_eq!(leaf.loose(), 0, "a constant has no loose variable");
    assert_eq!(leaf.size(), 1, "a constant is one node");

    // `fun x => #1` has one loose index, and the binder discharges index 0, so
    // the range of the whole term is 1.
    let under = Sub::new(Expr::lam("x", nat.clone(), Expr::bvar(1)));
    assert_eq!(under.loose(), 1);
    // The lambda, its binder type, and the body.
    assert_eq!(under.size(), 3);

    // An application takes the larger range and the sum of the sizes.
    let app = Sub::new(Expr::bvar(4).app(Expr::bvar(2)));
    assert_eq!(app.loose(), 5);
    assert_eq!(app.size(), 3);
}

// --- Level ---------------------------------------------------------------

#[test]
fn substitute_reaches_every_level_former() {
    let u = Name::from_dotted("u");
    let v = Name::from_dotted("v");
    let params = [u.clone(), v.clone()];
    let args = [Level::of_nat(1), Level::of_nat(3)];
    let at = |level: Level| level.substitute(&params, &args).to_nat();
    assert_eq!(at(Level::Zero), Some(0));
    assert_eq!(at(Level::param("u")), Some(1));
    assert_eq!(at(Level::param("v")), Some(3));
    assert_eq!(at(Level::param("u").succ()), Some(2));
    assert_eq!(at(Level::param("u").max(&Level::param("v"))), Some(3));
    assert_eq!(at(Level::param("u").imax(&Level::param("v"))), Some(3));
    assert_eq!(at(Level::param("v").imax(&Level::Zero)), Some(0));
    // A parameter that is not in the list stays as it is.
    assert!(!Level::param("w").substitute(&params, &args).is_closed());
    // A list that is too short gives zero rather than panic.
    assert_eq!(
        Level::param("v").substitute(&params, &args[..1]).to_nat(),
        Some(0)
    );
}

#[test]
fn normalize_reaches_every_rule() {
    let u = Level::param("u");
    let v = Level::param("v");
    // A closed level becomes a plain chain.
    assert_eq!(
        Level::of_nat(2).max(&Level::of_nat(1)).normalize(),
        Level::of_nat(2)
    );
    // `max` with itself, and with zero on either side.
    assert_eq!(u.max(&u).normalize(), u);
    assert_eq!(u.max(&Level::Zero).normalize(), u);
    assert_eq!(Level::Zero.max(&u).normalize(), u);
    // `max` of two different parameters stays.
    assert_eq!(u.max(&v).normalize(), u.max(&v).normalize());
    assert!(!u.max(&v).normalize().is_closed());
    // `imax` with zero on the right collapses.
    assert_eq!(u.imax(&Level::Zero).normalize(), Level::Zero);
    // `imax` with a successor on the right acts like `max`.
    assert_eq!(u.imax(&v.succ()).normalize(), u.max(&v.succ()).normalize());
    // `imax` with the same level on both sides.
    assert_eq!(u.imax(&u).normalize(), u);
    // `imax` of two different parameters stays.
    assert!(!u.imax(&v).normalize().is_closed());
    // A successor of an open level normalizes inside.
    assert_eq!(u.max(&Level::Zero).succ().normalize(), u.succ());
    // Zero and a bare parameter are already normal.
    assert_eq!(Level::Zero.normalize(), Level::Zero);
    assert_eq!(u.normalize(), u);
}

#[test]
fn level_display_covers_every_former() {
    let u = Level::param("u");
    assert_eq!(Level::Zero.to_string(), "0");
    assert_eq!(u.to_string(), "u");
    assert_eq!(u.succ().to_string(), "u+1");
    assert_eq!(u.max(&Level::param("v")).to_string(), "max u v");
    assert_eq!(u.imax(&Level::param("v")).to_string(), "imax u v");
    assert_eq!(Level::of_nat(5).to_string(), "5");
}

// --- Declaration ---------------------------------------------------------

/// One declaration of every kind.
fn every_declaration() -> Vec<Declaration> {
    let name = |text: &str| Name::from_dotted(text);
    let ty = Expr::prop();
    vec![
        Declaration::Axiom(AxiomVal {
            name: name("A"),
            level_params: vec![name("u")],
            ty: ty.clone(),
            is_unsafe: false,
        }),
        Declaration::Definition(DefinitionVal {
            name: name("D"),
            level_params: vec![name("u")],
            ty: ty.clone(),
            value: ty.clone(),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name("D")],
        }),
        Declaration::Theorem(TheoremVal {
            name: name("T"),
            level_params: vec![name("u")],
            ty: ty.clone(),
            value: ty.clone(),
            all: vec![name("T")],
        }),
        Declaration::Opaque(OpaqueVal {
            name: name("O"),
            level_params: vec![name("u")],
            ty: ty.clone(),
            value: ty.clone(),
            is_unsafe: true,
            all: vec![name("O")],
        }),
        Declaration::Quot(QuotVal {
            name: name("Q"),
            level_params: vec![name("u")],
            ty: ty.clone(),
            kind: QuotKind::Type,
        }),
        Declaration::Inductive(InductiveVal {
            name: name("I"),
            level_params: vec![name("u")],
            ty: ty.clone(),
            num_params: 0,
            num_indices: 0,
            all: vec![name("I")],
            ctors: vec![name("I.mk")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
        Declaration::Constructor(ConstructorVal {
            name: name("I.mk"),
            level_params: vec![name("u")],
            ty: ty.clone(),
            induct: name("I"),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }),
        Declaration::Recursor(RecursorVal {
            name: name("I.rec"),
            level_params: vec![name("u")],
            ty,
            all: vec![name("I")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: name("I.mk"),
                num_fields: 0,
                rhs: Expr::prop(),
            }],
            k: false,
            is_unsafe: false,
        }),
    ]
}

#[test]
fn every_declaration_answers_every_accessor() {
    let mut env = Environment::new();
    for decl in every_declaration() {
        assert!(!decl.name().is_anonymous());
        assert_eq!(decl.level_params().len(), 1);
        assert_eq!(decl.ty(), &Expr::prop());
        assert!(!decl.kind_label().is_empty());
        env.add(decl);
    }
    assert_eq!(env.len(), 8);
    assert!(!env.is_empty());
    assert!(env.contains(&Name::from_dotted("I.rec")));
    assert!(env.get(&Name::from_dotted("nope")).is_none());
}

#[test]
fn only_a_definition_or_a_theorem_unfolds() {
    for decl in every_declaration() {
        let should = matches!(decl, Declaration::Definition(_) | Declaration::Theorem(_));
        assert_eq!(
            decl.unfoldable_value().is_some(),
            should,
            "{} unfolded wrongly",
            decl.kind_label()
        );
    }
}

#[test]
fn the_inductive_lookups_handle_every_miss() {
    let mut env = Environment::new();
    for decl in every_declaration() {
        env.add(decl);
    }
    // The happy path.
    assert!(env.inductive_of_ctor(&Name::from_dotted("I.mk")).is_some());
    assert!(env.sole_ctor(&Name::from_dotted("I")).is_some());
    // A name that is not a constructor.
    assert!(env.inductive_of_ctor(&Name::from_dotted("D")).is_none());
    // A name that is not in the environment at all.
    assert!(env.inductive_of_ctor(&Name::from_dotted("nope")).is_none());
    assert!(env.sole_ctor(&Name::from_dotted("nope")).is_none());
    // A name that is not an inductive type.
    assert!(env.sole_ctor(&Name::from_dotted("D")).is_none());

    // An inductive with two constructors has no sole constructor.
    let mut two = Environment::new();
    two.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Pair"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: Vec::new(),
        ctors: vec![Name::from_dotted("a"), Name::from_dotted("b")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    assert!(two.sole_ctor(&Name::from_dotted("Pair")).is_none());
}

#[test]
fn a_recursor_rule_lookup_can_miss() {
    let Declaration::Recursor(rec) = &every_declaration()[7] else {
        panic!("the last one is a recursor");
    };
    assert!(rec.rule_for(&Name::from_dotted("I.mk")).is_some());
    assert!(rec.rule_for(&Name::from_dotted("other")).is_none());
}

// --- TypeError -----------------------------------------------------------

#[test]
fn every_error_variant_has_a_message() {
    let term = Box::new(Expr::prop());
    let errors = vec![
        TypeError::LooseBVar(2),
        TypeError::UnknownFVar(FVarId(1)),
        TypeError::MetavariableLeft(MVarId(2)),
        TypeError::UnknownConstant(Name::from_dotted("Nat")),
        TypeError::LevelArity {
            name: Name::from_dotted("List"),
            expected: 1,
            got: 0,
        },
        TypeError::NotAType {
            term: term.clone(),
            got: term.clone(),
        },
        TypeError::NotAFunction {
            term: term.clone(),
            got: term.clone(),
        },
        TypeError::NotAStructure {
            term: term.clone(),
            got: term.clone(),
        },
        TypeError::BadProjection {
            structure: Name::from_dotted("Prod"),
            index: 4,
        },
        TypeError::TypeMismatch {
            term: term.clone(),
            expected: term.clone(),
            got: term,
        },
        TypeError::ReductionLimit,
        TypeError::BadConstructor {
            ctor: Name::from_dotted("Bad.mk"),
            inductive: Name::from_dotted("Bad"),
            reason: PositivityError::NotStrictlyPositive { field: 0 },
        },
        TypeError::BadConstructor {
            ctor: Name::from_dotted("Bad.mk"),
            inductive: Name::from_dotted("Bad"),
            reason: PositivityError::TooFewBinders { expected: 2 },
        },
        TypeError::BadConstructor {
            ctor: Name::from_dotted("Bad.mk"),
            inductive: Name::from_dotted("Bad"),
            reason: PositivityError::WrongResult,
        },
    ];
    let ctx = LocalContext::new();
    for error in &errors {
        assert!(!error.to_string().is_empty(), "{error:?}");
        assert!(!error.render(&ctx).is_empty(), "{error:?}");
        // Both roads must agree on the shape of the message.
        assert_eq!(
            error.to_string().lines().count(),
            error.render(&ctx).lines().count()
        );
    }
    assert_eq!(errors.len(), 14);
}

// --- the checker error paths ---------------------------------------------

#[test]
fn an_unknown_free_variable_is_an_error() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let err = tc.infer_type(&Expr::FVar(FVarId(42))).unwrap_err();
    assert_eq!(err, TypeError::UnknownFVar(FVarId(42)));
}

#[test]
fn a_metavariable_is_an_error() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let err = tc.infer_type(&Expr::MVar(MVarId(7))).unwrap_err();
    assert_eq!(err, TypeError::MetavariableLeft(MVarId(7)));
}

#[test]
fn a_string_literal_has_type_string() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(
        tc.infer_type(&Expr::str("hi")).unwrap(),
        Expr::const_("String", vec![])
    );
}

#[test]
fn a_projection_of_something_that_is_not_a_structure_fails() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let term = Expr::Proj(Proj {
        structure: Name::from_dotted("Prod"),
        index: 0,
        value: Sub::new(Expr::prop()),
    });
    // The type of `Prop` is `Type`, whose head is a sort and not a constant.
    let err = tc.infer_type(&term).unwrap_err();
    assert!(matches!(err, TypeError::NotAStructure { .. }), "{err}");
}

#[test]
fn a_projection_past_the_last_field_fails() {
    // `PUnit` has one constructor with no field, so field 0 does not exist.
    let mut env = Environment::new();
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("U"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("U")],
        ctors: vec![Name::from_dotted("U.mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("U.mk"),
        level_params: Vec::new(),
        ty: Expr::const_("U", vec![]),
        induct: Name::from_dotted("U"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    }));
    let mut tc = TypeChecker::new(&env);
    let u = Expr::FVar(tc.push_local("u", Expr::const_("U", vec![])));
    let term = Expr::Proj(Proj {
        structure: Name::from_dotted("U"),
        index: 0,
        value: Sub::new(u),
    });
    let err = tc.infer_type(&term).unwrap_err();
    assert!(matches!(err, TypeError::BadProjection { .. }), "{err}");
}

#[test]
fn a_let_whose_value_has_the_wrong_type_fails() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    // `let x : Prop := Type; x`. `Type` is not a `Prop`.
    let term = Expr::let_("x", Expr::prop(), Expr::type_(0), Expr::bvar(0));
    let err = tc.infer_type(&term).unwrap_err();
    assert!(matches!(err, TypeError::TypeMismatch { .. }), "{err}");
}

#[test]
fn check_declaration_walks_every_kind() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    // An axiom has no value, so only its type is checked.
    let good_axiom = Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("A"),
        level_params: Vec::new(),
        ty: Expr::prop(),
        is_unsafe: false,
    });
    assert!(tc.check_declaration(&good_axiom).is_ok());

    // An opaque value is still checked, even though δ will not unfold it.
    let bad_opaque = Declaration::Opaque(OpaqueVal {
        name: Name::from_dotted("O"),
        level_params: Vec::new(),
        ty: Expr::prop(),
        value: Expr::type_(0),
        is_unsafe: false,
        all: Vec::new(),
    });
    assert!(tc.check_declaration(&bad_opaque).is_err());

    // A type that is not a type is refused.
    let bad_type = Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("B"),
        level_params: Vec::new(),
        ty: Expr::bvar(0),
        is_unsafe: false,
    });
    assert!(tc.check_declaration(&bad_type).is_err());
}

#[test]
fn positivity_steps_aside_when_the_inductive_is_unknown() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let ctor = ConstructorVal {
        name: Name::from_dotted("X.mk"),
        level_params: Vec::new(),
        ty: Expr::const_("X", vec![]),
        induct: Name::from_dotted("X"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };
    // Without the inductive type there is nothing to check against.
    assert!(tc.check_positivity(&ctor).is_ok());
}

#[test]
fn occurs_reaches_every_expr_variant() {
    let names = [Name::from_dotted("I")];
    let i = Expr::const_("I", vec![]);
    let holders = [
        i.clone(),
        i.clone().app(Expr::prop()),
        Expr::lam("x", i.clone(), Expr::prop()),
        Expr::forall("x", Expr::prop(), i.clone()),
        Expr::let_("x", Expr::prop(), i.clone(), Expr::prop()),
        Expr::let_("x", Expr::prop(), Expr::prop(), i.clone()),
        Expr::Proj(Proj {
            structure: Name::from_dotted("I"),
            index: 0,
            value: Sub::new(Expr::prop()),
        }),
        Expr::Proj(Proj {
            structure: Name::from_dotted("S"),
            index: 0,
            value: Sub::new(i),
        }),
    ];
    for holder in &holders {
        assert!(positivity::occurs(holder, &names), "{}", holder.pretty());
    }
    // The leaves that can never hold a name.
    for leaf in [
        Expr::bvar(0),
        Expr::FVar(FVarId(0)),
        Expr::MVar(MVarId(0)),
        Expr::prop(),
        Expr::nat("1"),
    ] {
        assert!(!positivity::occurs(&leaf, &names));
    }
}

#[test]
fn a_lambda_head_in_a_result_position_is_checked() {
    // The result of a field type is a redex whose head is a lambda that
    // mentions the inductive type. That is not strictly positive.
    let names = [Name::from_dotted("I")];
    let i = Expr::const_("I", vec![]);
    let head = Expr::lam("x", Expr::prop(), i);
    assert!(!positivity::strictly_positive(
        &head.app(Expr::prop()),
        &names
    ));
    // The same shape without the inductive type is fine.
    let clean = Expr::lam("x", Expr::prop(), Expr::prop());
    assert!(positivity::strictly_positive(
        &clean.app(Expr::prop()),
        &names
    ));
}

#[test]
fn a_literal_variant_compares_by_value() {
    assert_eq!(Literal::Nat("1".into()), Literal::Nat("1".into()));
    assert_ne!(Literal::Nat("1".into()), Literal::Str("1".into()));
}
