//! Executable examples for `docs/01-the-type-checker.md` and chapter 2.

use rean_core::Name;
use rean_kernel::positivity::PositivityError;
use rean_kernel::{
    ConstructorVal, Declaration, DefinitionSafety, DefinitionVal, Environment, Expr, InductiveVal,
    Level, QuotKind, QuotVal, RecursorRule, RecursorVal, TypeChecker, TypeError,
};

fn prop() -> Expr {
    Expr::prop()
}

/// `fun (α : Prop) (h : α) => h`, the proof of the identity.
fn id_proof() -> Expr {
    Expr::lam("α", prop(), Expr::lam("h", Expr::bvar(0), Expr::bvar(0)))
}

/// `(α : Prop) → α → α`, the proposition that the proof above proves.
fn id_prop() -> Expr {
    Expr::forall("α", prop(), Expr::arrow(Expr::bvar(0), Expr::bvar(0)))
}

/// Builds a checker with `p : Prop` and `hp : p`, and returns both variables.
fn with_a_proof(env: &Environment) -> (TypeChecker<'_>, Expr, Expr) {
    let mut tc = TypeChecker::new(env);
    let p = tc.push_local("p", prop());
    let hp = tc.push_local("hp", Expr::FVar(p));
    (tc, Expr::FVar(p), Expr::FVar(hp))
}

/// Builds `def name : ty := value`, with no universe parameters.
fn a_def(name: &str, ty: Expr, value: Expr) -> Declaration {
    Declaration::Definition(DefinitionVal {
        name: Name::from_dotted(name),
        level_params: Vec::new(),
        ty,
        value,
        hints: rean_kernel::ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    })
}

// --- chapter 1: the headline result ---------------------------------------

#[test]
fn the_identity_proof_checks() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let inferred = tc.infer_type(&id_proof()).expect("the proof must check");
    assert!(inferred.alpha_eq(&id_prop()), "got {}", inferred.pretty());
    assert_eq!(inferred.pretty(), "(α : Prop) → α → α");
    assert!(tc.lctx().is_empty(), "the context must come back empty");
}

#[test]
fn check_accepts_the_proof_against_the_proposition() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert!(tc.check(&id_proof(), &id_prop()).is_ok());
}

#[test]
fn the_proposition_itself_is_a_prop() {
    // `imax 1 0 = 0`, so the function type collapses back to `Prop`.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(tc.infer_type(&id_prop()).unwrap().pretty(), "Prop");
}

#[test]
fn a_sort_sits_in_the_next_sort_up() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(tc.infer_type(&prop()).unwrap().pretty(), "Type");
    assert_eq!(tc.infer_type(&Expr::type_(0)).unwrap().pretty(), "Type 1");
    assert_eq!(tc.infer_type(&Expr::type_(4)).unwrap().pretty(), "Type 5");
}

// --- chapter 1: the combinators -------------------------------------------

#[test]
fn the_k_combinator_checks() {
    // fun (A B : Prop) (a : A) (b : B) => a
    let k = Expr::lam(
        "A",
        prop(),
        Expr::lam(
            "B",
            prop(),
            Expr::lam(
                "a",
                Expr::bvar(1),
                Expr::lam("b", Expr::bvar(1), Expr::bvar(1)),
            ),
        ),
    );
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(
        tc.infer_type(&k).unwrap().pretty(),
        "(A : Prop) → (B : Prop) → A → B → A"
    );
}

#[test]
fn composition_checks() {
    // fun (A B C : Prop) (f : B → C) (g : A → B) (a : A) => f (g a)
    let comp = Expr::lam(
        "A",
        prop(),
        Expr::lam(
            "B",
            prop(),
            Expr::lam(
                "C",
                prop(),
                Expr::lam(
                    "f",
                    Expr::arrow(Expr::bvar(1), Expr::bvar(0)),
                    Expr::lam(
                        "g",
                        Expr::arrow(Expr::bvar(3), Expr::bvar(2)),
                        Expr::lam(
                            "a",
                            Expr::bvar(4),
                            Expr::bvar(2).app(Expr::bvar(1).app(Expr::bvar(0))),
                        ),
                    ),
                ),
            ),
        ),
    );
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(
        tc.infer_type(&comp).unwrap().pretty(),
        "(A : Prop) → (B : Prop) → (C : Prop) → (B → C) → (A → B) → A → C"
    );
}

#[test]
fn the_s_combinator_checks() {
    // fun (A B C : Prop) (f : A → B → C) (g : A → B) (a : A) => f a (g a)
    let s = Expr::lam(
        "A",
        prop(),
        Expr::lam(
            "B",
            prop(),
            Expr::lam(
                "C",
                prop(),
                Expr::lam(
                    "f",
                    Expr::arrow(Expr::bvar(2), Expr::arrow(Expr::bvar(1), Expr::bvar(0))),
                    Expr::lam(
                        "g",
                        Expr::arrow(Expr::bvar(3), Expr::bvar(2)),
                        Expr::lam(
                            "a",
                            Expr::bvar(4),
                            Expr::bvar(2)
                                .app(Expr::bvar(0))
                                .app(Expr::bvar(1).app(Expr::bvar(0))),
                        ),
                    ),
                ),
            ),
        ),
    );
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(
        tc.infer_type(&s).unwrap().pretty(),
        "(A : Prop) → (B : Prop) → (C : Prop) → (A → B → C) → (A → B) → A → C"
    );
}

// --- chapter 1: the application rule --------------------------------------

#[test]
fn applying_the_identity_gives_the_concrete_proposition() {
    let env = Environment::new();
    let (mut tc, p, hp) = with_a_proof(&env);
    let ty = tc.infer_type(&id_proof().apps([p.clone(), hp])).unwrap();
    assert!(ty.alpha_eq(&p));
    assert_eq!(tc.lctx().pretty(&ty), "p");
}

#[test]
fn the_result_type_depends_on_the_argument_value() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let a = tc.push_local("a", prop());
    let b = tc.push_local("b", prop());
    let at_a = tc.infer_type(&id_proof().app(Expr::FVar(a))).unwrap();
    let at_b = tc.infer_type(&id_proof().app(Expr::FVar(b))).unwrap();
    assert_eq!(tc.lctx().pretty(&at_a), "a → a");
    assert_eq!(tc.lctx().pretty(&at_b), "b → b");
}

// --- chapter 1: reduction --------------------------------------------------

#[test]
fn whnf_does_a_beta_step() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let id = Expr::lam("x", prop(), Expr::bvar(0));
    assert!(tc.whnf(&id.app(prop())).unwrap().alpha_eq(&prop()));
}

#[test]
fn whnf_does_a_zeta_step() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let term = Expr::let_("x", Expr::type_(0), prop(), Expr::bvar(0));
    assert!(tc.whnf(&term).unwrap().alpha_eq(&prop()));
}

#[test]
fn whnf_unfolds_a_let_under_an_application() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let id = Expr::lam("x", prop(), Expr::bvar(0));
    let term = Expr::let_("f", Expr::arrow(prop(), prop()), id, Expr::bvar(0)).app(prop());
    assert!(tc.whnf(&term).unwrap().alpha_eq(&prop()));
}

#[test]
fn is_def_eq_ignores_the_binder_name() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let with_x = Expr::lam("x", prop(), Expr::bvar(0));
    let with_y = Expr::lam("y", prop(), Expr::bvar(0));
    assert_ne!(with_x, with_y, "the derived == compares the name");
    assert!(tc.is_def_eq(&with_x, &with_y).unwrap());
}

#[test]
fn is_def_eq_compares_an_application_spine() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let f = tc.push_local("f", Expr::arrow(prop(), Expr::arrow(prop(), prop())));
    let id = Expr::lam("x", Expr::type_(0), Expr::bvar(0));
    let plain = Expr::FVar(f).apps([prop(), prop()]);
    let with_redex = Expr::FVar(f).apps([id.app(prop()), prop()]);
    assert!(tc.is_def_eq(&plain, &with_redex).unwrap());
}

#[test]
fn a_let_in_the_expected_type_still_matches() {
    let env = Environment::new();
    let (mut tc, p, hp) = with_a_proof(&env);
    let alias = Expr::let_("A", prop(), p, Expr::bvar(0));
    assert!(tc.check(&hp, &alias).is_ok());
}

// --- chapter 2: the delta rule --------------------------------------------

#[test]
fn an_empty_environment_does_not_unfold_a_constant() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let c = Expr::const_("Foo", vec![]);
    assert!(tc.whnf(&c).unwrap().alpha_eq(&c));
}

#[test]
fn a_definition_unfolds_to_its_value() {
    let mut env = Environment::new();
    env.add(a_def("MyProp", Expr::type_(0), prop()));
    let mut tc = TypeChecker::new(&env);
    let c = Expr::const_("MyProp", vec![]);
    // The type comes from the declaration.
    assert_eq!(tc.infer_type(&c).unwrap().pretty(), "Type");
    // The δ rule unfolds the value.
    assert_eq!(tc.whnf(&c).unwrap().pretty(), "Prop");
    assert!(tc.is_def_eq(&c, &prop()).unwrap());
}

#[test]
fn delta_substitutes_the_universe_arguments() {
    // `def Alias.{u} : Sort (u+1) := Sort u`
    let u = Name::from_dotted("u");
    let mut env = Environment::new();
    env.add(Declaration::Definition(DefinitionVal {
        name: Name::from_dotted("Alias"),
        level_params: vec![u.clone()],
        ty: Expr::sort(Level::param("u").succ().succ()),
        value: Expr::sort(Level::param("u").succ()),
        hints: rean_kernel::ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    }));
    let mut tc = TypeChecker::new(&env);
    // At `u := 0` the value must become `Sort 1`, which prints as `Type`.
    let at_zero = Expr::const_("Alias", vec![Level::Zero]);
    assert_eq!(tc.whnf(&at_zero).unwrap().pretty(), "Type");
    assert_eq!(tc.infer_type(&at_zero).unwrap().pretty(), "Type 1");
}

#[test]
fn the_wrong_number_of_universe_arguments_fails() {
    let mut env = Environment::new();
    env.add(a_def("MyProp", Expr::type_(0), prop()));
    let mut tc = TypeChecker::new(&env);
    let err = tc
        .infer_type(&Expr::const_("MyProp", vec![Level::Zero]))
        .unwrap_err();
    assert!(matches!(err, TypeError::LevelArity { .. }), "{err}");
}

// --- chapter 2: the iota rule ---------------------------------------------

/// Builds `inductive Bool2 | f | t`, with its recursor.
///
/// `Bool2.rec : {motive : Bool2 → Sort u} → motive f → motive t → (t : Bool2) → motive t`
fn bool2_env() -> Environment {
    let mut env = Environment::new();
    let bool2 = || Expr::const_("Bool2", vec![]);
    let u = Name::from_dotted("u");

    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Bool2"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("Bool2")],
        ctors: vec![Name::from_dotted("Bool2.f"), Name::from_dotted("Bool2.t")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    for (index, short) in ["f", "t"].iter().enumerate() {
        env.add(Declaration::Constructor(ConstructorVal {
            name: Name::from_dotted(&format!("Bool2.{short}")),
            level_params: Vec::new(),
            ty: bool2(),
            induct: Name::from_dotted("Bool2"),
            cidx: index as u32,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }));
    }
    // motive : Bool2 → Sort u
    let motive_ty = Expr::arrow(bool2(), Expr::sort(Level::param("u")));
    env.add(Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("Bool2.rec"),
        level_params: vec![u],
        ty: Expr::forall(
            "motive",
            motive_ty,
            // motive f → motive t → (x : Bool2) → motive x
            Expr::arrow(
                Expr::bvar(0).app(Expr::const_("Bool2.f", vec![])),
                Expr::arrow(
                    Expr::bvar(1).app(Expr::const_("Bool2.t", vec![])),
                    Expr::forall("x", bool2(), Expr::bvar(3).app(Expr::bvar(0))),
                ),
            ),
        ),
        all: vec![Name::from_dotted("Bool2")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        rules: vec![
            RecursorRule {
                ctor: Name::from_dotted("Bool2.f"),
                num_fields: 0,
                // fun motive onF onT => onF
                rhs: Expr::lam(
                    "motive",
                    Expr::type_(0),
                    Expr::lam(
                        "onF",
                        Expr::type_(0),
                        Expr::lam("onT", Expr::type_(0), Expr::bvar(1)),
                    ),
                ),
            },
            RecursorRule {
                ctor: Name::from_dotted("Bool2.t"),
                num_fields: 0,
                // fun motive onF onT => onT
                rhs: Expr::lam(
                    "motive",
                    Expr::type_(0),
                    Expr::lam(
                        "onF",
                        Expr::type_(0),
                        Expr::lam("onT", Expr::type_(0), Expr::bvar(0)),
                    ),
                ),
            },
        ],
        k: false,
        is_unsafe: false,
    }));
    env
}

#[test]
fn iota_picks_the_rule_of_the_constructor() {
    let env = bool2_env();
    let mut tc = TypeChecker::new(&env);
    let motive = Expr::lam("_x", Expr::const_("Bool2", vec![]), Expr::type_(0));
    let rec = |major: &str| {
        Expr::const_("Bool2.rec", vec![Level::of_nat(1)]).apps([
            motive.clone(),
            prop(),
            Expr::type_(0),
            Expr::const_(major, vec![]),
        ])
    };
    // `Bool2.rec motive Prop Type Bool2.f` must reduce to `Prop`.
    assert_eq!(tc.whnf(&rec("Bool2.f")).unwrap().pretty(), "Prop");
    // ... and with `Bool2.t` to `Type`.
    assert_eq!(tc.whnf(&rec("Bool2.t")).unwrap().pretty(), "Type");
}

#[test]
fn iota_waits_for_a_constructor() {
    // With a free variable as the major premise, no rule applies.
    let env = bool2_env();
    let mut tc = TypeChecker::new(&env);
    let x = tc.push_local("x", Expr::const_("Bool2", vec![]));
    let motive = Expr::lam("_x", Expr::const_("Bool2", vec![]), Expr::type_(0));
    let stuck = Expr::const_("Bool2.rec", vec![Level::of_nat(1)]).apps([
        motive,
        prop(),
        Expr::type_(0),
        Expr::FVar(x),
    ]);
    let reduced = tc.whnf(&stuck).unwrap();
    assert!(
        matches!(reduced, Expr::App { .. }),
        "it must stay stuck: {}",
        tc.lctx().pretty(&reduced)
    );
}

#[test]
fn iota_needs_enough_arguments() {
    let env = bool2_env();
    let mut tc = TypeChecker::new(&env);
    let partial = Expr::const_("Bool2.rec", vec![Level::of_nat(1)]).app(prop());
    assert!(tc.whnf(&partial).unwrap().alpha_eq(&partial));
}

// --- chapter 2: eta and proof irrelevance now work -----------------------

#[test]
fn eta_makes_a_wrapper_equal_to_the_function() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let f = tc.push_local("f", Expr::arrow(prop(), prop()));
    let wrapped = Expr::lam("x", prop(), Expr::FVar(f).app(Expr::bvar(0)));
    assert!(tc.is_def_eq(&wrapped, &Expr::FVar(f)).unwrap());
    assert!(tc.is_def_eq(&Expr::FVar(f), &wrapped).unwrap());
}

#[test]
fn proof_irrelevance_makes_two_proofs_equal() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let p = tc.push_local("p", prop());
    let h1 = tc.push_local("h1", Expr::FVar(p));
    let h2 = tc.push_local("h2", Expr::FVar(p));
    assert!(tc.is_def_eq(&Expr::FVar(h1), &Expr::FVar(h2)).unwrap());
}

#[test]
fn proof_irrelevance_does_not_apply_to_data() {
    // Two elements of a `Type` are not equal just because the type matches.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let t = tc.push_local("T", Expr::type_(0));
    let a = tc.push_local("a", Expr::FVar(t));
    let b = tc.push_local("b", Expr::FVar(t));
    assert!(!tc.is_def_eq(&Expr::FVar(a), &Expr::FVar(b)).unwrap());
}

#[test]
fn level_normalization_sees_through_max() {
    assert!(
        Level::param("u")
            .max(&Level::Zero)
            .is_equiv(&Level::param("u"))
    );
    assert!(Level::param("u").imax(&Level::Zero).is_equiv(&Level::Zero));
    assert!(!Level::param("u").is_equiv(&Level::param("v")));
}

// --- the errors -----------------------------------------------------------

#[test]
fn a_loose_bound_variable_is_an_error() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(tc.infer_type(&Expr::bvar(2)), Err(TypeError::LooseBVar(2)));
}

#[test]
fn an_unknown_constant_is_an_error() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let err = tc.infer_type(&Expr::const_("Nat", vec![])).unwrap_err();
    assert_eq!(err, TypeError::UnknownConstant(Name::from_dotted("Nat")));
}

#[test]
fn a_nat_literal_has_type_nat() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    // The type is `Nat`, and `Nat` itself is unknown in an empty environment.
    assert_eq!(
        tc.infer_type(&Expr::nat("3")).unwrap(),
        Expr::const_("Nat", vec![])
    );
}

#[test]
fn applying_a_term_that_is_not_a_function_fails() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let err = tc.infer_type(&prop().app(prop())).unwrap_err();
    assert!(matches!(err, TypeError::NotAFunction { .. }), "{err}");
}

#[test]
fn a_binder_whose_type_is_a_proof_fails() {
    let env = Environment::new();
    let (mut tc, _p, hp) = with_a_proof(&env);
    let err = tc
        .infer_type(&Expr::lam("x", hp, Expr::bvar(0)))
        .unwrap_err();
    assert!(matches!(err, TypeError::NotAType { .. }), "{err}");
}

#[test]
fn the_wrong_argument_type_fails() {
    let env = Environment::new();
    let (mut tc, _p, hp) = with_a_proof(&env);
    let err = tc.infer_type(&id_proof().app(hp)).unwrap_err();
    assert!(matches!(err, TypeError::TypeMismatch { .. }), "{err}");
}

#[test]
fn a_wrong_proof_does_not_check() {
    // The term proves `α → α`, and the proposition asks for `α → β`.
    let term = Expr::lam(
        "α",
        prop(),
        Expr::lam("β", prop(), Expr::lam("h", Expr::bvar(1), Expr::bvar(0))),
    );
    let wanted = Expr::forall(
        "α",
        prop(),
        Expr::forall("β", prop(), Expr::arrow(Expr::bvar(1), Expr::bvar(0))),
    );
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let err = tc.check(&term, &wanted).unwrap_err();
    assert!(matches!(err, TypeError::TypeMismatch { .. }), "{err}");
}

#[test]
fn the_context_is_clean_after_an_error() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert!(
        tc.infer_type(&Expr::lam("x", prop(), Expr::bvar(3)))
            .is_err()
    );
    assert!(tc.lctx().is_empty(), "a binder must not leak an entry");
}

// --- check_declaration -----------------------------------------------------

#[test]
fn check_declaration_accepts_a_good_definition() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert!(
        tc.check_declaration(&a_def("Id", id_prop(), id_proof()))
            .is_ok()
    );
}

#[test]
fn check_declaration_rejects_a_bad_definition() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let bad = a_def("Bad", id_prop(), prop());
    assert!(tc.check_declaration(&bad).is_err());
}

// --- chapter 4: the quotient rules ----------------------------------------

/// Builds the four `Quot` constants.
///
/// The types are placeholders. [`TypeChecker::whnf`] matches on the declaration
/// kind and the argument count, not on the types, so this environment is enough
/// to exercise the two quotient reduction rules.
fn quot_env() -> Environment {
    let mut env = Environment::new();
    let u = Name::from_dotted("u");
    for (name, kind) in [
        ("Quot", QuotKind::Type),
        ("Quot.mk", QuotKind::Ctor),
        ("Quot.lift", QuotKind::Lift),
        ("Quot.ind", QuotKind::Ind),
    ] {
        env.add(Declaration::Quot(QuotVal {
            name: Name::from_dotted(name),
            level_params: vec![u.clone()],
            ty: Expr::type_(0),
            kind,
        }));
    }
    env
}

#[test]
fn quot_lift_applies_the_function_to_the_value() {
    // `Quot.lift α r β f h (Quot.mk α r a)  ~>  f a`
    let env = quot_env();
    let mut tc = TypeChecker::new(&env);
    let one = vec![Level::of_nat(1)];
    let hole = |n: &str| Expr::const_(n, vec![]);
    let mk = Expr::const_("Quot.mk", one.clone()).apps([hole("A"), hole("r"), hole("a")]);
    let f = Expr::lam("x", Expr::type_(0), Expr::bvar(0));
    let term =
        Expr::const_("Quot.lift", one).apps([hole("A"), hole("r"), hole("B"), f, hole("h"), mk]);
    // `f` is the identity, so the result is the value `a`.
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "a");
}

#[test]
fn quot_ind_applies_the_proof_to_the_value() {
    // `Quot.ind α r β h (Quot.mk α r a)  ~>  h a`
    let env = quot_env();
    let mut tc = TypeChecker::new(&env);
    let one = vec![Level::of_nat(1)];
    let hole = |n: &str| Expr::const_(n, vec![]);
    let mk = Expr::const_("Quot.mk", one.clone()).apps([hole("A"), hole("r"), hole("a")]);
    let term = Expr::const_("Quot.ind", one).apps([hole("A"), hole("r"), hole("B"), hole("h"), mk]);
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "h a");
}

#[test]
fn a_quotient_rule_waits_for_quot_mk() {
    // With a variable in place of `Quot.mk`, nothing reduces.
    let env = quot_env();
    let mut tc = TypeChecker::new(&env);
    let one = vec![Level::of_nat(1)];
    let hole = |n: &str| Expr::const_(n, vec![]);
    let term =
        Expr::const_("Quot.ind", one).apps([hole("A"), hole("r"), hole("B"), hole("h"), hole("q")]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}

// --- chapter 4: a bad inductive declaration is refused --------------------

#[test]
fn an_inductive_that_could_prove_false_is_refused() {
    // `inductive Bad | mk : (Bad -> False) -> Bad`
    //
    // Accept this and a user proves `False` with no axiom and no other
    // mistake. The kernel must push back at the constructor.
    let mut env = Environment::new();
    let bad = || Expr::const_("Bad", vec![]);
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Bad"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("Bad")],
        ctors: vec![Name::from_dotted("Bad.mk")],
        num_nested: 0,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    }));
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("False"),
        level_params: Vec::new(),
        ty: Expr::prop(),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("False")],
        ctors: Vec::new(),
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));

    let ctor = ConstructorVal {
        name: Name::from_dotted("Bad.mk"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::arrow(bad(), Expr::const_("False", vec![])), bad()),
        induct: Name::from_dotted("Bad"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let decl = Declaration::Constructor(ctor);

    let mut tc = TypeChecker::new(&env);
    let err = tc.check_declaration(&decl).unwrap_err();
    assert!(
        matches!(
            err,
            TypeError::BadConstructor {
                reason: PositivityError::NotStrictlyPositive { field: 0 },
                ..
            }
        ),
        "{err}"
    );
    assert!(err.to_string().contains("strictly positive"));
    assert!(err.to_string().contains("prove `False`"));
}

#[test]
fn a_reflexive_inductive_is_still_accepted() {
    // `inductive Good | mk : (Nat -> Good) -> Good` is sound, and the check
    // must not reject it. A check that refuses correct code is worse than none.
    let mut env = Environment::new();
    env.add(Declaration::Axiom(rean_kernel::AxiomVal {
        name: Name::from_dotted("Nat"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    let good = || Expr::const_("Good", vec![]);
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Good"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("Good")],
        ctors: vec![Name::from_dotted("Good.mk")],
        num_nested: 0,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: true,
    }));
    let ctor = ConstructorVal {
        name: Name::from_dotted("Good.mk"),
        level_params: Vec::new(),
        // `(Nat -> Good) -> Good`. The field sits at the same level as `Good`,
        // so it fits.
        ty: Expr::arrow(Expr::arrow(Expr::const_("Nat", vec![]), good()), good()),
        induct: Name::from_dotted("Good"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let mut tc = TypeChecker::new(&env);
    assert!(tc.check_positivity(&ctor).is_ok());
}

#[test]
fn a_nested_inductive_gets_the_weaker_rule() {
    // `List Tree -> Tree` puts `Tree` inside another type constructor, so the
    // strict rule would refuse it. A nested declaration gets the weaker rule
    // instead: nowhere in a domain, anywhere in the result.
    let mut env = Environment::new();
    env.add(Declaration::Axiom(rean_kernel::AxiomVal {
        name: Name::from_dotted("List"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::type_(0), Expr::type_(0)),
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
    let tree = || Expr::const_("Tree", vec![]);
    let ctor = ConstructorVal {
        name: Name::from_dotted("Tree.node"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::const_("List", vec![]).app(tree()), tree()),
        induct: Name::from_dotted("Tree"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let mut tc = TypeChecker::new(&env);
    assert!(tc.check_positivity(&ctor).is_ok());
}
