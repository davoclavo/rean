//! Executable examples for `docs/01-the-type-checker.md`.

use rean_core::Name;
use rean_kernel::{Expr, LocalContext, TypeError, check, infer_type, is_def_eq, whnf};

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

/// Builds a context with `p : Prop` and `hp : p`, and returns both variables.
fn context_with_a_proof() -> (LocalContext, Expr, Expr) {
    let mut ctx = LocalContext::new();
    let p = ctx.push(Name::from_dotted("p"), prop());
    let hp = ctx.push(Name::from_dotted("hp"), Expr::FVar(p));
    (ctx, Expr::FVar(p), Expr::FVar(hp))
}

// --- the headline result ---------------------------------------------------

#[test]
fn the_identity_proof_checks() {
    let mut ctx = LocalContext::new();
    let inferred = infer_type(&mut ctx, &id_proof()).expect("the proof must check");
    assert!(
        inferred.alpha_eq(&id_prop()),
        "inferred {} but wanted {}",
        inferred.pretty(),
        id_prop().pretty()
    );
    assert_eq!(inferred.pretty(), "(α : Prop) → α → α");
    assert!(ctx.is_empty(), "the context must come back empty");
}

#[test]
fn check_accepts_the_proof_against_the_proposition() {
    let mut ctx = LocalContext::new();
    assert!(check(&mut ctx, &id_proof(), &id_prop()).is_ok());
}

#[test]
fn the_proposition_itself_is_a_prop() {
    // `imax 1 0 = 0`. The domain is `Prop : Sort 1` and the body is at level 0,
    // so the whole function type collapses back to `Prop`.
    let mut ctx = LocalContext::new();
    let ty = infer_type(&mut ctx, &id_prop()).expect("a function type is a type");
    assert_eq!(ty.pretty(), "Prop");
}

// --- the sort rule ---------------------------------------------------------

#[test]
fn a_sort_sits_in_the_next_sort_up() {
    let mut ctx = LocalContext::new();
    assert_eq!(infer_type(&mut ctx, &prop()).unwrap().pretty(), "Type");
    assert_eq!(
        infer_type(&mut ctx, &Expr::type_(0)).unwrap().pretty(),
        "Type 1"
    );
    assert_eq!(
        infer_type(&mut ctx, &Expr::type_(4)).unwrap().pretty(),
        "Type 5"
    );
}

// --- the combinators of implicational logic -------------------------------

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
    let mut ctx = LocalContext::new();
    let ty = infer_type(&mut ctx, &k).expect("K must check");
    assert_eq!(ty.pretty(), "(A : Prop) → (B : Prop) → A → B → A");
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
    let mut ctx = LocalContext::new();
    let ty = infer_type(&mut ctx, &comp).expect("composition must check");
    assert_eq!(
        ty.pretty(),
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
    let mut ctx = LocalContext::new();
    let ty = infer_type(&mut ctx, &s).expect("S must check");
    assert_eq!(
        ty.pretty(),
        "(A : Prop) → (B : Prop) → (C : Prop) → (A → B → C) → (A → B) → A → C"
    );
}

// --- the application rule --------------------------------------------------

#[test]
fn applying_the_identity_gives_the_concrete_proposition() {
    let (mut ctx, p, hp) = context_with_a_proof();
    // `idProof p hp` must have the type `p`.
    let term = id_proof().apps([p.clone(), hp]);
    let ty = infer_type(&mut ctx, &term).expect("the application must check");
    assert!(ty.alpha_eq(&p), "got {}", ctx.pretty(&ty));
    assert_eq!(ctx.pretty(&ty), "p");
}

#[test]
fn the_result_type_depends_on_the_argument_value() {
    // One function, two arguments, two different result types. This is the
    // reason that the application rule needs substitution.
    let mut ctx = LocalContext::new();
    let a = ctx.push(Name::from_dotted("a"), prop());
    let b = ctx.push(Name::from_dotted("b"), prop());
    let at_a = infer_type(&mut ctx, &id_proof().app(Expr::FVar(a))).unwrap();
    let at_b = infer_type(&mut ctx, &id_proof().app(Expr::FVar(b))).unwrap();
    assert_eq!(ctx.pretty(&at_a), "a → a");
    assert_eq!(ctx.pretty(&at_b), "b → b");
}

// --- reduction -------------------------------------------------------------

#[test]
fn whnf_does_a_beta_step() {
    let id = Expr::lam("x", prop(), Expr::bvar(0));
    assert!(whnf(&id.app(prop())).alpha_eq(&prop()));
}

#[test]
fn whnf_does_a_zeta_step() {
    let term = Expr::let_("x", Expr::type_(0), prop(), Expr::bvar(0));
    assert!(whnf(&term).alpha_eq(&prop()));
}

#[test]
fn whnf_unfolds_a_let_under_an_application() {
    // `(let f := fun x => x; f) Prop` needs ζ first and then β.
    let id = Expr::lam("x", prop(), Expr::bvar(0));
    let term = Expr::let_("f", Expr::arrow(prop(), prop()), id, Expr::bvar(0)).app(prop());
    assert!(whnf(&term).alpha_eq(&prop()));
}

#[test]
fn whnf_does_not_unfold_a_constant() {
    // The δ rule needs an environment, and there is none. See chapter 2.
    let c = Expr::const_("Nat", vec![]);
    assert!(whnf(&c).alpha_eq(&c));
}

#[test]
fn is_def_eq_sees_through_a_beta_step() {
    let id = Expr::lam("x", prop(), Expr::bvar(0));
    assert!(is_def_eq(&id.app(prop()), &prop()));
}

#[test]
fn is_def_eq_ignores_the_binder_name() {
    let with_x = Expr::lam("x", prop(), Expr::bvar(0));
    let with_y = Expr::lam("y", prop(), Expr::bvar(0));
    assert_ne!(with_x, with_y, "the derived == compares the name");
    assert!(is_def_eq(&with_x, &with_y));
}

#[test]
fn is_def_eq_compares_an_application_spine() {
    let mut ctx = LocalContext::new();
    let f = ctx.push(
        Name::from_dotted("f"),
        Expr::arrow(prop(), Expr::arrow(prop(), prop())),
    );
    let id = Expr::lam("x", Expr::type_(0), Expr::bvar(0));
    // `f Prop Prop` against `f ((fun x => x) Prop) Prop`.
    let plain = Expr::FVar(f).apps([prop(), prop()]);
    let with_redex = Expr::FVar(f).apps([id.app(prop()), prop()]);
    assert!(is_def_eq(&plain, &with_redex));
}

#[test]
fn a_let_in_the_expected_type_still_matches() {
    // The ζ rule makes a local definition transparent.
    let (mut ctx, p, hp) = context_with_a_proof();
    let alias = Expr::let_("A", prop(), p, Expr::bvar(0));
    assert!(check(&mut ctx, &hp, &alias).is_ok());
}

// --- the errors ------------------------------------------------------------

#[test]
fn a_loose_bound_variable_is_an_error() {
    let mut ctx = LocalContext::new();
    assert_eq!(
        infer_type(&mut ctx, &Expr::bvar(2)),
        Err(TypeError::LooseBVar(2))
    );
}

#[test]
fn a_constant_has_no_declaration_yet() {
    let mut ctx = LocalContext::new();
    let err = infer_type(&mut ctx, &Expr::const_("Nat", vec![])).unwrap_err();
    assert_eq!(err, TypeError::UnknownConstant(Name::from_dotted("Nat")));
    assert!(err.to_string().contains("chapter 2"));
}

#[test]
fn a_literal_needs_an_environment() {
    let mut ctx = LocalContext::new();
    let err = infer_type(&mut ctx, &Expr::nat("3")).unwrap_err();
    assert_eq!(err, TypeError::NeedsEnvironment { what: "a literal" });
}

#[test]
fn applying_a_term_that_is_not_a_function_fails() {
    let mut ctx = LocalContext::new();
    let err = infer_type(&mut ctx, &prop().app(prop())).unwrap_err();
    assert!(matches!(err, TypeError::NotAFunction { .. }), "{err}");
    assert!(err.to_string().contains("is not a function"));
}

#[test]
fn a_binder_whose_type_is_a_proof_fails() {
    // `hp : p` and `p : Prop`, so `hp` is a proof and not a type.
    let (mut ctx, _p, hp) = context_with_a_proof();
    let bad = Expr::lam("x", hp, Expr::bvar(0));
    let err = infer_type(&mut ctx, &bad).unwrap_err();
    assert!(matches!(err, TypeError::NotAType { .. }), "{err}");
}

#[test]
fn the_wrong_argument_type_fails() {
    let (mut ctx, _p, hp) = context_with_a_proof();
    // `idProof` wants a `Prop` first, and `hp` is a proof, not a proposition.
    let err = infer_type(&mut ctx, &id_proof().app(hp)).unwrap_err();
    assert!(matches!(err, TypeError::TypeMismatch { .. }), "{err}");
    assert!(err.to_string().contains("type mismatch"));
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
    let mut ctx = LocalContext::new();
    let err = check(&mut ctx, &term, &wanted).unwrap_err();
    assert!(matches!(err, TypeError::TypeMismatch { .. }), "{err}");
}

#[test]
fn the_context_is_clean_after_an_error() {
    let mut ctx = LocalContext::new();
    let bad = Expr::lam("x", prop(), Expr::bvar(3));
    assert!(infer_type(&mut ctx, &bad).is_err());
    assert!(ctx.is_empty(), "with_binder must not leak an entry");
}

// --- the gaps that chapter 2 closes ---------------------------------------

#[test]
fn proof_irrelevance_is_missing() {
    // `h1 : p` and `h2 : p` with `p : Prop`. A full kernel makes these two
    // definitionally equal. This one does not yet.
    let mut ctx = LocalContext::new();
    let p = ctx.push(Name::from_dotted("p"), prop());
    let h1 = ctx.push(Name::from_dotted("h1"), Expr::FVar(p));
    let h2 = ctx.push(Name::from_dotted("h2"), Expr::FVar(p));
    assert!(
        !is_def_eq(&Expr::FVar(h1), &Expr::FVar(h2)),
        "this assertion must flip when chapter 2 adds proof irrelevance"
    );
}

#[test]
fn eta_is_missing() {
    // `fun x => f x` and `f` are the same function. The η rule says so.
    let mut ctx = LocalContext::new();
    let f = ctx.push(Name::from_dotted("f"), Expr::arrow(prop(), prop()));
    let wrapped = Expr::lam("x", prop(), Expr::FVar(f).app(Expr::bvar(0)));
    assert!(
        !is_def_eq(&wrapped, &Expr::FVar(f)),
        "this assertion must flip when chapter 2 adds the eta rule"
    );
}
