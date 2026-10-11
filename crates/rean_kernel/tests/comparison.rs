//! The order in which the kernel asks its questions.
//!
//! `is_def_eq` has more than one way to answer, and the order matters more than
//! any one of them. Chapter 11 explains why.

use rean_core::Name;
use rean_kernel::{
    AxiomVal, Declaration, DefinitionSafety, DefinitionVal, Environment, Expr, ReducibilityHints,
    TypeChecker, TypeError,
};

/// A well-formed term of about `3 * depth` nodes.
///
/// `fun x => fun x => ... => Nat`, so unfolding it is expensive and reading its
/// head is not.
fn big(depth: usize) -> Expr {
    let nat = Expr::const_("Nat", vec![]);
    let mut term = nat.clone();
    for _ in 0..depth {
        term = Expr::lam("x", nat.clone(), term);
    }
    term
}

/// `Nat` as an axiom, `Big` as an expensive definition, `E` as a cheap one.
fn env() -> Environment {
    let mut env = Environment::new();
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("Nat"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    let nat = Expr::const_("Nat", vec![]);
    let mut ty = Expr::type_(0);
    for _ in 0..600 {
        ty = Expr::arrow(nat.clone(), ty);
    }
    env.add(Declaration::Definition(DefinitionVal {
        name: Name::from_dotted("Big"),
        all: vec![Name::from_dotted("Big")],
        level_params: Vec::new(),
        ty,
        value: big(600),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    }));
    env.add(Declaration::Definition(DefinitionVal {
        name: Name::from_dotted("E"),
        all: vec![Name::from_dotted("E")],
        level_params: Vec::new(),
        ty: Expr::type_(0),
        value: nat,
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    }));
    env
}

/// The budget is the measure. It is a count and not a clock, so it is the same
/// on every machine and in every run.
const SMALL: u64 = 2_000;

#[test]
fn the_same_head_is_compared_before_it_is_unfolded() {
    // `Big E` and `Big Nat` have the same head, and `E` unfolds to `Nat`, so
    // the two are equal by congruence. Reading that costs the one argument.
    //
    // Unfolding `Big` first would cost its whole body, twice. The budget here
    // is far too small for that, so this test fails if the kernel unfolds
    // before it compares.
    let env = env();
    let mut tc = TypeChecker::new(&env);
    tc.set_fuel(SMALL);
    let left = Expr::const_("Big", vec![]).app(Expr::const_("E", vec![]));
    let right = Expr::const_("Big", vec![]).app(Expr::const_("Nat", vec![]));
    assert_eq!(tc.is_def_eq(&left, &right), Ok(true));
}

#[test]
fn a_different_head_still_costs_the_unfolding() {
    // The control for the test above. With no shared head there is nothing to
    // compare, so the kernel must unfold `Big`, and the same small budget is
    // not enough. Without this test the one above could pass because the terms
    // are cheap rather than because the order is right.
    let env = env();
    let mut tc = TypeChecker::new(&env);
    tc.set_fuel(SMALL);
    let left = Expr::const_("Big", vec![]).app(Expr::const_("E", vec![]));
    let right = Expr::const_("Nat", vec![]);
    assert_eq!(
        tc.is_def_eq(&left, &right),
        Err(TypeError::OutOfFuel(SMALL))
    );
}

#[test]
fn a_shared_head_with_unequal_arguments_falls_through() {
    // A `false` from the quick comparison proves nothing, so the kernel must
    // carry on. Here the arguments really differ, and `Big` ignores its
    // argument, so the full comparison finds the two terms equal anyway.
    let env = env();
    let mut tc = TypeChecker::new(&env);
    let left = Expr::const_("Big", vec![]).app(Expr::const_("Nat", vec![]));
    let right = Expr::const_("Big", vec![]).app(Expr::type_(3));
    assert_eq!(tc.is_def_eq(&left, &right), Ok(true));
}

// --- proof irrelevance, before any reduction ------------------------------

/// Adds `T : <sort>`, `t : T`, and `Slow : T` whose reduction is expensive.
///
/// `Slow` unfolds to `Wrap Big`, and `Big` is about 1,200 nodes, so each step
/// of that reduction is charged for a term of that size. Reading the **type**
/// of `Slow` costs nothing, because a declaration states its own type.
fn with_a_slow_proof(env: &mut Environment, sort: Expr, prefix: &str) {
    let name = |part: &str| Name::from_dotted(&format!("{prefix}{part}"));
    let ty = Expr::const_(name("T").to_string().as_str(), vec![]);
    env.add(Declaration::Axiom(AxiomVal {
        name: name("T"),
        level_params: Vec::new(),
        ty: sort,
        is_unsafe: false,
    }));
    env.add(Declaration::Axiom(AxiomVal {
        name: name("t"),
        level_params: Vec::new(),
        ty: ty.clone(),
        is_unsafe: false,
    }));
    // `Wrap := fun _ => t`, so it throws its argument away.
    env.add(Declaration::Definition(DefinitionVal {
        name: name("Wrap"),
        all: vec![name("Wrap")],
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::const_("Nat", vec![]), ty.clone()),
        value: Expr::lam(
            "n",
            Expr::const_("Nat", vec![]),
            Expr::const_(name("t").to_string().as_str(), vec![]),
        ),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    }));
    env.add(Declaration::Definition(DefinitionVal {
        name: name("Slow"),
        all: vec![name("Slow")],
        level_params: Vec::new(),
        ty,
        value: Expr::const_(name("Wrap").to_string().as_str(), vec![]).app(big(600)),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    }));
}

#[test]
fn two_proofs_of_one_proposition_need_no_reduction() {
    // `PropSlow` and `Propt` both prove `PropT`, which is a `Prop`. So they are
    // equal, and the kernel never has to look at either one.
    //
    // Reducing `PropSlow` costs more than this budget, so the test fails if the
    // kernel reduces before it reads the two types.
    let mut env = env();
    with_a_slow_proof(&mut env, Expr::prop(), "Prop");
    let mut tc = TypeChecker::new(&env);
    tc.set_fuel(SMALL);
    let slow = Expr::const_("PropSlow", vec![]);
    let plain = Expr::const_("Propt", vec![]);
    assert_eq!(tc.is_def_eq(&slow, &plain), Ok(true));
}

#[test]
fn two_terms_of_one_type_do_need_reduction() {
    // The control. `TypeT` is a `Type` and not a `Prop`, so two of its terms
    // are not equal for free, and the kernel must reduce after all. The same
    // budget is then not enough.
    //
    // Without this test the one above could pass because `Prop` is special in
    // name only.
    let mut env = env();
    with_a_slow_proof(&mut env, Expr::type_(0), "Type");
    let mut tc = TypeChecker::new(&env);
    tc.set_fuel(SMALL);
    let slow = Expr::const_("TypeSlow", vec![]);
    let plain = Expr::const_("Typet", vec![]);
    assert_eq!(
        tc.is_def_eq(&slow, &plain),
        Err(TypeError::OutOfFuel(SMALL))
    );
}
