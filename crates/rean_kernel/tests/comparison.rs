//! The order in which the kernel asks its questions.
//!
//! `is_def_eq` has more than one way to answer, and the order matters more than
//! any one of them. Chapter 11 explains why.

use rean_core::Name;
use rean_kernel::{
    AxiomVal, ConstructorVal, Declaration, DefinitionSafety, DefinitionVal, Environment, Expr,
    InductiveVal, ReducibilityHints, TypeChecker, TypeError,
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

// --- reading a number in either of its two forms -------------------------

/// `Nat`, its two constructors, `Bool`, and `Big : Nat` as a definition.
///
/// `Nat.ble` is deliberately **not** declared, so the only way to answer a
/// comparison here is the kernel's own rule for two numbers. If the rule
/// declines, the term is stuck, and the test sees it.
///
/// `Big` is a definition rather than a literal on purpose, because
/// `Nat.Linear.fixedVar` of the Lean prelude is one too, and δ has to run
/// before the number can be read.
fn env_with_nat_ble(size: u128) -> Environment {
    let mut env = Environment::new();
    let nat = Expr::const_("Nat", vec![]);
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Nat"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("Nat")],
        ctors: vec![Name::from_dotted("Nat.zero"), Name::from_dotted("Nat.succ")],
        num_nested: 0,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    }));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("Nat.zero"),
        level_params: Vec::new(),
        ty: nat.clone(),
        induct: Name::from_dotted("Nat"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    }));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("Nat.succ"),
        level_params: Vec::new(),
        ty: Expr::arrow(nat.clone(), nat.clone()),
        induct: Name::from_dotted("Nat"),
        cidx: 1,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    }));
    for part in ["Bool.true", "Bool.false"] {
        env.add(Declaration::Axiom(AxiomVal {
            name: Name::from_dotted(part),
            level_params: Vec::new(),
            ty: Expr::const_("Bool", vec![]),
            is_unsafe: false,
        }));
    }
    // `Big` is a definition, exactly as `Nat.Linear.fixedVar` is.
    env.add(Declaration::Definition(DefinitionVal {
        name: Name::from_dotted("Big"),
        all: vec![Name::from_dotted("Big")],
        level_params: Vec::new(),
        ty: nat,
        value: Expr::nat(size.to_string().as_str()),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    }));
    env
}

#[test]
fn a_number_is_read_through_the_constructor_form() {
    // `Nat.ble Big (Nat.succ 1)` is a comparison of two numbers, and the kernel
    // computes it in one step. The second argument is in **constructor** form,
    // and a reader that accepts only a literal declines here, leaving the term
    // stuck.
    //
    // In the prelude the cost of declining was far worse than a stuck term. δ
    // unfolded the real `Nat.ble` into the structural recursion that defines
    // it, that recursion walks its **first** argument through `Nat.brecOn`,
    // and `Nat.Linear.fixedVar` is 100,000,000. The checker counted down from
    // a hundred million. See chapter 13.
    let env = env_with_nat_ble(100_000_000);
    let mut tc = TypeChecker::new(&env);
    tc.set_fuel(SMALL);
    let term = Expr::const_("Nat.ble", vec![]).apps([
        Expr::const_("Big", vec![]),
        Expr::const_("Nat.succ", vec![]).app(Expr::nat("1")),
    ]);
    // 100000000 <= 2 is false.
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "Bool.false");
}

#[test]
fn a_number_is_read_through_a_chain_of_constructors() {
    // The chain can be more than one deep, and the innermost end can be either
    // `Nat.zero` or a literal.
    let env = env_with_nat_ble(2);
    let mut tc = TypeChecker::new(&env);
    let succ = Expr::const_("Nat.succ", vec![]);
    let three = succ.clone().app(
        succ.clone()
            .app(succ.clone().app(Expr::const_("Nat.zero", vec![]))),
    );
    let term = Expr::const_("Nat.ble", vec![]).apps([Expr::const_("Big", vec![]), three]);
    // 2 <= 3 is true.
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "Bool.true");
}

#[test]
fn something_that_is_not_a_number_is_not_read_as_one() {
    // A free variable is not a number, so the rule must decline rather than
    // invent an answer.
    let env = env_with_nat_ble(2);
    let mut tc = TypeChecker::new(&env);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("Nat", vec![])));
    let term = Expr::const_("Nat.ble", vec![]).apps([Expr::const_("Big", vec![]), x]);
    // `Nat.ble` has no value in this environment, so the term is stuck, and
    // being stuck is the right answer.
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}
