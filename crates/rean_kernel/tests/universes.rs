//! Executable examples for `docs/00-introduction-to-the-kernel.md`.
//!
//! Every claim that the chapter makes about `Sort`, `Prop`, `Type`, and `Not`
//! has a test here. If a claim in the chapter goes stale, a test fails.

use rean_kernel::{Expr, Level};

/// `Nat`, as the kernel sees it.
fn nat() -> Expr {
    Expr::const_("Nat", vec![])
}

/// `False`, as the kernel sees it.
fn false_() -> Expr {
    Expr::const_("False", vec![])
}

/// `True`, as the kernel sees it.
fn true_() -> Expr {
    Expr::const_("True", vec![])
}

/// `Not := fun (p : Prop) => p → False`.
fn not() -> Expr {
    Expr::lam("p", Expr::prop(), Expr::arrow(Expr::bvar(0), false_()))
}

/// The level of `(x : A) → B` when `A : Sort u` and `B : Sort v`.
fn pi_level(u: u32, v: u32) -> u32 {
    Level::of_nat(u)
        .imax(&Level::of_nat(v))
        .to_nat()
        .expect("both levels are closed")
}

// --- section 0.9: Sort, Prop, and Type ------------------------------------

#[test]
fn prop_and_type_are_both_just_sort() {
    // The kernel has one universe former. `Prop` and `Type` are two names.
    assert_eq!(Expr::prop(), Expr::Sort(Level::Zero));
    assert_eq!(Expr::type_(0), Expr::Sort(Level::of_nat(1)));
    assert_eq!(Expr::type_(4), Expr::Sort(Level::of_nat(5)));
}

#[test]
fn the_printer_turns_sort_back_into_the_familiar_names() {
    assert_eq!(Expr::prop().pretty(), "Prop");
    assert_eq!(Expr::type_(0).pretty(), "Type");
    assert_eq!(Expr::type_(2).pretty(), "Type 2");
    // An open level has no short name, so the printer says `Sort`.
    assert_eq!(Expr::sort(Level::param("u")).pretty(), "Sort u");
}

#[test]
fn there_is_no_level_below_zero() {
    // `Level` has `Zero` and `Succ`. It has no predecessor, so `Sort -1` is
    // not a rejected term. It cannot be written at all.
    assert!(Level::of_nat(0).is_zero());
    assert_eq!(Level::of_nat(0), Level::Zero);
    // Every closed level is at least 0, because `to_nat` returns a `u32`.
    for n in 0..5 {
        assert_eq!(Level::of_nat(n).to_nat(), Some(n));
    }
}

// --- section 0.10: why Prop and Type differ -------------------------------

#[test]
fn a_function_into_prop_stays_in_prop() {
    // `P → Q` with `P, Q : Prop`. Both sides sit at level 0.
    assert_eq!(pi_level(0, 0), 0);
    // `∀ (α : Type 98), α = α`. The domain sits at level 99 and the body
    // `α = α` is a Prop, so the whole term collapses back to level 0.
    // This is impredicativity, and `imax` is the only reason it works.
    //
    // Note the trap. `∀ (α : Type 98), α → α` is NOT a Prop. There the body
    // sits at level 99, not 0, so `imax` does not collapse. A big domain alone
    // does not make a Prop. The body must land at level 0.
    assert_eq!(pi_level(99, 0), 0);
    assert_eq!(
        pi_level(99, 99),
        99,
        "a body above level 0 does not collapse"
    );
}

#[test]
fn a_function_between_data_does_not_collapse() {
    // `Prop → Prop`. Both sides are `Sort 1`, because `Prop : Sort 1`.
    // So `Not` is data, and it lives at `Type`.
    assert_eq!(pi_level(1, 1), 1);
    // `Nat → Nat`. The same arithmetic, the same answer.
    assert_eq!(pi_level(1, 1), 1);
    // `Prop → Type`, which is the type of `Decidable`.
    assert_eq!(pi_level(1, 2), 2);
}

// --- section 0.11: Prop and Nat share a universe --------------------------

#[test]
fn prop_and_nat_fit_the_same_container() {
    let list = Expr::const_("List", vec![Level::Zero]);
    assert_eq!(list.clone().app(nat()).pretty(), "List.{0} Nat");
    assert_eq!(list.clone().app(Expr::prop()).pretty(), "List.{0} Prop");
}

// --- section 0.11: the `Not False` puzzle ---------------------------------

#[test]
fn not_is_a_function_from_prop_to_prop() {
    assert_eq!(not().pretty(), "fun (p : Prop) => p → False");
    // The type of `Not`. It is data, not a proposition.
    assert_eq!(
        Expr::arrow(Expr::prop(), Expr::prop()).pretty(),
        "Prop → Prop"
    );
}

#[test]
fn not_false_reduces_to_false_arrow_false() {
    let term = not().app(false_());
    assert_eq!(term.pretty(), "(fun (p : Prop) => p → False) False");
    assert_eq!(term.beta().pretty(), "False → False");
}

#[test]
fn not_false_is_not_the_term_true() {
    // `Not False` is a TRUE proposition, because `fun h => h` proves it.
    // It is still not the TERM `True`. The kernel keeps the two apart.
    let reduced = not().app(false_()).beta();
    assert_ne!(reduced, true_());
}

#[test]
fn not_true_reduces_to_true_arrow_false() {
    let reduced = not().app(true_()).beta();
    assert_eq!(reduced.pretty(), "True → False");
    assert_ne!(reduced, false_());
}

#[test]
fn double_negation_keeps_nesting_the_arrow() {
    let not_false = not().app(false_()).beta();
    let reduced = not().app(not_false).beta();
    assert_eq!(reduced.pretty(), "(False → False) → False");
}

#[test]
fn head_beta_leaves_an_inner_redex_alone() {
    // `beta` reduces the head only. It does not go under a binder. A full
    // normal form needs more, and chapter 1 will add it.
    let inner = not().app(false_());
    let outer = not().app(inner);
    assert!(outer.beta().pretty().contains("fun (p : Prop)"));
}

// --- section 0.5: substitution and de Bruijn indices ----------------------

#[test]
fn de_bruijn_erases_the_binder_name_from_the_body() {
    let with_x = Expr::lam("x", nat(), Expr::bvar(0));
    let with_y = Expr::lam("y", nat(), Expr::bvar(0));
    // The bodies are the same data. Only the printer keeps the name.
    let (Expr::Lam { body: a, .. }, Expr::Lam { body: b, .. }) = (&with_x, &with_y) else {
        panic!("both terms are lambdas");
    };
    assert_eq!(a, b);
}

#[test]
fn an_arrow_is_a_forall_whose_body_ignores_the_binder() {
    let term = Expr::arrow(nat(), nat());
    assert!(matches!(term, Expr::Forall { .. }));
    assert_eq!(term.pretty(), "Nat → Nat");
    let Expr::Forall { body, .. } = &term else {
        panic!("an arrow is a forall");
    };
    assert!(!body.has_loose_bvar(0), "the body must not use the binder");
}

#[test]
fn a_dependent_forall_does_use_its_binder() {
    // `(α : Type) → α → α`, the type of the identity function.
    let term = Expr::forall(
        "α",
        Expr::type_(0),
        Expr::arrow(Expr::bvar(0), Expr::bvar(0)),
    );
    assert_eq!(term.pretty(), "(α : Type) → α → α");
    let Expr::Forall { body, .. } = &term else {
        panic!("a forall");
    };
    assert!(body.has_loose_bvar(0), "the body must use the binder");
}
