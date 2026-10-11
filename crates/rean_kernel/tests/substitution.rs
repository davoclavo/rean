//! Discharging several binders at once must give what doing them one at a time
//! gave.
//!
//! A β step used to substitute one argument and rebuild the whole remaining
//! term, once per argument. It now discharges the whole spine in one pass. That
//! is the same answer and much less work, and a substitution that is **nearly**
//! right is a soundness bug, so this file compares the two directly.
//!
//! Chapter 14 explains the cost. This file is about the correctness.

use rean_kernel::{Expr, FVarId};

/// The old β step: take one argument, rebuild, and leave the rest applied.
///
/// This is the reference. It is kept here, in a test, rather than in the
/// kernel, because its answer is the thing being checked and not the thing
/// being used.
fn one_at_a_time(term: &Expr) -> Option<Expr> {
    let (head, args) = term.unfold_apps();
    let Expr::Lam { body, .. } = head else {
        return None;
    };
    let first = *args.first()?;
    let reduced = body.instantiate(first);
    Some(reduced.apps(args[1..].iter().map(|arg| (*arg).clone())))
}

/// Repeats the reference step until no step applies.
fn beta_reference(term: &Expr) -> Expr {
    let mut current = term.clone();
    while let Some(next) = one_at_a_time(&current) {
        current = next;
    }
    current
}

fn nat() -> Expr {
    Expr::const_("Nat", vec![])
}

/// `fun x1 => fun x2 => ... => body`, with `depth` binders.
fn lambdas(depth: usize, body: Expr) -> Expr {
    let mut term = body;
    for _ in 0..depth {
        term = Expr::lam("x", nat(), term);
    }
    term
}

/// Every shape worth trying, each applied to a spine of free variables.
fn cases() -> Vec<Expr> {
    let f = |n: u64| Expr::FVar(FVarId(n));
    let a = f(1);
    let b = f(2);
    let c = f(3);
    vec![
        // The arguments arrive in the right order.
        lambdas(3, Expr::bvar(2).apps([Expr::bvar(1), Expr::bvar(0)])).apps([
            a.clone(),
            b.clone(),
            c.clone(),
        ]),
        // The outermost binder is the first argument.
        lambdas(2, Expr::bvar(1)).apps([a.clone(), b.clone()]),
        // The innermost binder is the last argument.
        lambdas(2, Expr::bvar(0)).apps([a.clone(), b.clone()]),
        // An index above the window moves down by the whole width.
        lambdas(2, Expr::bvar(3)).apps([a.clone(), b.clone()]),
        // A binder inside the body lifts each value as it goes past.
        lambdas(2, Expr::lam("y", nat(), Expr::bvar(2).app(Expr::bvar(1))))
            .apps([a.clone(), b.clone()]),
        // Fewer arguments than binders.
        lambdas(3, Expr::bvar(2).apps([Expr::bvar(1), Expr::bvar(0)])).app(a.clone()),
        // More arguments than binders.
        lambdas(1, Expr::bvar(0)).apps([a.clone(), b.clone(), c.clone()]),
        // A `let` in the body, which has a binder of its own.
        lambdas(
            2,
            Expr::let_("z", nat(), Expr::bvar(1), Expr::bvar(2).app(Expr::bvar(0))),
        )
        .apps([a.clone(), b.clone()]),
        // A long spine, which is the shape this change exists for.
        lambdas(12, Expr::bvar(11).apps((0..11).rev().map(Expr::bvar))).apps((1..=12).map(f)),
        // Nothing to do.
        lambdas(2, Expr::bvar(0)),
        nat().app(a),
    ]
}

#[test]
fn one_pass_gives_what_many_passes_gave() {
    for term in cases() {
        let batched = term.beta();
        let reference = beta_reference(&term);
        assert!(
            batched.alpha_eq(&reference),
            "\n  term:      {}\n  batched:   {}\n  reference: {}",
            term.pretty(),
            batched.pretty(),
            reference.pretty()
        );
    }
}

#[test]
fn the_arguments_keep_their_order() {
    // The outermost binder takes the first argument. Reversing this is the
    // mistake that a differential test alone might not show, because a
    // symmetric body hides it.
    let f = |n: u64| Expr::FVar(FVarId(n));
    let term =
        lambdas(3, Expr::bvar(2).apps([Expr::bvar(1), Expr::bvar(0)])).apps([f(1), f(2), f(3)]);
    assert_eq!(term.beta().pretty(), "_f1 _f2 _f3");
}

#[test]
fn an_index_above_the_window_moves_down_by_the_width() {
    // Two binders go, so index 3 becomes index 1.
    let term = lambdas(2, Expr::bvar(3)).apps([Expr::FVar(FVarId(1)), Expr::FVar(FVarId(2))]);
    assert_eq!(term.beta().pretty(), "#1");
}

#[test]
fn a_value_is_lifted_past_a_binder_in_the_body() {
    // The body keeps a binder of its own, so a free index inside it counts one
    // deeper. Here the values are free variables, which no lift can change, so
    // the test uses a bound one.
    let inner = Expr::lam("y", nat(), Expr::bvar(1));
    let term = lambdas(1, inner).app(Expr::bvar(0));
    // `#0` from outside the step is `#1` once it sits under `y`.
    assert_eq!(term.beta().pretty(), "fun (y : Nat) => #1");
}

#[test]
fn instantiate_many_with_nothing_changes_nothing() {
    let term = lambdas(2, Expr::bvar(0));
    assert!(term.instantiate_many(&[]).alpha_eq(&term));
}
