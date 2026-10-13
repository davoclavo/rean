//! The two limits, and the rule they both obey: **a limit is a verdict.**
//!
//! A checker meets two things it cannot finish: work without end, and
//! recursion without end. Chapter 17 bounded the first with a work budget.
//! Chapter 24 bounds the second with the stack, after a run at a hundred times
//! the default budget overflowed 4 GB and **aborted**, which is the one answer
//! a report cannot carry.
//!
//! Both limits say the same thing: we did not check it. Neither says the
//! declaration is wrong, and [`TypeError::is_a_limit`] is how the rules of
//! `is_def_eq` tell them apart from an answer.

use rean_kernel::{Environment, Expr, TypeChecker, TypeError};

/// Builds `f (f (f ... x))`, nested `depth` times.
///
/// The term is closed and it holds no rule to fire, so what the kernel does
/// with it is pure recursion over the shape, which is the thing being bounded.
fn nested(depth: usize) -> Expr {
    let mut term = Expr::const_("x", vec![]);
    for _ in 0..depth {
        term = Expr::const_("f", vec![]).app(term);
    }
    term
}

#[test]
fn a_recursion_past_the_allowance_is_a_verdict_and_not_a_crash() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    // One byte. The first entry records where the stack is and has used
    // nothing, so it passes; anything nested inside it has used more than one
    // byte and is refused.
    tc.set_stack_budget(1);
    let error = tc
        .infer_type(&nested(8))
        .expect_err("a nested term must reach the guard");
    assert_eq!(error, TypeError::OutOfStack(1));
    assert!(error.is_a_limit());
}

#[test]
fn the_message_names_the_knob_that_raises_it() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let message = TypeError::OutOfStack(512 * 1024 * 1024).render(tc.lctx());
    assert!(message.contains("512 MiB"), "{message}");
    assert!(message.contains("REAN_STACK"), "{message}");
    // "so it was not checked" is the sentence that both limits share. A
    // reader must not read either one as "this declaration is wrong".
    assert!(message.contains("not checked"), "{message}");
}

#[test]
fn the_budget_is_a_limit_and_a_type_error_is_not() {
    assert!(TypeError::OutOfFuel(20_000_000).is_a_limit());
    assert!(TypeError::OutOfStack(1).is_a_limit());
    // A real fault in a term is not a limit, and the rules of `is_def_eq`
    // depend on that difference: a limit must travel out, and anything else
    // means "this rule does not apply".
    assert!(!TypeError::LooseBVar(0).is_a_limit());
    assert!(!TypeError::UnknownConstant(rean_core::Name::from_dotted("Nat.foo")).is_a_limit());
}

#[test]
fn a_generous_allowance_checks_the_same_term() {
    // The guard must not refuse ordinary work. The same term, with the
    // allowance a main thread can afford, reaches a real answer instead: `f`
    // is not in the environment, so the kernel says which constant is missing.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_stack_budget(4 * 1024 * 1024);
    let error = tc.infer_type(&nested(8)).expect_err("`f` is not declared");
    assert!(!error.is_a_limit(), "{error:?}");
    assert_eq!(
        error,
        TypeError::UnknownConstant(rean_core::Name::from_dotted("f"))
    );
}
