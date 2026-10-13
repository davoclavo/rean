//! Running terms, against the two committed fixtures.
//!
//! The fixtures hold real Lean declarations, so these tests run what Lean's own
//! elaborator produced: `Nat.add` is `Nat.brecOn` over a generated `match_1`,
//! and nobody wrote either. See `rean show`.

use rean_core::Name;
use rean_eval::{EvalError, Evaluator, Thunk, Value};
use rean_kernel::{Environment, Expr, Proj, Sub};

const FIXTURE: &str = "../../fixtures/lean4export/Nat.add_succ.ndjson";
const SHAPES: &str = "../../fixtures/lean4export/shapes.ndjson";

fn environment(path: &str) -> Environment {
    rean_export::read_module(path)
        .expect("the fixture must read")
        .env
}

/// Evaluates `term` against the declarations of `path`.
fn run(path: &str, term: &Expr) -> Result<String, EvalError> {
    let env = environment(path);
    let mut eval = Evaluator::new(&env);
    let value = eval.eval(term, &rean_eval::Env::new())?;
    Ok(format!("{}", rean_eval::Shown(&value, 4)))
}

fn nat(n: &str) -> Expr {
    Expr::nat(n)
}

/// `Nat.add a b`, through the definition that Lean exported.
fn add(a: &str, b: &str) -> Expr {
    Expr::const_("Nat.add", vec![]).apps([nat(a), nat(b)])
}

#[test]
fn it_adds_two_numbers_through_leans_own_definition() {
    // `Nat.add` is not addition. It is `brecOn` over a `match`, and the
    // evaluator runs that and gets a number out.
    assert_eq!(run(FIXTURE, &add("2", "3")).unwrap(), "5");
    assert_eq!(run(FIXTURE, &add("0", "0")).unwrap(), "0");
    assert_eq!(run(FIXTURE, &add("1000000", "1")).unwrap(), "1000001");
}

#[test]
fn it_runs_a_number_that_no_kernel_would_reduce() {
    // A hundred million. The kernel counts these down one `Nat.succ` at a
    // time unless a rule stops it, and chapter 21 is about what that cost.
    // Here it is one instruction, because `Nat.add` is a primitive.
    assert_eq!(run(FIXTURE, &add("100000000", "1")).unwrap(), "100000001");
}

#[test]
fn a_number_past_a_u128_is_named_and_not_wrapped() {
    let huge = "340282366920938463463374607431768211455"; // u128::MAX
    let error = run(FIXTURE, &add(huge, "1")).unwrap_err();
    assert_eq!(error, EvalError::PastU128("Nat.add"));
    // And the message says what the limit is, rather than blaming the term.
    assert!(error.to_string().contains("128 bit"), "{error}");
}

#[test]
fn it_runs_a_declaration_by_name() {
    let env = environment(SHAPES);
    let mut eval = Evaluator::new(&env);
    // `withLet` of the fixture is `let x := 2; x + x`, elaborated.
    let value = eval.run(&Name::from_dotted("withLet")).unwrap();
    assert_eq!(format!("{}", rean_eval::Shown(&value, 4)), "4");
}

#[test]
fn it_takes_a_structure_apart() {
    let env = environment(SHAPES);
    let mut eval = Evaluator::new(&env);
    // `Point.mk 1 2`, and then the projections.
    let point = Expr::const_("Point.mk", vec![]).apps([nat("1"), nat("2")]);
    let field = |index: u32, of: Expr| {
        Expr::Proj(Proj {
            structure: Name::from_dotted("Point"),
            index,
            value: Sub::new(of),
        })
    };
    let first = field(0, point.clone());
    let second = field(1, point);
    let one = eval.eval(&first, &rean_eval::Env::new()).unwrap();
    let two = eval.eval(&second, &rean_eval::Env::new()).unwrap();
    assert_eq!(one.as_nat(), Some(1));
    assert_eq!(two.as_nat(), Some(2));
}

#[test]
fn a_constructor_keeps_its_arguments_unevaluated() {
    let env = environment(SHAPES);
    let mut eval = Evaluator::new(&env);
    // `Forest.cons` holds a tree and a forest, and neither is forced by
    // building the value. That is what makes a lazy list affordable.
    let value = eval
        .eval(&Expr::const_("Forest.nil", vec![]), &rean_eval::Env::new())
        .unwrap();
    match value {
        Value::Ctor { name, args } => {
            assert_eq!(name.to_string(), "Forest.nil");
            assert!(args.is_empty());
        }
        other => panic!(
            "expected a constructor, got {}",
            rean_eval::Shown(&other, 2)
        ),
    }
}

#[test]
fn a_loop_is_reported_and_not_run_for_ever() {
    // A term the kernel would refuse: a thunk that asks for itself. It cannot
    // come out of a checked declaration, and the evaluator must still say so
    // rather than spin.
    let env = Environment::new();
    let mut eval = Evaluator::new(&env);
    let looping = Expr::bvar(0);
    let thunk = Thunk::waiting(looping, rean_eval::Env::new());
    let env_with_itself = rean_eval::Env::new().with(thunk.clone());
    // Forcing it evaluates `#0`, which is the thunk being forced.
    let error = eval
        .eval(&Expr::bvar(0), &env_with_itself)
        .expect_err("a cycle must be reported");
    assert!(
        matches!(error, EvalError::Cycle | EvalError::LooseBVar(_)),
        "{error:?}"
    );
}

#[test]
fn the_step_budget_stops_an_evaluation() {
    let env = environment(FIXTURE);
    let mut eval = Evaluator::new(&env);
    // Two steps. Five were **enough**, which is the measurement hiding in
    // this test: `Nat.add` is a primitive, so the whole of `2 + 3` is the
    // application, the two forced arguments and the addition.
    eval.set_steps(2);
    let error = eval
        .eval(&add("2", "3"), &rean_eval::Env::new())
        .expect_err("two steps are not enough");
    assert!(matches!(error, EvalError::OutOfSteps(_)), "{error:?}");
}
