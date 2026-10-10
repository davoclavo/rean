//! Chapter 4. Does the checker handle what a beginner writes?
//!
//! Every test here failed before chapter 4. Each one is a shape that a person
//! writes on their first day with Lean, and each one needs a rule that the
//! fixture of chapter 3 never exercised.

use rean_kernel::{Expr, Level, TypeChecker};

fn module() -> rean_export::Module {
    rean_export::read_module("../../fixtures/lean4export/Nat.add_succ.ndjson")
        .expect("the fixture must read")
}

fn nat() -> Expr {
    Expr::const_("Nat", vec![])
}

fn zero() -> Expr {
    Expr::const_("Nat.zero", vec![])
}

fn succ(x: Expr) -> Expr {
    Expr::const_("Nat.succ", vec![]).app(x)
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::const_("Nat.add", vec![]).apps([a, b])
}

#[test]
fn arithmetic_on_literals_computes() {
    // Before chapter 4 this unfolded through `Nat.rec` once per unit and got
    // stuck in a wall of `Nat.brecOn`.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    assert_eq!(
        tc.whnf(&add(Expr::nat("2"), Expr::nat("3")))
            .unwrap()
            .pretty(),
        "5"
    );
    assert_eq!(
        tc.whnf(&add(Expr::nat("0"), Expr::nat("7")))
            .unwrap()
            .pretty(),
        "7"
    );
}

#[test]
fn two_plus_three_equals_five() {
    // The first thing anybody writes. `rfl` proves it, so the kernel must see
    // the two sides as definitionally equal.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    assert!(
        tc.is_def_eq(&add(Expr::nat("2"), Expr::nat("3")), &Expr::nat("5"))
            .unwrap()
    );
    assert!(
        !tc.is_def_eq(&add(Expr::nat("2"), Expr::nat("3")), &Expr::nat("6"))
            .unwrap()
    );
}

#[test]
fn a_literal_equals_the_constructor_chain() {
    // `3` is stored as digits for speed. In the theory it is three successors.
    // The kernel must treat the two as one number.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    assert!(tc.is_def_eq(&Expr::nat("1"), &succ(zero())).unwrap());
    assert!(
        tc.is_def_eq(&Expr::nat("3"), &succ(succ(succ(zero()))))
            .unwrap()
    );
    assert!(!tc.is_def_eq(&Expr::nat("2"), &succ(zero())).unwrap());
    // And in the other order.
    assert!(tc.is_def_eq(&succ(zero()), &Expr::nat("1")).unwrap());
}

#[test]
fn a_literal_works_as_a_major_premise_for_iota() {
    // `Nat.add n 3` must fire the `Nat.succ` rule, so `3` has to behave like
    // `Nat.succ 2`.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let n = Expr::FVar(tc.push_local("n", nat()));
    let left = add(n.clone(), Expr::nat("1"));
    let right = succ(add(n, Expr::nat("0")));
    assert!(tc.is_def_eq(&left, &right).unwrap());
}

#[test]
fn eq_rec_reduces_on_an_opaque_proof() {
    // K-like ι. `Eq` has one constructor with no field, so a proof of `a = a`
    // carries nothing beyond its own existence. The recursor may reduce even
    // when the proof is a variable.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let one = Level::of_nat(1);
    let a = Expr::FVar(tc.push_local("a", nat()));
    let eq = |x: Expr, y: Expr| Expr::const_("Eq", vec![one.clone()]).apps([nat(), x, y]);
    let h = Expr::FVar(tc.push_local("h", eq(a.clone(), a.clone())));
    let motive = Expr::lam(
        "b",
        nat(),
        Expr::lam("hb", eq(a.clone(), Expr::bvar(0)), nat()),
    );
    let term = Expr::const_("Eq.rec", vec![one.clone(), one]).apps([
        nat(),
        a.clone(),
        motive,
        zero(),
        a,
        h,
    ]);
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "Nat.zero");
}

#[test]
fn a_huge_literal_stays_stuck_rather_than_lie() {
    // `u128` is the limit of this kernel's arithmetic. Past it, the term does
    // not reduce. A stuck term is correct. A wrapped answer would not be.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let huge = "9".repeat(60);
    let term = add(Expr::nat(huge.as_str()), Expr::nat("1"));
    let reduced = tc.whnf(&term).unwrap();
    assert!(
        rean_kernel::nat_lit::value(&reduced).is_none(),
        "it must not produce a number"
    );
}

#[test]
fn the_fixture_still_passes_with_every_new_rule() {
    // Chapter 4 added five rules. None of them may break chapter 3.
    let m = module();
    let mut known = rean_kernel::Environment::new();
    let mut failures = Vec::new();
    for name in &m.order {
        let decl = m.env.get(name).unwrap();
        let mut tc = TypeChecker::new(&known);
        if let Err(err) = tc.check_declaration(decl) {
            failures.push(format!("{name}: {}", err.render(tc.lctx())));
        }
        known.add(decl.clone());
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(m.order.len(), 32);
}

#[test]
fn the_positivity_check_accepts_every_real_constructor() {
    // Lean wrote these seven. A check that rejects a correct declaration is
    // worse than no check at all.
    let m = module();
    let mut tc = TypeChecker::new(&m.env);
    let mut seen = 0;
    for name in &m.order {
        if let Some(rean_kernel::Declaration::Constructor(ctor)) = m.env.get(name) {
            tc.check_positivity(ctor)
                .unwrap_or_else(|err| panic!("{name} was rejected: {err}"));
            seen += 1;
        }
    }
    assert_eq!(seen, 7);
}
