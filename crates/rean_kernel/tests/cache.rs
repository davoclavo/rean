//! The hash in every node, and the cache it serves.
//!
//! The one rule that keeps a cache sound: a hash **finds** an answer, and
//! [`Expr::alpha_eq`] **decides** whether to trust it. Chapter 10 explains why.

use rean_core::Name;
use rean_kernel::{
    Declaration, DefinitionSafety, DefinitionVal, Environment, Expr, Level, ReducibilityHints,
    TypeChecker,
};

/// The invariant a hash must keep: equal terms hash equally.
///
/// If this fails, a lookup of a term misses an answer that is there. That costs
/// speed and not correctness, but it also means the cache does nothing.
fn must_agree(a: &Expr, b: &Expr) {
    assert!(
        a.alpha_eq(b),
        "the test is wrong: {} vs {}",
        a.pretty(),
        b.pretty()
    );
    assert_eq!(
        a.hash_value(),
        b.hash_value(),
        "equal terms must hash equally: {} vs {}",
        a.pretty(),
        b.pretty()
    );
}

#[test]
fn a_binder_name_does_not_change_the_hash() {
    // `alpha_eq` ignores the name of a binder, so the hash must ignore it too.
    let nat = Expr::const_("Nat", vec![]);
    must_agree(
        &Expr::lam("x", nat.clone(), Expr::bvar(0)),
        &Expr::lam("y", nat.clone(), Expr::bvar(0)),
    );
    must_agree(
        &Expr::forall("x", nat.clone(), Expr::bvar(0)),
        &Expr::forall("whatever", nat.clone(), Expr::bvar(0)),
    );
    must_agree(
        &Expr::let_("x", nat.clone(), nat.clone(), Expr::bvar(0)),
        &Expr::let_("z", nat.clone(), nat, Expr::bvar(0)),
    );
}

#[test]
fn an_equivalent_level_does_not_change_the_hash() {
    // `alpha_eq` compares a level by equivalence and not by shape. `max u u` is
    // `u`, so the two terms are equal and must hash equally.
    let u = Level::param("u");
    let doubled = Level::Max(u.clone().into(), u.clone().into());
    must_agree(&Expr::sort(u.clone()), &Expr::sort(doubled.clone()));
    must_agree(
        &Expr::const_("List", vec![u]),
        &Expr::const_("List", vec![doubled]),
    );
}

#[test]
fn a_different_term_usually_hashes_differently() {
    // The hash is only a filter, so this is not a requirement. It is a check
    // that the filter filters, because a hash that is always the same would
    // turn every lookup into a walk of one long bucket.
    let nat = Expr::const_("Nat", vec![]);
    let terms = [
        Expr::bvar(0),
        Expr::bvar(1),
        nat.clone(),
        Expr::const_("Int", vec![]),
        nat.clone().app(nat.clone()),
        Expr::lam("x", nat.clone(), Expr::bvar(0)),
        Expr::forall("x", nat.clone(), Expr::bvar(0)),
        Expr::nat("7"),
        Expr::nat("8"),
        Expr::str("hi"),
    ];
    let mut seen: Vec<u64> = terms.iter().map(Expr::hash_value).collect();
    let total = seen.len();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(
        seen.len(),
        total,
        "these ten terms should hash to ten values"
    );
}

/// An environment with `D := Nat`, so that δ has something to unfold.
fn with_a_definition() -> Environment {
    let mut env = Environment::new();
    env.add(Declaration::Definition(DefinitionVal {
        name: Name::from_dotted("D"),
        all: vec![Name::from_dotted("D")],
        level_params: Vec::new(),
        ty: Expr::type_(0),
        value: Expr::const_("Nat", vec![]),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    }));
    env
}

#[test]
fn the_answer_is_the_same_whether_it_is_cached_or_not() {
    // The second call hits the cache. A cache that changes an answer is a bug
    // no coverage number would find.
    let env = with_a_definition();
    let mut tc = TypeChecker::new(&env);
    // Large enough that the cache takes an interest. See `CACHE_MIN_SIZE`.
    let term = Expr::const_("D", vec![]).apps([
        Expr::const_("D", vec![]),
        Expr::const_("D", vec![]),
        Expr::const_("D", vec![]),
    ]);
    let first = tc.whnf(&term).unwrap();
    let second = tc.whnf(&term).unwrap();
    assert!(
        first.alpha_eq(&second),
        "{} vs {}",
        first.pretty(),
        second.pretty()
    );
    assert_eq!(first.pretty(), "Nat D D D");
}

#[test]
fn a_cached_answer_does_not_outlive_its_declaration() {
    // A term that mentions a free variable only means something in the context
    // that holds it, so `check_declaration` starts with an empty cache.
    let env = with_a_definition();
    let mut tc = TypeChecker::new(&env);
    let term =
        Expr::const_("D", vec![]).apps([Expr::const_("D", vec![]), Expr::const_("D", vec![])]);
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "Nat D D");
    // Checking a declaration clears the cache, and the answer is still right.
    // `E : Type 1 := Type 0` needs no constant, so the check can pass here.
    let decl = Declaration::Definition(DefinitionVal {
        name: Name::from_dotted("E"),
        all: vec![Name::from_dotted("E")],
        level_params: Vec::new(),
        ty: Expr::type_(1),
        value: Expr::type_(0),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    });
    tc.check_declaration(&decl).unwrap();
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "Nat D D");
}
