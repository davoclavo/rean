//! The branches that say "no".
//!
//! A reduction rule that fires when it should not is a soundness bug, and a
//! comparison that says yes when it should say no is worse. So every guard
//! needs a test that reaches it.

use rean_core::Name;
use rean_kernel::positivity::{self, PositivityError};
use rean_kernel::{
    AxiomVal, ConstructorVal, Declaration, DefinitionSafety, DefinitionVal, Environment, Expr,
    InductiveVal, Level, Proj, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    Sub, TypeChecker, TypeError,
};

fn prop() -> Expr {
    Expr::prop()
}

fn an_axiom(name: &str, ty: Expr) -> Declaration {
    Declaration::Axiom(AxiomVal {
        name: Name::from_dotted(name),
        level_params: Vec::new(),
        ty,
        is_unsafe: false,
    })
}

/// An environment with two unrelated propositions and a polymorphic constant.
fn two_props() -> Environment {
    let mut env = Environment::new();
    env.add(an_axiom("A", prop()));
    env.add(an_axiom("B", prop()));
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("L"),
        level_params: vec![Name::from_dotted("u")],
        ty: prop(),
        is_unsafe: false,
    }));
    // The type of a `Nat` literal is the constant `Nat`, and proof irrelevance
    // asks for the type of each side, so the constant has to be here.
    env.add(an_axiom("Nat", Expr::type_(0)));
    env
}

// --- the accessor ---------------------------------------------------------

#[test]
fn the_checker_lends_out_its_environment() {
    let env = two_props();
    let tc = TypeChecker::new(&env);
    assert_eq!(tc.env().len(), 4);
}

// --- reduction that does not stop ----------------------------------------

#[test]
fn a_definition_that_unfolds_to_itself_hits_the_limit() {
    // `def Loop : Prop := Loop`. The δ rule unfolds it forever.
    //
    // The theory says reduction terminates. A corrupt file does not have to
    // obey the theory, so the loop needs a bound, and the bound must report an
    // error rather than hang.
    let mut env = Environment::new();
    env.add(Declaration::Definition(DefinitionVal {
        name: Name::from_dotted("Loop"),
        level_params: Vec::new(),
        ty: prop(),
        value: Expr::const_("Loop", vec![]),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    }));
    let mut tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&Expr::const_("Loop", vec![])),
        Err(TypeError::ReductionLimit)
    );
}

// --- guards in the reduction rules ---------------------------------------

#[test]
fn nat_arithmetic_waits_for_two_literals() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    let partial = Expr::const_("Nat.add", vec![]).app(Expr::nat("1"));
    assert!(
        tc.whnf(&partial).unwrap().alpha_eq(&partial),
        "one argument"
    );
    let open = Expr::const_("Nat.add", vec![]).apps([Expr::nat("1"), Expr::const_("A", vec![])]);
    assert!(
        tc.whnf(&open).unwrap().alpha_eq(&open),
        "one side is not a literal"
    );
    // A name that is not an arithmetic function must not reduce.
    let other = Expr::const_("Nat.wat", vec![]).apps([Expr::nat("1"), Expr::nat("2")]);
    assert!(tc.whnf(&other).unwrap().alpha_eq(&other));
}

#[test]
fn a_bool_result_needs_the_bool_constructors() {
    // `Nat.beq 1 1` gives `Bool.true`, and that constant must exist.
    let empty = Environment::new();
    let mut tc = TypeChecker::new(&empty);
    let term = Expr::const_("Nat.beq", vec![]).apps([Expr::nat("1"), Expr::nat("1")]);
    assert!(
        tc.whnf(&term).unwrap().alpha_eq(&term),
        "no Bool, no reduction"
    );

    let mut env = Environment::new();
    env.add(an_axiom("Bool.true", Expr::type_(0)));
    let mut tc = TypeChecker::new(&env);
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "Bool.true");
}

/// The four `Quot` constants, with placeholder types.
fn quot_env() -> Environment {
    let mut env = Environment::new();
    for (name, kind) in [
        ("Quot", QuotKind::Type),
        ("Quot.mk", QuotKind::Ctor),
        ("Quot.lift", QuotKind::Lift),
        ("Quot.ind", QuotKind::Ind),
    ] {
        env.add(Declaration::Quot(QuotVal {
            name: Name::from_dotted(name),
            level_params: Vec::new(),
            ty: Expr::type_(0),
            kind,
        }));
    }
    env
}

#[test]
fn a_quotient_type_or_constructor_never_reduces() {
    let env = quot_env();
    let mut tc = TypeChecker::new(&env);
    let hole = |n: &str| Expr::const_(n, vec![]);
    // `Quot` and `Quot.mk` are data, not rules. They must stay.
    for name in ["Quot", "Quot.mk"] {
        let term = Expr::const_(name, vec![]).apps([hole("A"), hole("r"), hole("a")]);
        assert!(tc.whnf(&term).unwrap().alpha_eq(&term), "{name}");
    }
}

#[test]
fn a_quotient_rule_waits_for_enough_arguments() {
    let env = quot_env();
    let mut tc = TypeChecker::new(&env);
    let hole = |n: &str| Expr::const_(n, vec![]);
    let partial = Expr::const_("Quot.lift", vec![]).apps([hole("A"), hole("r")]);
    assert!(tc.whnf(&partial).unwrap().alpha_eq(&partial));
}

#[test]
fn a_quotient_rule_refuses_a_major_that_is_not_quot_mk() {
    let env = quot_env();
    let mut tc = TypeChecker::new(&env);
    let hole = |n: &str| Expr::const_(n, vec![]);
    // `Quot` in the major position is the wrong kind of quotient constant.
    let wrong = Expr::const_("Quot.ind", vec![]).apps([
        hole("A"),
        hole("r"),
        hole("B"),
        hole("h"),
        Expr::const_("Quot", vec![]).apps([hole("A"), hole("r"), hole("a")]),
    ]);
    assert!(tc.whnf(&wrong).unwrap().alpha_eq(&wrong));
    // And a `Quot.mk` with too few arguments is not a value either.
    let thin = Expr::const_("Quot.ind", vec![]).apps([
        hole("A"),
        hole("r"),
        hole("B"),
        hole("h"),
        Expr::const_("Quot.mk", vec![]).app(hole("A")),
    ]);
    assert!(tc.whnf(&thin).unwrap().alpha_eq(&thin));
}

#[test]
fn a_projection_waits_for_a_constructor() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    // `A` is an axiom, not a constructor, so the projection stays.
    let term = Expr::Proj(Proj {
        structure: Name::from_dotted("S"),
        index: 0,
        value: Sub::new(Expr::const_("A", vec![])),
    });
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
    // A sort in the target is not a constructor either.
    let on_sort = Expr::Proj(Proj {
        structure: Name::from_dotted("S"),
        index: 0,
        value: Sub::new(prop()),
    });
    assert!(tc.whnf(&on_sort).unwrap().alpha_eq(&on_sort));
}

// --- the K-like guards ----------------------------------------------------

/// Builds a K-like recursor over an inductive with the given shape.
fn k_env(num_ctors: usize, num_fields: u32) -> Environment {
    let mut env = Environment::new();
    let ctors: Vec<Name> = (0..num_ctors)
        .map(|i| Name::from_dotted(&format!("I.c{i}")))
        .collect();
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("I"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("I")],
        ctors: ctors.clone(),
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    for (index, name) in ctors.iter().enumerate() {
        env.add(Declaration::Constructor(ConstructorVal {
            name: name.clone(),
            level_params: Vec::new(),
            ty: if num_fields == 0 {
                Expr::const_("I", vec![])
            } else {
                Expr::arrow(Expr::type_(0), Expr::const_("I", vec![]))
            },
            induct: Name::from_dotted("I"),
            cidx: index as u32,
            num_params: 0,
            num_fields,
            is_unsafe: false,
        }));
    }
    env.add(Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("I.rec"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        all: vec![Name::from_dotted("I")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: ctors
            .iter()
            .map(|ctor| RecursorRule {
                ctor: ctor.clone(),
                num_fields,
                rhs: Expr::lam(
                    "motive",
                    Expr::type_(0),
                    Expr::lam("minor", Expr::type_(0), prop()),
                ),
            })
            .collect(),
        k: true,
        is_unsafe: false,
    }));
    env
}

/// `I.rec motive minor major`
fn apply_rec(major: Expr) -> Expr {
    Expr::const_("I.rec", vec![]).apps([Expr::type_(0), Expr::type_(0), major])
}

#[test]
fn k_like_reduction_needs_exactly_one_constructor_with_no_field() {
    // One constructor and no field: the rule fires on an opaque variable.
    let good = k_env(1, 0);
    let mut tc = TypeChecker::new(&good);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("I", vec![])));
    assert_eq!(tc.whnf(&apply_rec(x)).unwrap().pretty(), "Prop");

    // Two constructors: there is no sole constructor to build.
    let two = k_env(2, 0);
    let mut tc = TypeChecker::new(&two);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("I", vec![])));
    let term = apply_rec(x);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term), "two constructors");

    // One constructor with a field: the K rule declines, because the field
    // value is unknown. A **second** rule then applies, and it is not K.
    // `I` has one constructor, no index and no recursion, so it is a structure,
    // and `x` is definitionally `I.c0 x.0`. That is enough for ι to fire, so
    // the term does reduce here. `reduction.rs` tests that rule by name.
    let with_field = k_env(1, 1);
    let mut tc = TypeChecker::new(&with_field);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("I", vec![])));
    let term = apply_rec(x);
    assert!(!tc.whnf(&term).unwrap().alpha_eq(&term), "one field");

    // Two constructors and a field: neither rule applies.
    let two_with_field = k_env(2, 1);
    let mut tc = TypeChecker::new(&two_with_field);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("I", vec![])));
    let term = apply_rec(x);
    assert!(
        tc.whnf(&term).unwrap().alpha_eq(&term),
        "two constructors and a field"
    );
}

#[test]
fn k_like_reduction_steps_aside_for_a_real_constructor() {
    // The major premise is already a constructor, so the normal ι rule runs
    // and the K path has nothing to do.
    let env = k_env(1, 0);
    let mut tc = TypeChecker::new(&env);
    let term = apply_rec(Expr::const_("I.c0", vec![]));
    assert_eq!(tc.whnf(&term).unwrap().pretty(), "Prop");
}

#[test]
fn k_like_reduction_refuses_a_major_of_the_wrong_type() {
    let env = k_env(1, 0);
    let mut tc = TypeChecker::new(&env);
    // The type of the major premise is a sort, not the inductive type.
    let sort_major = apply_rec(prop());
    assert!(tc.whnf(&sort_major).unwrap().alpha_eq(&sort_major));

    // The type of the major premise is a different inductive type.
    let mut other = k_env(1, 0);
    other.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("J"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    let mut tc = TypeChecker::new(&other);
    let y = Expr::FVar(tc.push_local("y", Expr::const_("J", vec![])));
    let wrong = apply_rec(y);
    assert!(tc.whnf(&wrong).unwrap().alpha_eq(&wrong));
}

// --- the branches of is_def_eq that say no -------------------------------

#[test]
fn two_different_constants_are_not_equal() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    assert!(
        !tc.is_def_eq(&Expr::const_("A", vec![]), &Expr::const_("B", vec![]))
            .unwrap()
    );
}

#[test]
fn the_same_constant_at_two_universes_is_not_equal() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    let at = |n: u32| Expr::const_("L", vec![Level::of_nat(n)]);
    assert!(!tc.is_def_eq(&at(0), &at(1)).unwrap());
    assert!(tc.is_def_eq(&at(2), &at(2)).unwrap());
}

#[test]
fn two_spines_of_different_length_are_not_equal() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    let two_arg = Expr::arrow(Expr::type_(0), Expr::arrow(Expr::type_(0), Expr::type_(0)));
    let f = Expr::FVar(tc.push_local("f", two_arg));
    let one = f.clone().app(prop());
    let two = f.app(prop()).app(prop());
    assert!(!tc.is_def_eq(&one, &two).unwrap());
}

#[test]
fn a_bound_variable_can_head_a_spine() {
    // Two open terms, compared without opening a binder. Neither side has a
    // type, so only the structural path can answer.
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    let id = Expr::lam("x", Expr::type_(0), Expr::bvar(0));
    let plain = Expr::bvar(0).app(prop());
    let redex = Expr::bvar(0).app(id.app(prop()));
    assert!(
        tc.is_def_eq(&plain, &redex).unwrap(),
        "same after a beta step"
    );
    let other = Expr::bvar(0).app(Expr::type_(0));
    assert!(!tc.is_def_eq(&plain, &other).unwrap(), "different argument");
    // Two different bound variables are not equal, and neither has a type, so
    // proof irrelevance must step aside rather than fail.
    assert!(!tc.is_def_eq(&Expr::bvar(0), &Expr::bvar(1)).unwrap());
}

#[test]
fn two_function_types_compare_through_their_parts() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    let id = Expr::lam("x", Expr::type_(0), Expr::bvar(0));
    // The bodies differ by one beta step, so the two are equal.
    let plain = Expr::forall("x", prop(), prop());
    let redex = Expr::forall("x", prop(), id.app(prop()));
    assert!(tc.is_def_eq(&plain, &redex).unwrap());
    // A different domain makes them differ.
    let other_domain = Expr::forall("x", Expr::type_(0), prop());
    assert!(!tc.is_def_eq(&plain, &other_domain).unwrap());
    // A different body makes them differ.
    let other_body = Expr::forall("x", prop(), Expr::type_(0));
    assert!(!tc.is_def_eq(&plain, &other_body).unwrap());
}

#[test]
fn two_different_lambdas_are_not_equal() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    let left = Expr::lam("x", prop(), prop());
    let right = Expr::lam("x", prop(), Expr::type_(0));
    assert!(!tc.is_def_eq(&left, &right).unwrap());
}

#[test]
fn a_literal_against_a_term_that_is_not_a_nat_is_not_equal() {
    let env = two_props();
    let mut tc = TypeChecker::new(&env);
    // Neither side is a literal, so this path must step aside.
    assert!(!tc.is_def_eq(&prop(), &Expr::type_(0)).unwrap());
    // One side is a literal and the other is not a `Nat` shape at all.
    assert!(
        !tc.is_def_eq(&Expr::nat("1"), &Expr::const_("A", vec![]))
            .unwrap()
    );
    // Two literals of different value.
    assert!(!tc.is_def_eq(&Expr::nat("1"), &Expr::nat("2")).unwrap());
    // A literal against `Nat.succ` of a mismatched inner term.
    let succ_of = Expr::const_("Nat.succ", vec![]).app(Expr::nat("5"));
    assert!(!tc.is_def_eq(&Expr::nat("1"), &succ_of).unwrap());
    // Zero against a successor.
    assert!(
        !tc.is_def_eq(
            &Expr::nat("0"),
            &Expr::const_("Nat.succ", vec![]).app(Expr::nat("0"))
        )
        .unwrap()
    );
}

// --- infer_proj error paths ----------------------------------------------

#[test]
fn a_projection_whose_constructor_takes_no_parameter_fails_cleanly() {
    // The inductive type claims one parameter and its constructor type has no
    // binder to take it. A corrupt file can say that.
    let mut env = Environment::new();
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("S"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 1,
        num_indices: 0,
        all: vec![Name::from_dotted("S")],
        ctors: vec![Name::from_dotted("S.mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("S.mk"),
        level_params: Vec::new(),
        // No binder at all, although the inductive type claims a parameter.
        ty: Expr::const_("S", vec![]),
        induct: Name::from_dotted("S"),
        cidx: 0,
        num_params: 1,
        num_fields: 1,
        is_unsafe: false,
    }));
    let mut tc = TypeChecker::new(&env);
    // `s : S Prop`, so the type of `s` has one argument to fill.
    let s_type = Expr::const_("S", vec![]).app(prop());
    let s = Expr::FVar(tc.push_local("s", s_type));
    let term = Expr::Proj(Proj {
        structure: Name::from_dotted("S"),
        index: 0,
        value: Sub::new(s),
    });
    let err = tc.infer_type(&term).unwrap_err();
    assert!(matches!(err, TypeError::NotAStructure { .. }), "{err}");
}

// --- positivity edge cases ----------------------------------------------

#[test]
fn a_constructor_with_too_few_parameter_binders_is_refused() {
    let names = [Name::from_dotted("I")];
    // The declaration claims two parameters and the type has one binder.
    let ty = Expr::arrow(Expr::type_(0), Expr::const_("I", vec![]));
    assert_eq!(
        positivity::check_constructor(&ty, 2, 0, &names),
        Err(PositivityError::TooFewBinders { expected: 2 })
    );
}

#[test]
fn positivity_falls_back_to_the_single_name_when_the_group_is_empty() {
    // A declaration with an empty `all` list still has its own name.
    let mut env = Environment::new();
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Bad"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: Vec::new(),
        ctors: vec![Name::from_dotted("Bad.mk")],
        num_nested: 0,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    }));
    let bad = || Expr::const_("Bad", vec![]);
    let ctor = ConstructorVal {
        name: Name::from_dotted("Bad.mk"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::arrow(bad(), prop()), bad()),
        induct: Name::from_dotted("Bad"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let mut tc = TypeChecker::new(&env);
    let err = tc.check_positivity(&ctor).unwrap_err();
    assert!(matches!(err, TypeError::BadConstructor { .. }), "{err}");
}
