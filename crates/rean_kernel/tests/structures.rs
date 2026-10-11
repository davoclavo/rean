//! The three rules a structure needs.
//!
//! A **structure** is an inductive type with one constructor and no index.
//! Three rules of the kernel exist only for it, and the Lean prelude needs all
//! three. Chapter 9 explains why each one exists.

use rean_core::Name;
use rean_kernel::{
    ConstructorVal, Declaration, Environment, Expr, InductiveVal, Proj, RecursorRule, RecursorVal,
    Sub, TypeChecker,
};

/// Builds an inductive with the given shape, its constructor, and a recursor.
///
/// The recursor's rule returns the minor premise, so a reduction shows the
/// fields it received.
fn env_of(num_ctors: usize, num_fields: u32, num_indices: u32) -> Environment {
    let mut env = Environment::new();
    let nat = Expr::const_("Nat", vec![]);
    let ctors: Vec<Name> = (0..num_ctors)
        .map(|i| Name::from_dotted(&format!("S.c{i}")))
        .collect();
    let ty = if num_indices == 0 {
        Expr::type_(0)
    } else {
        Expr::arrow(nat.clone(), Expr::type_(0))
    };
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("S"),
        level_params: Vec::new(),
        ty,
        num_params: 0,
        num_indices,
        all: vec![Name::from_dotted("S")],
        ctors: ctors.clone(),
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    let s = Expr::const_("S", vec![]);
    for (index, name) in ctors.iter().enumerate() {
        let mut ctor_ty = if num_indices == 0 {
            s.clone()
        } else {
            s.clone().app(nat.clone())
        };
        for _ in 0..num_fields {
            ctor_ty = Expr::arrow(nat.clone(), ctor_ty);
        }
        env.add(Declaration::Constructor(ConstructorVal {
            name: name.clone(),
            level_params: Vec::new(),
            ty: ctor_ty,
            induct: Name::from_dotted("S"),
            cidx: index as u32,
            num_params: 0,
            num_fields,
            is_unsafe: false,
        }));
    }
    env.add(Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("S.rec"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        all: vec![Name::from_dotted("S")],
        num_params: 0,
        num_indices,
        num_motives: 1,
        num_minors: 1,
        rules: ctors
            .iter()
            .map(|ctor| RecursorRule {
                ctor: ctor.clone(),
                num_fields,
                // `fun motive => fun minor => minor`, so the result is the
                // minor premise applied to the fields.
                rhs: Expr::lam(
                    "motive",
                    Expr::type_(0),
                    Expr::lam("minor", Expr::type_(0), Expr::bvar(0)),
                ),
            })
            .collect(),
        k: false,
        is_unsafe: false,
    }));
    env
}

// --- eta for a structure, on the major premise ----------------------------

#[test]
fn iota_fires_on_a_variable_of_a_structure() {
    // `S` has one constructor with two fields, no index, and no recursion, so
    // `x` is definitionally `S.c0 x.0 x.1`. The ι rule may use that form.
    let env = env_of(1, 2, 0);
    let mut tc = TypeChecker::new(&env);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("S", vec![])));
    let minor = Expr::FVar(tc.push_local("minor", Expr::type_(0)));
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, x]);
    // The minor premise receives the two projections of `x`. A projection
    // prints from one, so field 0 shows as `.1`.
    let reduced = tc.whnf(&term).unwrap();
    assert_eq!(tc.lctx().pretty(&reduced), "minor x.1 x.2");
}

#[test]
fn iota_declines_when_the_type_has_two_constructors() {
    // With two constructors, a variable could be either one.
    let env = env_of(2, 2, 0);
    let mut tc = TypeChecker::new(&env);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("S", vec![])));
    let minor = Expr::FVar(tc.push_local("minor", Expr::type_(0)));
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, x]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}

#[test]
fn iota_declines_when_the_type_has_an_index() {
    // An index can differ between the variable and the rebuilt term, so the
    // two need not have the same type. `Eq` is the familiar example.
    let env = env_of(1, 2, 1);
    let mut tc = TypeChecker::new(&env);
    let nat = Expr::const_("Nat", vec![]);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("S", vec![]).app(nat.clone())));
    let minor = Expr::FVar(tc.push_local("minor", Expr::type_(0)));
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, nat, x]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}

#[test]
fn iota_declines_when_the_type_is_recursive() {
    // A field of the type itself would make the rebuilt term grow with no end.
    let mut env = env_of(1, 2, 0);
    let Some(Declaration::Inductive(ind)) = env.get(&Name::from_dotted("S")).cloned() else {
        panic!("S must be an inductive");
    };
    env.add(Declaration::Inductive(InductiveVal {
        is_rec: true,
        ..ind
    }));
    let mut tc = TypeChecker::new(&env);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("S", vec![])));
    let minor = Expr::FVar(tc.push_local("minor", Expr::type_(0)));
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, x]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}

// --- a type with one term -------------------------------------------------

#[test]
fn two_terms_of_a_one_term_type_are_equal() {
    // `S` has one constructor and no field, so it has one term. `Unit.ext` of
    // the Lean prelude is this rule.
    let env = env_of(1, 0, 0);
    let mut tc = TypeChecker::new(&env);
    let s = Expr::const_("S", vec![]);
    let a = Expr::FVar(tc.push_local("a", s.clone()));
    let b = Expr::FVar(tc.push_local("b", s));
    assert!(tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn two_terms_of_a_type_with_a_field_are_not_equal() {
    // The field values are unknown, so the two terms may differ.
    let env = env_of(1, 1, 0);
    let mut tc = TypeChecker::new(&env);
    let s = Expr::const_("S", vec![]);
    let a = Expr::FVar(tc.push_local("a", s.clone()));
    let b = Expr::FVar(tc.push_local("b", s));
    assert!(!tc.is_def_eq(&a, &b).unwrap());
}

#[test]
fn two_terms_of_two_one_term_types_are_not_equal() {
    // Each type has one term, and the two terms are not the same term.
    let mut env = env_of(1, 0, 0);
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("T"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("T")],
        ctors: vec![Name::from_dotted("T.mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("T.mk"),
        level_params: Vec::new(),
        ty: Expr::const_("T", vec![]),
        induct: Name::from_dotted("T"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    }));
    let mut tc = TypeChecker::new(&env);
    let a = Expr::FVar(tc.push_local("a", Expr::const_("S", vec![])));
    let b = Expr::FVar(tc.push_local("b", Expr::const_("T", vec![])));
    assert!(!tc.is_def_eq(&a, &b).unwrap());
}

// --- the bytes of a string literal ---------------------------------------

/// Projects the first field out of `text`.
fn bytes_of(text: &str) -> Expr {
    Expr::Proj(Proj {
        structure: Name::from_dotted("String"),
        index: 0,
        value: Sub::new(Expr::str(text)),
    })
}

#[test]
fn the_first_field_of_a_string_literal_is_its_byte_array() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&bytes_of("")).unwrap().pretty(),
        "ByteArray.mk (Array.mk.{0} UInt8 (List.nil.{0} UInt8))"
    );
    // `a` is one byte, 97.
    assert_eq!(
        tc.whnf(&bytes_of("a")).unwrap().pretty(),
        "ByteArray.mk (Array.mk.{0} UInt8 \
             (List.cons.{0} UInt8 (UInt8.ofNat 97) (List.nil.{0} UInt8)))"
    );
}

#[test]
fn the_bytes_are_utf8_and_not_code_points() {
    // `é` is one code point and two bytes. The field is a `ByteArray`, so the
    // rule must give two.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let shown = tc.whnf(&bytes_of("é")).unwrap().pretty();
    assert!(shown.contains("UInt8.ofNat 195"), "{shown}");
    assert!(shown.contains("UInt8.ofNat 169"), "{shown}");
}

#[test]
fn the_second_field_of_a_string_literal_stays_a_projection() {
    // The second field is a proof. No rule has to produce a proof, because
    // proof irrelevance makes any two of them equal.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let term = Expr::Proj(Proj {
        structure: Name::from_dotted("String"),
        index: 1,
        value: Sub::new(Expr::str("a")),
    });
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}

// --- the honest message ---------------------------------------------------

#[test]
fn a_missing_constructor_is_named_as_missing() {
    // The export is in topological order, so a constructor is absent only when
    // the kernel rejected it. Reporting "not a structure" would send the reader
    // after the wrong fault.
    let mut env = Environment::new();
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("S"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: vec![Name::from_dotted("S")],
        ctors: vec![Name::from_dotted("S.c0")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    // The constructor is absent on purpose.
    let mut tc = TypeChecker::new(&env);
    let x = Expr::FVar(tc.push_local("x", Expr::const_("S", vec![])));
    let term = Expr::Proj(Proj {
        structure: Name::from_dotted("S"),
        index: 0,
        value: Sub::new(x),
    });
    let message = tc.infer_type(&term).unwrap_err().to_string();
    assert!(message.contains("unknown constant"), "{message}");
    assert!(message.contains("S.c0"), "{message}");
}

// --- the guards that no prelude declaration reached ----------------------

#[test]
fn the_rule_declines_on_an_open_term() {
    // The rule reads the type of the major premise, and a loose bound variable
    // has no type. `eta_eq` opens a binder on purpose and hands the result to
    // `is_def_eq`, so a helper does meet an open term, and it must decline
    // rather than report an error for a rule that simply did not apply.
    let env = env_of(1, 2, 0);
    let mut tc = TypeChecker::new(&env);
    let minor = Expr::FVar(tc.push_local("minor", Expr::type_(0)));
    // The major premise is index 0, which points outside this term.
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, Expr::bvar(0)]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}

#[test]
fn both_rules_decline_when_the_constructor_is_missing() {
    // The prelude showed this cascade. A constructor the kernel rejected never
    // enters the environment, and then a later rule cannot find it. The rule
    // must decline, so that the one real fault is reported once.
    let mut env = Environment::new();
    let mut add = |ctors: Vec<Name>, name: &str| {
        env.add(Declaration::Inductive(InductiveVal {
            name: Name::from_dotted(name),
            level_params: Vec::new(),
            ty: Expr::type_(0),
            num_params: 0,
            num_indices: 0,
            all: vec![Name::from_dotted(name)],
            ctors,
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }));
    };
    add(vec![Name::from_dotted("S.c0")], "S");
    env.add(Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("S.rec"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        all: vec![Name::from_dotted("S")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: Vec::new(),
        k: false,
        is_unsafe: false,
    }));
    let mut tc = TypeChecker::new(&env);
    let s = Expr::const_("S", vec![]);
    let x = Expr::FVar(tc.push_local("x", s.clone()));
    let y = Expr::FVar(tc.push_local("y", s));
    let minor = Expr::FVar(tc.push_local("minor", Expr::type_(0)));

    // The ι rule finds a structure and no constructor to build.
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, x.clone()]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
    // And the one term rule cannot learn whether the constructor has a field.
    assert!(!tc.is_def_eq(&x, &y).unwrap());
}

#[test]
fn the_rule_declines_for_a_sibling_of_a_mutual_group() {
    // `S` is a structure and `M` is not, and one recursor speaks about both.
    // A term of `M` must not be rebuilt as a constructor of `S`.
    let mut env = env_of(1, 2, 0);
    let both = vec![Name::from_dotted("S"), Name::from_dotted("M")];
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("M"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: both.clone(),
        ctors: vec![Name::from_dotted("M.a"), Name::from_dotted("M.b")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    for name in ["M.a", "M.b"] {
        env.add(Declaration::Constructor(ConstructorVal {
            name: Name::from_dotted(name),
            level_params: Vec::new(),
            ty: Expr::const_("M", vec![]),
            induct: Name::from_dotted("M"),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }));
    }
    // The recursor now covers the group, so the cheap test passes and the real
    // one has to refuse.
    let Some(Declaration::Recursor(rec)) = env.get(&Name::from_dotted("S.rec")).cloned() else {
        panic!("S.rec must be a recursor");
    };
    env.add(Declaration::Recursor(RecursorVal { all: both, ..rec }));
    let mut tc = TypeChecker::new(&env);
    let m = Expr::FVar(tc.push_local("m", Expr::const_("M", vec![])));
    let minor = Expr::FVar(tc.push_local("minor", Expr::type_(0)));
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, m]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}

#[test]
fn the_rule_declines_when_the_type_is_missing_its_parameters() {
    // `S` takes one parameter, so a term whose type is a bare `S` is not well
    // formed. The rule cannot read the parameter, so it refuses rather than
    // build a constructor with a missing argument.
    let mut env = Environment::new();
    let nat = Expr::const_("Nat", vec![]);
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("S"),
        level_params: Vec::new(),
        ty: Expr::arrow(Expr::type_(0), Expr::type_(0)),
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
        ty: Expr::forall(
            "a",
            Expr::type_(0),
            Expr::arrow(Expr::bvar(0), Expr::const_("S", vec![]).app(Expr::bvar(1))),
        ),
        induct: Name::from_dotted("S"),
        cidx: 0,
        num_params: 1,
        num_fields: 1,
        is_unsafe: false,
    }));
    env.add(Declaration::Recursor(RecursorVal {
        name: Name::from_dotted("S.rec"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        all: vec![Name::from_dotted("S")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: Name::from_dotted("S.mk"),
            num_fields: 1,
            rhs: Expr::lam(
                "motive",
                Expr::type_(0),
                Expr::lam("minor", Expr::type_(0), Expr::bvar(0)),
            ),
        }],
        k: false,
        is_unsafe: false,
    }));
    let mut tc = TypeChecker::new(&env);
    // The type is `S` with no argument, so there is no parameter to read.
    let x = Expr::FVar(tc.push_local("x", Expr::const_("S", vec![])));
    let minor = Expr::FVar(tc.push_local("minor", nat));
    let term = Expr::const_("S.rec", vec![]).apps([Expr::type_(0), minor, x]);
    assert!(tc.whnf(&term).unwrap().alpha_eq(&term));
}
