//! The last corners.

use rean_core::Name;
use rean_kernel::{
    AxiomVal, BinderInfo, ConstructorVal, Declaration, Environment, Expr, InductiveVal, Level,
    Proj, TypeChecker, nat_lit,
};
use std::sync::Arc;

fn prop() -> Expr {
    Expr::prop()
}

#[test]
fn the_local_context_lists_its_entries() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.push_local("a", prop());
    tc.push_local("b", prop());
    let decls = tc.lctx().decls();
    assert_eq!(decls.len(), 2);
    // The list runs from the outermost to the innermost.
    assert_eq!(decls[0].name.to_string(), "a");
    assert_eq!(decls[1].name.to_string(), "b");
    assert_eq!(decls[0].ty, prop());
    assert_ne!(decls[0].id, decls[1].id);
}

#[test]
fn a_constant_that_is_not_a_nat_constructor_has_no_shape() {
    // `nat_lit::shape` answers only for `Nat.zero` and `Nat.succ`.
    assert!(nat_lit::shape(&Expr::const_("Int.zero", vec![])).is_none());
    assert!(
        nat_lit::shape(&Expr::const_("Nat.succ", vec![])).is_none(),
        "no argument"
    );
    assert!(nat_lit::shape(&prop()).is_none());
    assert!(nat_lit::is_binop(&Name::from_dotted("Nat.add")));
    assert!(!nat_lit::is_binop(&Name::from_dotted("Nat.frobnicate")));
    assert!(nat_lit::returns_bool(&Name::from_dotted("Nat.ble")));
    assert!(!nat_lit::returns_bool(&Name::from_dotted("Nat.add")));
    assert_eq!(nat_lit::lit(5).pretty(), "5");
    assert!(nat_lit::to_ctor_if_lit(&prop()).is_none());
}

#[test]
fn an_instance_binder_prints_square_brackets() {
    // The fourth `BinderInfo`. Each of the four has its own bracket pair.
    assert_eq!(BinderInfo::Default.brackets(), ("(", ")"));
    assert_eq!(BinderInfo::Implicit.brackets(), ("{", "}"));
    assert_eq!(BinderInfo::StrictImplicit.brackets(), ("⦃", "⦄"));
    assert_eq!(BinderInfo::InstImplicit.brackets(), ("[", "]"));
    let term = Expr::Forall {
        binder_name: Name::from_dotted("inst"),
        binder_type: Arc::new(Expr::const_("Add", vec![])),
        body: Arc::new(Expr::bvar(0)),
        info: BinderInfo::InstImplicit,
    };
    assert_eq!(term.pretty(), "[inst : Add] → inst");
}

#[test]
fn the_printer_brackets_a_nested_shape() {
    let nat = Expr::const_("Nat", vec![]);
    // A lambda as an argument needs brackets.
    let id = Expr::lam("x", nat.clone(), Expr::bvar(0));
    assert_eq!(
        nat.clone().app(id.clone()).pretty(),
        "Nat (fun (x : Nat) => x)"
    );
    // A lambda on the left of an arrow needs brackets too.
    assert_eq!(
        Expr::arrow(id.clone(), nat.clone()).pretty(),
        "(fun (x : Nat) => x) → Nat"
    );
    // A let as an argument.
    let bound = Expr::let_("y", nat.clone(), nat.clone(), Expr::bvar(0));
    assert!(
        bound
            .clone()
            .app(nat.clone())
            .pretty()
            .starts_with("(let y")
    );
    // An arrow on the left of an arrow.
    let arrow = Expr::arrow(nat.clone(), nat.clone());
    assert_eq!(Expr::arrow(arrow, nat).pretty(), "(Nat → Nat) → Nat");
}

#[test]
fn the_inductive_lookups_refuse_a_name_of_the_wrong_kind() {
    let mut env = Environment::new();
    // A constructor whose `induct` points at something that is not inductive.
    env.add(Declaration::Axiom(AxiomVal {
        name: Name::from_dotted("NotInductive"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        is_unsafe: false,
    }));
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("c"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        induct: Name::from_dotted("NotInductive"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    }));
    assert!(env.inductive_of_ctor(&Name::from_dotted("c")).is_none());

    // An inductive whose sole constructor name is not a constructor.
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("I"),
        level_params: Vec::new(),
        ty: Expr::type_(0),
        num_params: 0,
        num_indices: 0,
        all: Vec::new(),
        ctors: vec![Name::from_dotted("NotInductive")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    assert!(env.sole_ctor(&Name::from_dotted("I")).is_none());
}

#[test]
fn a_sort_or_a_literal_can_head_a_spine() {
    // An ill formed term still has to get a yes or a no, not a crash. A loose
    // bound variable keeps proof irrelevance out of the way, because a loose
    // variable has no type.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    let id = Expr::lam("x", Expr::type_(0), Expr::bvar(0));
    // Two sorts that match, with an argument that needs one beta step.
    let left = prop().app(Expr::bvar(0));
    let right = prop().app(id.clone().app(Expr::bvar(0)));
    assert!(tc.is_def_eq(&left, &right).unwrap());
    // Two sorts that do not match.
    assert!(
        !tc.is_def_eq(&left, &Expr::type_(0).app(Expr::bvar(0)))
            .unwrap()
    );
    // Two literals that match, and two that do not.
    let lit_left = Expr::nat("1").app(Expr::bvar(0));
    let lit_right = Expr::nat("1").app(id.app(Expr::bvar(0)));
    assert!(tc.is_def_eq(&lit_left, &lit_right).unwrap());
    assert!(
        !tc.is_def_eq(&lit_left, &Expr::nat("2").app(Expr::bvar(0)))
            .unwrap()
    );
}

#[test]
fn a_later_field_can_mention_an_earlier_one() {
    // `Sig` has two fields, and the type of the second mentions the first.
    //
    // ```text
    // Sig.mk : (A : Type) → (B : A → Type) → (fst : A) → B fst → Sig A B
    // ```
    //
    // So the type of `.2` is `B p.1`, and `infer_proj` has to substitute a
    // projection for each earlier field to build it.
    let mut env = Environment::new();
    let one = Level::of_nat(1);
    let sig = |a: Expr, b: Expr| Expr::const_("Sig", vec![one.clone()]).apps([a, b]);
    env.add(Declaration::Inductive(InductiveVal {
        name: Name::from_dotted("Sig"),
        level_params: vec![Name::from_dotted("u")],
        ty: Expr::type_(1),
        num_params: 2,
        num_indices: 0,
        all: vec![Name::from_dotted("Sig")],
        ctors: vec![Name::from_dotted("Sig.mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    // (A : Type) → (B : A → Type) → (fst : A) → (snd : B fst) → Sig A B
    let ctor_type = Expr::forall(
        "A",
        Expr::type_(0),
        Expr::forall(
            "B",
            Expr::arrow(Expr::bvar(0), Expr::type_(0)),
            Expr::forall(
                "fst",
                Expr::bvar(1),
                Expr::forall(
                    "snd",
                    Expr::bvar(1).app(Expr::bvar(0)),
                    sig(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
        ),
    );
    env.add(Declaration::Constructor(ConstructorVal {
        name: Name::from_dotted("Sig.mk"),
        level_params: vec![Name::from_dotted("u")],
        ty: ctor_type,
        induct: Name::from_dotted("Sig"),
        cidx: 0,
        num_params: 2,
        num_fields: 2,
        is_unsafe: false,
    }));

    let mut tc = TypeChecker::new(&env);
    let a = Expr::FVar(tc.push_local("A", Expr::type_(0)));
    let b = Expr::FVar(tc.push_local("B", Expr::arrow(a.clone(), Expr::type_(0))));
    let p = Expr::FVar(tc.push_local("p", sig(a.clone(), b.clone())));
    let field = |index: u32| {
        Expr::Proj(Proj {
            structure: Name::from_dotted("Sig"),
            index,
            value: Arc::new(p.clone()),
        })
    };
    // The first field has the type `A`.
    let first = tc.infer_type(&field(0)).expect("field 0 must have a type");
    assert_eq!(tc.lctx().pretty(&first), "A");
    // The second field has the type `B p.1`, which mentions the first field.
    let second = tc.infer_type(&field(1)).expect("field 1 must have a type");
    assert_eq!(tc.lctx().pretty(&second), "B p.1");
}
