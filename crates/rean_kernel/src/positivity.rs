//! The strict positivity check.
//!
//! An `inductive` declaration is the one place where a user hands the kernel a
//! new rule. If the kernel accepts any shape at all, the user can prove
//! `False`:
//!
//! ```text
//! inductive Bad | mk : (Bad → False) → Bad
//! ```
//!
//! That declaration says "a `Bad` is a function from `Bad` to `False`". Give it
//! to yourself and you get `False`, with no axiom and no mistake anywhere else.
//! The kernel must refuse it.
//!
//! # The rule
//!
//! Write the type of a constructor as a chain of binders:
//!
//! ```text
//! (p₁ : P₁) … (pₙ : Pₙ)   (f₁ : F₁) … (fₘ : Fₘ)   →   I p₁ … pₙ i₁ … i_k
//!  ^ the parameters         ^ the fields                ^ the result
//! ```
//!
//! Two conditions must hold:
//!
//! 1. The result is the inductive type itself, applied to arguments.
//! 2. The inductive type occurs **strictly positively** in every field type.
//!
//! A name occurs strictly positively in a field type `F` when you write `F` as
//! its own chain of binders:
//!
//! ```text
//! F  =  (x₁ : A₁) → … → (x_j : A_j) → B
//! ```
//!
//! - No `A` may mention the name at all. That is the strict part.
//! - `B` may mention the name only as the head of an application, and the
//!   arguments of that head must not mention it either.
//!
//! So `Nat → I` is fine, because `I` is only the result. `I → Nat` is not,
//! because `I` sits in a domain.
//!
//! # The limit
//!
//! A **nested** inductive puts its own type inside another type constructor,
//! such as `inductive Tree | node : List Tree → Tree`. Lean compiles that into
//! an auxiliary declaration, and the export format records the depth in
//! `num_nested`.
//!
//! The strict rule above would refuse `List Tree → Tree`, because `Tree` is an
//! argument of `List` and not the head. So a nested declaration gets a
//! **weaker** rule, [`no_negative_occurrence`]: the inductive type may appear
//! anywhere in the result, and still nowhere in a domain.
//!
//! That is weaker than Lean in two ways, and both are honest limits rather
//! than hidden ones:
//!
//! 1. It does not understand the auxiliary form that Lean builds, so it checks
//!    the declaration as written.
//! 2. The check reads a shape, so it only ever sees the shape it is given.
//!    `TypeChecker::check_positivity` reduces the binders of a constructor
//!    type first, which is what stops an abbreviation from hiding an
//!    occurrence. It does not reduce the **arguments** of an application, so
//!    an occurrence inside `List (Bad Tree)` is refused rather than read.
//!
//! It still refuses `(Tree → False) → Tree`, which is the shape that proves
//! `False` directly. Refusing that is worth more than skipping everything.

use crate::expr::Expr;
use rean_core::Name;

/// Returns `true` if any name in `names` occurs anywhere in `e`.
pub fn occurs(e: &Expr, names: &[Name]) -> bool {
    match e {
        Expr::Const { name, .. } => names.contains(name),
        Expr::App { fun, arg } => occurs(fun, names) || occurs(arg, names),
        Expr::Lam {
            binder_type, body, ..
        }
        | Expr::Forall {
            binder_type, body, ..
        } => occurs(binder_type, names) || occurs(body, names),
        Expr::Let {
            binder_type,
            value,
            body,
            ..
        } => occurs(binder_type, names) || occurs(value, names) || occurs(body, names),
        Expr::Proj(proj) => names.contains(&proj.structure) || occurs(&proj.value, names),
        Expr::BVar(_) | Expr::FVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Lit(_) => false,
    }
}

/// Returns `true` if every name in `names` occurs strictly positively in `e`.
///
/// Call this on the type of one field of one constructor.
pub fn strictly_positive(e: &Expr, names: &[Name]) -> bool {
    // Walk the chain of binders. No domain may mention the inductive type.
    let mut current = e;
    while let Expr::Forall {
        binder_type, body, ..
    } = current
    {
        if occurs(binder_type, names) {
            return false;
        }
        current = body;
    }

    // The result may use the inductive type as the head of an application, and
    // nowhere else.
    let (head, args) = current.unfold_apps();
    if args.iter().any(|arg| occurs(arg, names)) {
        return false;
    }
    match head {
        // A constant head is always acceptable. Either it is the inductive
        // type, which is the one allowed position, or it is unrelated.
        Expr::Const { .. } => true,
        // Any other head, such as a lambda left by a redex, must not mention
        // the inductive type at all.
        other => !occurs(other, names),
    }
}

/// Returns `true` if no name in `names` sits in a domain position in `e`.
///
/// This is the weaker rule, for a nested inductive declaration. Read `e` as a
/// chain of binders. No domain may mention the name. The result may.
pub fn no_negative_occurrence(e: &Expr, names: &[Name]) -> bool {
    let mut current = e;
    while let Expr::Forall {
        binder_type, body, ..
    } = current
    {
        if occurs(binder_type, names) {
            return false;
        }
        current = body;
    }
    true
}

/// Why a constructor type is not acceptable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PositivityError {
    /// A field type uses the inductive type in a position that is not strictly
    /// positive. This is the case that lets a user prove `False`.
    NotStrictlyPositive { field: u32 },
    /// The chain of binders is shorter than the parameter and field counts say.
    TooFewBinders { expected: u32 },
    /// The constructor does not return the inductive type that owns it.
    WrongResult,
}

/// Checks the type of one constructor.
///
/// - `ty` is the type of the constructor.
/// - `num_params` and `num_fields` come from the constructor declaration.
/// - `names` is the mutual group of the inductive type that owns it.
pub fn check_constructor(
    ty: &Expr,
    num_params: u32,
    num_fields: u32,
    names: &[Name],
) -> Result<(), PositivityError> {
    check_constructor_with(ty, num_params, num_fields, names, strictly_positive)
}

/// Checks the type of one constructor of a **nested** inductive declaration.
///
/// Uses [`no_negative_occurrence`] in place of [`strictly_positive`]. See the
/// module documentation for what that gives up.
pub fn check_nested_constructor(
    ty: &Expr,
    num_params: u32,
    num_fields: u32,
    names: &[Name],
) -> Result<(), PositivityError> {
    check_constructor_with(ty, num_params, num_fields, names, no_negative_occurrence)
}

fn check_constructor_with(
    ty: &Expr,
    num_params: u32,
    num_fields: u32,
    names: &[Name],
    acceptable: fn(&Expr, &[Name]) -> bool,
) -> Result<(), PositivityError> {
    let mut current = ty;

    // A parameter is fixed across every constructor, so it needs no check.
    for _ in 0..num_params {
        let Expr::Forall { body, .. } = current else {
            return Err(PositivityError::TooFewBinders {
                expected: num_params + num_fields,
            });
        };
        current = body;
    }

    // Every field type must use the inductive type strictly positively.
    for field in 0..num_fields {
        let Expr::Forall {
            binder_type, body, ..
        } = current
        else {
            return Err(PositivityError::TooFewBinders {
                expected: num_params + num_fields,
            });
        };
        if !acceptable(binder_type, names) {
            return Err(PositivityError::NotStrictlyPositive { field });
        }
        current = body;
    }

    // The result must be the inductive type.
    let (head, _) = current.unfold_apps();
    match head {
        Expr::Const { name, .. } if names.contains(name) => Ok(()),
        _ => Err(PositivityError::WrongResult),
    }
}

#[cfg(test)]
mod tests {
    use super::{PositivityError, check_constructor, occurs, strictly_positive};
    use crate::expr::Expr;
    use rean_core::Name;

    fn group() -> Vec<Name> {
        vec![Name::from_dotted("I")]
    }

    fn i() -> Expr {
        Expr::const_("I", vec![])
    }

    fn nat() -> Expr {
        Expr::const_("Nat", vec![])
    }

    #[test]
    fn occurs_finds_a_name_anywhere() {
        assert!(occurs(&i(), &group()));
        assert!(occurs(&Expr::arrow(nat(), i()), &group()));
        assert!(occurs(&Expr::lam("x", i(), nat()), &group()));
        assert!(!occurs(&Expr::arrow(nat(), nat()), &group()));
        assert!(!occurs(&Expr::prop(), &group()));
    }

    #[test]
    fn a_bare_occurrence_is_positive() {
        // A field of type `I`, as in `Nat.succ : Nat → Nat`.
        assert!(strictly_positive(&i(), &group()));
    }

    #[test]
    fn a_result_position_is_positive() {
        // `Nat → I`, as in a reflexive inductive type.
        assert!(strictly_positive(&Expr::arrow(nat(), i()), &group()));
    }

    #[test]
    fn a_domain_position_is_not_positive() {
        // `I → Nat`. This is the shape that lets a user prove `False`.
        assert!(!strictly_positive(&Expr::arrow(i(), nat()), &group()));
    }

    #[test]
    fn an_argument_of_the_result_is_not_positive() {
        // `F I`, where `I` is an argument and not the head.
        let f = Expr::const_("F", vec![]);
        assert!(!strictly_positive(&f.app(i()), &group()));
    }

    #[test]
    fn an_unrelated_type_is_positive() {
        assert!(strictly_positive(&Expr::arrow(nat(), nat()), &group()));
    }

    #[test]
    fn the_successor_of_nat_is_accepted() {
        // `Nat.succ : Nat → Nat`, with 0 parameters and 1 field.
        let names = vec![Name::from_dotted("Nat")];
        assert_eq!(
            check_constructor(&Expr::arrow(nat(), nat()), 0, 1, &names),
            Ok(())
        );
    }

    #[test]
    fn the_bad_inductive_is_rejected() {
        // `Bad.mk : (Bad → False) → Bad`
        let bad = Expr::const_("Bad", vec![]);
        let names = vec![Name::from_dotted("Bad")];
        let field = Expr::arrow(bad.clone(), Expr::const_("False", vec![]));
        assert_eq!(
            check_constructor(&Expr::arrow(field, bad), 0, 1, &names),
            Err(PositivityError::NotStrictlyPositive { field: 0 })
        );
    }

    #[test]
    fn a_reflexive_inductive_is_accepted() {
        // `Good.mk : (Nat → Good) → Good`
        let good = Expr::const_("Good", vec![]);
        let names = vec![Name::from_dotted("Good")];
        let field = Expr::arrow(nat(), good.clone());
        assert_eq!(
            check_constructor(&Expr::arrow(field, good), 0, 1, &names),
            Ok(())
        );
    }

    #[test]
    fn a_constructor_that_returns_the_wrong_type_is_rejected() {
        let names = vec![Name::from_dotted("I")];
        assert_eq!(
            check_constructor(&Expr::arrow(nat(), nat()), 0, 1, &names),
            Err(PositivityError::WrongResult)
        );
    }

    #[test]
    fn too_few_binders_is_rejected() {
        let names = vec![Name::from_dotted("I")];
        assert_eq!(
            check_constructor(&i(), 0, 1, &names),
            Err(PositivityError::TooFewBinders { expected: 1 })
        );
    }
}
