//! The four quotient declarations, and the type the kernel fixes for each one.
//!
//! `Quot` is a primitive. You cannot write it as an `inductive` declaration,
//! because its whole point is a rule that no inductive type has: two terms
//! that a relation relates become **one** term. So the kernel carries the four
//! declarations itself, and [`TypeChecker::quot_step`][step] carries the rule
//! that computes with them.
//!
//! | declaration | what it is |
//! |---|---|
//! | `Quot` | the type. `Quot r` is `α` with `r` collapsed |
//! | `Quot.mk` | the constructor. It puts an `α` into the quotient |
//! | `Quot.lift` | the eliminator. A function that respects `r` becomes a function on the quotient |
//! | `Quot.ind` | the same for a proof |
//!
//! `Quot.sound`, the axiom that says `Quot.mk a` and `Quot.mk b` are equal
//! when `r a b` holds, is an `axiom` in an export and not one of these four.
//! It is the one part of the quotient that asks to be trusted, so it belongs
//! in the trust report. See [`Environment::axioms_of`][axioms].
//!
//! # Why the kernel may not take these types as given
//!
//! An export is a file, and a file can say anything. `quot_step` fires on any
//! declaration whose kind is `lift` or `ind`, and it rewrites
//! `Quot.lift f h (Quot.mk r a)` to `f a` **without checking the result**,
//! exactly as the ι rule does for a recursor. A rewrite that is trusted must
//! be a rewrite that preserves the type, and that holds for these four types
//! and for no others.
//!
//! So a `quot` declaration with a type of its own is an untracked axiom, which
//! is the same hole that chapter 13 closed for a forged recursor and chapter
//! 28 closed for an orphan constructor. `Quot.lift : False` is three lines of
//! a file, it proves `False`, and no axiom appears in the report.
//!
//! The real Lean kernel never faces the question: `addQuot` **builds** these
//! four declarations from nothing, so the file cannot reach them. We read a
//! file, so we check instead. [`declared_type`] holds the four types, and
//! [`TypeChecker::check_quot`][check] compares.
//!
//! [step]: crate::TypeChecker::quot_step
//! [check]: crate::TypeChecker::check_quot
//! [axioms]: crate::Environment::axioms_of

use crate::environment::QuotKind;
use crate::expr::Expr;
use crate::level::Level;
use rean_core::Name;

/// The name that Lean gives this declaration.
pub fn name_of(kind: QuotKind) -> &'static str {
    match kind {
        QuotKind::Type => "Quot",
        QuotKind::Ctor => "Quot.mk",
        QuotKind::Lift => "Quot.lift",
        QuotKind::Ind => "Quot.ind",
    }
}

/// How many universe parameters this declaration takes.
///
/// `Quot.lift` takes two, because the function it lifts may land in a universe
/// of its own. The other three take one.
pub fn level_arity(kind: QuotKind) -> usize {
    match kind {
        QuotKind::Lift => 2,
        _ => 1,
    }
}

/// The type that Lean fixes for one of the four quotient declarations.
///
/// `levels` holds the universe parameters of the declaration under check, in
/// the order it lists them, so that the answer can be compared with the type
/// the file gave. It returns `None` when the count is wrong.
///
/// # Reading the code below
///
/// A bound variable is a **number**: how many binders stand between the use
/// and the binder that owns it. So the same variable is a different number
/// further in, and `α` is `bvar(0)` right under its own binder and `bvar(3)`
/// three binders later. The comment on each line names what each number is.
///
/// [`Expr::arrow`] builds `A → B` and lifts `B` by one on its own, so both
/// halves of an arrow are written at the depth **outside** it.
pub fn declared_type(kind: QuotKind, levels: &[Name]) -> Option<Expr> {
    if levels.len() != level_arity(kind) {
        return None;
    }
    let u = Level::Param(levels[0].clone());
    let sort_u = || Expr::sort(u.clone());
    let quot = |alpha: u32, r: u32| {
        Expr::const_("Quot", vec![u.clone()]).apps([Expr::bvar(alpha), Expr::bvar(r)])
    };
    // `α → α → Prop`, written one binder inside `α`.
    let relation = || Expr::arrow(Expr::bvar(0), Expr::arrow(Expr::bvar(0), Expr::prop()));

    Some(match kind {
        // {α : Sort u} → (α → α → Prop) → Sort u
        QuotKind::Type => Expr::forall("α", sort_u(), Expr::arrow(relation(), sort_u())),

        // {α : Sort u} → (r : α → α → Prop) → α → Quot α r
        QuotKind::Ctor => Expr::forall(
            "α",
            sort_u(),
            Expr::forall(
                "r",
                relation(),
                // α is 1 and r is 0.
                Expr::arrow(Expr::bvar(1), quot(1, 0)),
            ),
        ),

        // {α : Sort u} → {r : α → α → Prop} → {β : Quot α r → Prop} →
        //   ((a : α) → β (Quot.mk α r a)) → (q : Quot α r) → β q
        QuotKind::Ind => Expr::forall(
            "α",
            sort_u(),
            Expr::forall(
                "r",
                relation(),
                Expr::forall(
                    "β",
                    // α is 1 and r is 0.
                    Expr::arrow(quot(1, 0), Expr::prop()),
                    Expr::forall(
                        "f",
                        // α is 2, r is 1 and β is 0. Under the `a` binder each
                        // one is one deeper, and `a` itself is 0.
                        Expr::forall(
                            "a",
                            Expr::bvar(2),
                            Expr::bvar(1).app(Expr::const_("Quot.mk", vec![u.clone()]).apps([
                                Expr::bvar(3),
                                Expr::bvar(2),
                                Expr::bvar(0),
                            ])),
                        ),
                        // α is 3, r is 2 and β is 1. Under the `q` binder β is
                        // 2 and `q` is 0.
                        Expr::forall("q", quot(3, 2), Expr::bvar(2).app(Expr::bvar(0))),
                    ),
                ),
            ),
        ),

        // {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) →
        //   ((a b : α) → r a b → f a = f b) → Quot α r → β
        QuotKind::Lift => {
            let v = Level::Param(levels[1].clone());
            // Under `a` and `b`: α is 5, r is 4, β is 3, f is 2, a is 1, b is 0.
            let respects = Expr::forall(
                "a",
                Expr::bvar(3),
                Expr::forall(
                    "b",
                    Expr::bvar(4),
                    Expr::arrow(
                        Expr::bvar(4).apps([Expr::bvar(1), Expr::bvar(0)]),
                        Expr::const_("Eq", vec![v.clone()]).apps([
                            Expr::bvar(3),
                            Expr::bvar(2).app(Expr::bvar(1)),
                            Expr::bvar(2).app(Expr::bvar(0)),
                        ]),
                    ),
                ),
            );
            Expr::forall(
                "α",
                sort_u(),
                Expr::forall(
                    "r",
                    relation(),
                    Expr::forall(
                        "β",
                        Expr::sort(v),
                        Expr::forall(
                            "f",
                            // α is 2 and β is 0.
                            Expr::arrow(Expr::bvar(2), Expr::bvar(0)),
                            // α is 3, r is 2, β is 1 and f is 0.
                            Expr::arrow(respects, Expr::arrow(quot(3, 2), Expr::bvar(1))),
                        ),
                    ),
                ),
            )
        }
    })
}
