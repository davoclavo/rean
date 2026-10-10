//! The type checker.
//!
//! This module holds the three functions that chapter 0, section 0.13 named:
//!
//! - [`infer_type`] applies the type rules and returns the type of a term.
//! - [`is_def_eq`] decides whether two terms are the same by computation.
//! - [`whnf`] reduces a term until its head is stable.
//!
//! The three call each other. [`infer_type`] needs [`whnf`], because the
//! application rule wants a function type. [`infer_type`] needs [`is_def_eq`],
//! to accept an argument whose type matches only after a reduction.
//! [`is_def_eq`] needs [`whnf`], because you cannot compare two terms without
//! a reduction first.
//!
//! # What this version does not do
//!
//! The checker is honest about its limits, and each limit has one cause.
//!
//! | Missing | Cause |
//! |---|---|
//! | the δ rule | there is no `Environment`, so no constant has a value |
//! | the ι rule | there is no inductive declaration, so there is no recursor |
//! | the η rule | not written yet |
//! | proof irrelevance | not written yet |
//! | level normalization | [`Level::is_equiv`] compares open levels by shape |
//!
//! So [`infer_type`] returns an error for [`Expr::Const`], [`Expr::Lit`], and
//! [`Expr::Proj`]. Chapter 2 adds the environment and removes those three
//! errors.
//!
//! What is left is enough to check every proof of implicational logic: the
//! identity, composition, the K combinator, and the S combinator.
//!
//! [`Level::is_equiv`]: crate::Level::is_equiv

use crate::expr::{Expr, FVarId, MVarId};
use crate::local::LocalContext;
use rean_core::Name;
use std::fmt;
use std::sync::Arc;

/// Why a term failed to check.
///
/// The three variants that carry a term carry it in a [`Box`]. The reason is
/// size, not style. [`infer_type`] returns a `Result` for every node of the
/// term, so the error sits in the return value of the hot path. An `Expr` is
/// about 64 bytes, and [`TypeError::TypeMismatch`] holds three of them. Without
/// the boxes, every recursive call would carry 200 bytes for a case that almost
/// never happens.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TypeError {
    /// A bound variable pointed outside the term. The caller must open every
    /// binder with [`LocalContext::with_binder`] first.
    LooseBVar(u32),
    /// A free variable was not in the local context.
    UnknownFVar(FVarId),
    /// A metavariable survived into the kernel. The elaborator must solve it.
    MetavariableLeft(MVarId),
    /// A constant has no declaration, because there is no environment yet.
    UnknownConstant(Name),
    /// A term form needs the environment that chapter 2 adds.
    NeedsEnvironment { what: &'static str },
    /// A term stood where a type was wanted.
    NotAType { term: Box<Expr>, got: Box<Expr> },
    /// A term stood in the function position and it is not a function.
    NotAFunction { term: Box<Expr>, got: Box<Expr> },
    /// A term has the wrong type for its place.
    TypeMismatch {
        term: Box<Expr>,
        expected: Box<Expr>,
        got: Box<Expr>,
    },
}

impl TypeError {
    /// Builds a [`TypeError::NotAType`].
    fn not_a_type(term: &Expr, got: Expr) -> Self {
        TypeError::NotAType {
            term: Box::new(term.clone()),
            got: Box::new(got),
        }
    }

    /// Builds a [`TypeError::NotAFunction`].
    fn not_a_function(term: &Expr, got: Expr) -> Self {
        TypeError::NotAFunction {
            term: Box::new(term.clone()),
            got: Box::new(got),
        }
    }

    /// Builds a [`TypeError::TypeMismatch`].
    fn mismatch(term: &Expr, expected: Expr, got: Expr) -> Self {
        TypeError::TypeMismatch {
            term: Box::new(term.clone()),
            expected: Box::new(expected),
            got: Box::new(got),
        }
    }

    /// Renders the error and names every free variable that `ctx` holds.
    ///
    /// Use this method, not [`fmt::Display`]. A message that says `_f0` helps
    /// nobody.
    pub fn render(&self, ctx: &LocalContext) -> String {
        self.describe(&|e| ctx.pretty(e))
    }

    /// Renders the error with `show` as the term printer.
    fn describe(&self, show: &dyn Fn(&Expr) -> String) -> String {
        match self {
            TypeError::LooseBVar(index) => {
                format!("the bound variable #{index} points outside the term")
            }
            TypeError::UnknownFVar(id) => {
                format!("the free variable _f{} is not in scope", id.0)
            }
            TypeError::MetavariableLeft(id) => {
                format!("the metavariable ?m{} is not solved", id.0)
            }
            TypeError::UnknownConstant(name) => format!(
                "unknown constant `{name}`. There is no environment yet, so no \
                 constant has a declaration. See chapter 2."
            ),
            TypeError::NeedsEnvironment { what } => {
                format!("{what} needs an environment. See chapter 2.")
            }
            TypeError::NotAType { term, got } => format!(
                "expected a type, but `{}` has type `{}`",
                show(term),
                show(got)
            ),
            TypeError::NotAFunction { term, got } => format!(
                "`{}` is not a function. Its type is `{}`",
                show(term),
                show(got)
            ),
            TypeError::TypeMismatch {
                term,
                expected,
                got,
            } => format!(
                "type mismatch for `{}`\n  expected: {}\n  got     : {}",
                show(term),
                show(expected),
                show(got)
            ),
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.describe(&|e| e.pretty()))
    }
}

impl std::error::Error for TypeError {}

/// The result of a check.
pub type TypeResult<T> = Result<T, TypeError>;

// --- reduction -------------------------------------------------------------

/// Reduces `e` until the head is stable.
///
/// The name is short for weak head normal form. "Weak" means that the function
/// does not look inside a binder. "Head" means that it only reduces the
/// outermost shape, and leaves the arguments alone.
///
/// This version uses two of the five equations: β and ζ. See the limits in the
/// module documentation.
pub fn whnf(e: &Expr) -> Expr {
    let mut current = e.clone();
    loop {
        // ζ: a `let` in the head position substitutes its value.
        let (head, args) = current.unfold_apps();
        if let Expr::Let { value, body, .. } = head {
            let reduced = body.instantiate(value);
            let args: Vec<Expr> = args.into_iter().cloned().collect();
            current = reduced.apps(args);
            continue;
        }
        // β: a lambda in the head position takes its first argument.
        if let Some(next) = current.beta_step() {
            current = next;
            continue;
        }
        return current;
    }
}

// --- definitional equality -------------------------------------------------

/// Returns `true` if `a` and `b` are the same term by computation.
///
/// The function tries the cheap test first, then reduces, then compares the
/// parts. A real kernel adds the δ, ι, and η equations plus proof irrelevance.
/// See the limits in the module documentation.
pub fn is_def_eq(a: &Expr, b: &Expr) -> bool {
    // The cheap test. Most comparisons stop here.
    if a.alpha_eq(b) {
        return true;
    }
    let a = whnf(a);
    let b = whnf(b);
    if a.alpha_eq(&b) {
        return true;
    }
    match (&a, &b) {
        (Expr::App { .. }, Expr::App { .. }) => {
            // Compare the spine. `f x y` matches `g a b` only when the heads
            // match and every argument matches.
            let (head_a, args_a) = a.unfold_apps();
            let (head_b, args_b) = b.unfold_apps();
            args_a.len() == args_b.len()
                && is_def_eq(head_a, head_b)
                && args_a.iter().zip(&args_b).all(|(x, y)| is_def_eq(x, y))
        }
        (
            Expr::Lam {
                binder_type: t1,
                body: b1,
                info: i1,
                ..
            },
            Expr::Lam {
                binder_type: t2,
                body: b2,
                info: i2,
                ..
            },
        )
        | (
            Expr::Forall {
                binder_type: t1,
                body: b1,
                info: i1,
                ..
            },
            Expr::Forall {
                binder_type: t2,
                body: b2,
                info: i2,
                ..
            },
        ) => {
            // Both bodies sit under one binder each, so the two index spaces
            // line up. No renumber is needed here.
            i1 == i2 && is_def_eq(t1, t2) && is_def_eq(b1, b2)
        }
        _ => false,
    }
}

// --- the type rules --------------------------------------------------------

/// Returns the type of `e` in the context `ctx`.
///
/// Each arm of the `match` is one rule of chapter 0, section 0.6.
pub fn infer_type(ctx: &mut LocalContext, e: &Expr) -> TypeResult<Expr> {
    match e {
        // A bound variable must not reach this function. The caller opens
        // every binder into a free variable first.
        Expr::BVar(index) => Err(TypeError::LooseBVar(*index)),

        // The variable rule. The context gives the type.
        Expr::FVar(id) => ctx.type_of(*id).cloned().ok_or(TypeError::UnknownFVar(*id)),

        Expr::MVar(id) => Err(TypeError::MetavariableLeft(*id)),

        // The sort rule. `Sort u : Sort (u+1)`.
        Expr::Sort(level) => Ok(Expr::Sort(level.succ())),

        // These three need a declaration, and there is no environment yet.
        Expr::Const { name, .. } => Err(TypeError::UnknownConstant(name.clone())),
        Expr::Lit(_) => Err(TypeError::NeedsEnvironment { what: "a literal" }),
        Expr::Proj(_) => Err(TypeError::NeedsEnvironment {
            what: "a projection",
        }),

        // The function type rule. The level is `imax u v`, and that single
        // choice is what makes `Prop` impredicative.
        Expr::Forall {
            binder_name,
            binder_type,
            body,
            ..
        } => {
            let u = infer_sort(ctx, binder_type)?;
            let v = ctx.with_binder(binder_name.clone(), (**binder_type).clone(), |ctx, id| {
                let opened = body.instantiate(&Expr::FVar(id));
                infer_sort(ctx, &opened)
            })?;
            Ok(Expr::Sort(u.imax(&v)))
        }

        // The function rule. Open the binder, infer the body, close it again.
        Expr::Lam {
            binder_name,
            binder_type,
            body,
            info,
        } => {
            // The binder type must be a type. The level itself is not needed.
            infer_sort(ctx, binder_type)?;
            let body_type =
                ctx.with_binder(binder_name.clone(), (**binder_type).clone(), |ctx, id| {
                    let opened = body.instantiate(&Expr::FVar(id));
                    infer_type(ctx, &opened).map(|ty| ty.abstract_fvar(id))
                })?;
            Ok(Expr::Forall {
                binder_name: binder_name.clone(),
                binder_type: binder_type.clone(),
                body: Arc::new(body_type),
                info: *info,
            })
        }

        // The application rule. This arm is the only one that substitutes.
        Expr::App { fun, arg } => {
            let fun_type = infer_type(ctx, fun)?;
            let Expr::Forall {
                binder_type, body, ..
            } = whnf(&fun_type)
            else {
                return Err(TypeError::not_a_function(fun, fun_type));
            };
            let arg_type = infer_type(ctx, arg)?;
            if !is_def_eq(&arg_type, &binder_type) {
                return Err(TypeError::mismatch(arg, (*binder_type).clone(), arg_type));
            }
            // The type of the result depends on the argument value.
            Ok(body.instantiate(arg))
        }

        // The let rule. The ζ equation substitutes the value into the body.
        Expr::Let {
            binder_type,
            value,
            body,
            ..
        } => {
            infer_sort(ctx, binder_type)?;
            let value_type = infer_type(ctx, value)?;
            if !is_def_eq(&value_type, binder_type) {
                return Err(TypeError::mismatch(
                    value,
                    (**binder_type).clone(),
                    value_type,
                ));
            }
            let opened = body.instantiate(value);
            infer_type(ctx, &opened)
        }
    }
}

/// Returns the level of `e`, and fails if `e` is not a type.
///
/// Three rules need this helper. A binder type must be a type, and the body of
/// a function type must be a type.
pub fn infer_sort(ctx: &mut LocalContext, e: &Expr) -> TypeResult<crate::Level> {
    let ty = infer_type(ctx, e)?;
    match whnf(&ty) {
        Expr::Sort(level) => Ok(level),
        got => Err(TypeError::not_a_type(e, got)),
    }
}

/// Checks that `e` has the type `expected`.
///
/// This is the entry point of a proof checker. Give it the proof and the
/// proposition, and it answers yes or no.
pub fn check(ctx: &mut LocalContext, e: &Expr, expected: &Expr) -> TypeResult<()> {
    // The expected type must itself be a type. A proof of a non type is
    // meaningless.
    infer_sort(ctx, expected)?;
    let got = infer_type(ctx, e)?;
    if is_def_eq(&got, expected) {
        return Ok(());
    }
    Err(TypeError::mismatch(e, expected.clone(), got))
}

/// Checks a closed term against a closed type, with an empty context.
pub fn check_closed(e: &Expr, expected: &Expr) -> TypeResult<()> {
    check(&mut LocalContext::new(), e, expected)
}
