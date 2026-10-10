//! The type checker.
//!
//! Chapter 1 had three free functions. Now they need an [`Environment`], and
//! they call each other, so they live on one struct. The real Lean kernel does
//! the same, for the same reason.
//!
//! - [`TypeChecker::infer_type`] applies the type rules.
//! - [`TypeChecker::is_def_eq`] decides whether two terms are the same by
//!   computation.
//! - [`TypeChecker::whnf`] reduces a term until its head is stable.
//!
//! # The five equations
//!
//! | Rule | Status | Where |
//! |---|---|---|
//! | β beta | done | [`Expr::beta_step`] |
//! | ζ zeta | done | a `let` in the head position |
//! | δ delta | done | a `Const` whose declaration has a value |
//! | ι iota | done | a recursor applied to a constructor |
//! | η eta | done | in [`TypeChecker::is_def_eq`] |
//!
//! Plus proof irrelevance, and projection of a constructor.
//!
//! # What is still missing
//!
//! | Missing | Effect |
//! |---|---|
//! | K-like ι reduction | `Eq.rec` does not reduce unless its major premise is already `Eq.refl` |
//! | the strict positivity check | a bad `inductive` is trusted, not rejected |
//! | recursor re-derivation | the recursor and its ι rules are trusted as given |
//! | a full level normal form | a hard pair of open levels can fail to match |

use crate::environment::{Declaration, Environment};
use crate::expr::{Expr, FVarId, Literal, MVarId, Proj};
use crate::level::Level;
use crate::local::LocalContext;
use rean_core::Name;
use std::fmt;
use std::sync::Arc;

/// The largest number of reduction steps that [`TypeChecker::whnf`] will take.
///
/// The theory says that reduction terminates. A corrupt input file does not
/// have to obey the theory, so the loop needs a bound.
const REDUCTION_LIMIT: u32 = 100_000;

/// Why a term failed to check.
///
/// The variants that carry a term carry it in a [`Box`]. The reason is size.
/// [`TypeChecker::infer_type`] returns a `Result` for every node of the term,
/// so the error sits in the return value of the hot path.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TypeError {
    /// A bound variable pointed outside the term.
    LooseBVar(u32),
    /// A free variable was not in the local context.
    UnknownFVar(FVarId),
    /// A metavariable survived into the kernel.
    MetavariableLeft(MVarId),
    /// A constant has no declaration in the environment.
    UnknownConstant(Name),
    /// A constant got the wrong number of universe arguments.
    LevelArity {
        name: Name,
        expected: usize,
        got: usize,
    },
    /// A term stood where a type was wanted.
    NotAType { term: Box<Expr>, got: Box<Expr> },
    /// A term stood in the function position and it is not a function.
    NotAFunction { term: Box<Expr>, got: Box<Expr> },
    /// A projection was applied to something that is not a one constructor
    /// inductive type.
    NotAStructure { term: Box<Expr>, got: Box<Expr> },
    /// A projection index is past the last field.
    BadProjection { structure: Name, index: u32 },
    /// A term has the wrong type for its place.
    TypeMismatch {
        term: Box<Expr>,
        expected: Box<Expr>,
        got: Box<Expr>,
    },
    /// Reduction did not stop. The input is probably corrupt.
    ReductionLimit,
}

impl TypeError {
    fn not_a_type(term: &Expr, got: Expr) -> Self {
        TypeError::NotAType {
            term: Box::new(term.clone()),
            got: Box::new(got),
        }
    }

    fn not_a_function(term: &Expr, got: Expr) -> Self {
        TypeError::NotAFunction {
            term: Box::new(term.clone()),
            got: Box::new(got),
        }
    }

    fn not_a_structure(term: &Expr, got: Expr) -> Self {
        TypeError::NotAStructure {
            term: Box::new(term.clone()),
            got: Box::new(got),
        }
    }

    fn mismatch(term: &Expr, expected: Expr, got: Expr) -> Self {
        TypeError::TypeMismatch {
            term: Box::new(term.clone()),
            expected: Box::new(expected),
            got: Box::new(got),
        }
    }

    /// Renders the error and names every free variable that `ctx` holds.
    pub fn render(&self, ctx: &LocalContext) -> String {
        self.describe(&|e| ctx.pretty(e))
    }

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
            TypeError::UnknownConstant(name) => {
                format!("unknown constant `{name}`")
            }
            TypeError::LevelArity {
                name,
                expected,
                got,
            } => format!("`{name}` takes {expected} universe arguments, but got {got}"),
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
            TypeError::NotAStructure { term, got } => format!(
                "`{}` is not a structure. Its type is `{}`",
                show(term),
                show(got)
            ),
            TypeError::BadProjection { structure, index } => {
                format!("`{structure}` has no field at position {index}")
            }
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
            TypeError::ReductionLimit => {
                format!("reduction did not stop after {REDUCTION_LIMIT} steps")
            }
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

/// A checker over one environment.
pub struct TypeChecker<'e> {
    env: &'e Environment,
    lctx: LocalContext,
}

impl<'e> TypeChecker<'e> {
    /// Builds a checker with an empty local context.
    pub fn new(env: &'e Environment) -> Self {
        TypeChecker {
            env,
            lctx: LocalContext::new(),
        }
    }

    /// Returns the environment.
    pub fn env(&self) -> &'e Environment {
        self.env
    }

    /// Returns the local context, for a message.
    pub fn lctx(&self) -> &LocalContext {
        &self.lctx
    }

    /// Adds a free variable to the local context and returns its identifier.
    pub fn push_local(&mut self, name: impl Into<Name>, ty: Expr) -> FVarId {
        self.lctx.push(name.into(), ty)
    }

    // --- reduction ------------------------------------------------------

    /// Reduces `e` until the head is stable.
    ///
    /// "Weak" means that the function does not look inside a binder. "Head"
    /// means that it only reduces the outermost shape.
    pub fn whnf(&mut self, e: &Expr) -> TypeResult<Expr> {
        let mut current = e.clone();
        for _ in 0..REDUCTION_LIMIT {
            if let Some(next) = self.whnf_step(&current)? {
                current = next;
                continue;
            }
            return Ok(current);
        }
        Err(TypeError::ReductionLimit)
    }

    /// Does one reduction step at the head, or returns `None` if none applies.
    fn whnf_step(&mut self, e: &Expr) -> TypeResult<Option<Expr>> {
        let (head, args) = e.unfold_apps();
        let args: Vec<Expr> = args.into_iter().cloned().collect();

        // ζ: a `let` in the head position substitutes its value.
        if let Expr::Let { value, body, .. } = head {
            return Ok(Some(body.instantiate(value).apps(args)));
        }

        // β: a lambda in the head position takes its first argument.
        if let Some(next) = e.beta_step() {
            return Ok(Some(next));
        }

        // A projection of a constructor application takes the field.
        if let Expr::Proj(proj) = head
            && let Some(field) = self.proj_step(proj)?
        {
            return Ok(Some(field.apps(args)));
        }

        if let Expr::Const { name, levels } = head {
            // ι: a recursor applied to a constructor rewrites to its rule.
            if let Some(next) = self.iota_step(name, levels, &args)? {
                return Ok(Some(next));
            }
            // δ: a definition unfolds to its value.
            if let Some(decl) = self.env.get(name)
                && let Some(value) = decl.unfoldable_value()
            {
                let value = value.instantiate_levels(decl.level_params(), levels);
                return Ok(Some(value.apps(args)));
            }
        }

        Ok(None)
    }

    /// Reduces a projection whose target is a constructor application.
    fn proj_step(&mut self, proj: &Proj) -> TypeResult<Option<Expr>> {
        let value = self.whnf(&proj.value)?;
        let (head, args) = value.unfold_apps();
        let Expr::Const { name, .. } = head else {
            return Ok(None);
        };
        let Some(Declaration::Constructor(ctor)) = self.env.get(name) else {
            return Ok(None);
        };
        // The fields come after the parameters.
        let slot = ctor.num_params as usize + proj.index as usize;
        Ok(args.get(slot).map(|field| (*field).clone()))
    }

    /// Applies the ι rule, if `name` is a recursor with enough arguments and
    /// its major premise reduces to a constructor application.
    ///
    /// The argument order of a recursor is fixed:
    ///
    /// ```text
    /// rec  <params>  <motives>  <minors>  <indices>  <major>
    /// ```
    fn iota_step(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> TypeResult<Option<Expr>> {
        let Some(Declaration::Recursor(rec)) = self.env.get(name) else {
            return Ok(None);
        };
        let rec = rec.clone();
        let major_index = rec.major_index();
        if args.len() <= major_index {
            return Ok(None);
        }

        let major = self.whnf(&args[major_index])?;
        let (major_head, major_args) = major.unfold_apps();
        let Expr::Const { name: ctor, .. } = major_head else {
            // A K-like recursor reduces even here. That case is not written yet.
            return Ok(None);
        };
        let Some(rule) = rec.rule_for(ctor) else {
            return Ok(None);
        };
        let fields = rule.num_fields as usize;
        if major_args.len() < fields {
            return Ok(None);
        }

        // The rule takes the universe arguments of the call site, then the
        // parameters, the motives and the minor premises, then the fields of
        // the constructor, then anything that followed the major premise.
        let mut out = rule.rhs.instantiate_levels(&rec.level_params, levels);
        out = out.apps(args[..rec.num_prefix()].iter().cloned());
        out = out.apps(
            major_args[major_args.len() - fields..]
                .iter()
                .map(|field| (*field).clone()),
        );
        out = out.apps(args[major_index + 1..].iter().cloned());
        Ok(Some(out))
    }

    // --- definitional equality ------------------------------------------

    /// Returns `true` if `a` and `b` are the same term by computation.
    pub fn is_def_eq(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        // The cheap test. Most comparisons stop here.
        if a.alpha_eq(b) {
            return Ok(true);
        }
        let a = self.whnf(a)?;
        let b = self.whnf(b)?;
        if a.alpha_eq(&b) {
            return Ok(true);
        }

        match (&a, &b) {
            (Expr::Sort(x), Expr::Sort(y)) => return Ok(x.is_equiv(y)),
            (Expr::Lit(x), Expr::Lit(y)) => return Ok(x == y),
            _ => {}
        }

        // Two lambdas, or two function types.
        if self.binders_eq(&a, &b)? {
            return Ok(true);
        }
        // Compare the application spine. The heads must match, and so must
        // every argument. A bare `Proj` is a spine with no argument, so this
        // call covers that case too.
        if self.spine_eq(&a, &b)? {
            return Ok(true);
        }
        // η: `fun x => f x` is the same function as `f`.
        if self.eta_eq(&a, &b)? || self.eta_eq(&b, &a)? {
            return Ok(true);
        }
        // Proof irrelevance: all proofs of one proposition are equal.
        self.proof_irrelevant(&a, &b)
    }

    /// Compares two lambdas, or two function types.
    ///
    /// Returns `false` when the two terms do not have the same binder shape.
    fn binders_eq(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        let (name, left_type, left_body, right_type, right_body) = match (a, b) {
            (
                Expr::Lam {
                    binder_name,
                    binder_type: t1,
                    body: b1,
                    ..
                },
                Expr::Lam {
                    binder_type: t2,
                    body: b2,
                    ..
                },
            )
            | (
                Expr::Forall {
                    binder_name,
                    binder_type: t1,
                    body: b1,
                    ..
                },
                Expr::Forall {
                    binder_type: t2,
                    body: b2,
                    ..
                },
            ) => (binder_name, t1, b1, t2, b2),
            _ => return Ok(false),
        };
        if !self.is_def_eq(left_type, right_type)? {
            return Ok(false);
        }
        // Open both bodies with ONE shared free variable, then compare.
        //
        // A direct comparison of the two bodies would also line up, because
        // both sit under one binder. But it would leave a loose bound variable
        // in each body, and then nothing inside the comparison could infer a
        // type. Proof irrelevance needs that.
        let id = self.lctx.push(name.clone(), (**left_type).clone());
        let left = left_body.instantiate(&Expr::FVar(id));
        let right = right_body.instantiate(&Expr::FVar(id));
        let same = self.is_def_eq(&left, &right);
        self.lctx.pop();
        same
    }

    /// Compares two application spines.
    fn spine_eq(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        let (head_a, args_a) = a.unfold_apps();
        let (head_b, args_b) = b.unfold_apps();
        if args_a.len() != args_b.len() {
            return Ok(false);
        }
        match (head_a, head_b) {
            (
                Expr::Const {
                    name: n1,
                    levels: l1,
                },
                Expr::Const {
                    name: n2,
                    levels: l2,
                },
            ) => {
                if n1 != n2
                    || l1.len() != l2.len()
                    || !l1.iter().zip(l2).all(|(x, y)| x.is_equiv(y))
                {
                    return Ok(false);
                }
            }
            (Expr::FVar(x), Expr::FVar(y)) if x == y => {}
            (Expr::BVar(x), Expr::BVar(y)) if x == y => {}
            (Expr::Sort(x), Expr::Sort(y)) => {
                if !x.is_equiv(y) {
                    return Ok(false);
                }
            }
            (Expr::Lit(x), Expr::Lit(y)) => {
                if x != y {
                    return Ok(false);
                }
            }
            // A projection can head a spine. `(Nat.brecOn ... m).1 n` is one,
            // and the compiled form of a recursive definition is full of them.
            // The target of the projection is strictly smaller than the whole
            // term, so this recursion ends.
            (Expr::Proj(p1), Expr::Proj(p2)) => {
                if p1.index != p2.index || !self.is_def_eq(&p1.value, &p2.value)? {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
        for (x, y) in args_a.iter().zip(&args_b) {
            if !self.is_def_eq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns `true` if `lam` is `fun x => f x` and `other` is `f`.
    fn eta_eq(&mut self, lam: &Expr, other: &Expr) -> TypeResult<bool> {
        let Expr::Lam { body, .. } = lam else {
            return Ok(false);
        };
        if matches!(other, Expr::Lam { .. }) {
            return Ok(false);
        }
        // Build `other x` under one new binder, then compare the bodies.
        let applied = other.lift(0, 1).app(Expr::bvar(0));
        self.is_def_eq(body, &applied)
    }

    /// Returns `true` if `a` and `b` are two proofs of one proposition.
    ///
    /// The test needs the type of each side, so it needs both sides to be
    /// closed. A loose bound variable has no type.
    fn proof_irrelevant(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        if a.has_loose_bvars() || b.has_loose_bvars() {
            return Ok(false);
        }
        let type_a = self.infer_type(a)?;
        // The type of the type must be `Sort 0`, which is `Prop`.
        let sort = self.infer_type(&type_a)?;
        let Expr::Sort(level) = self.whnf(&sort)? else {
            return Ok(false);
        };
        if !level.normalize().is_zero() {
            return Ok(false);
        }
        let type_b = self.infer_type(b)?;
        self.is_def_eq(&type_a, &type_b)
    }

    // --- the type rules --------------------------------------------------

    /// Returns the type of `e`.
    pub fn infer_type(&mut self, e: &Expr) -> TypeResult<Expr> {
        match e {
            Expr::BVar(index) => Err(TypeError::LooseBVar(*index)),

            Expr::FVar(id) => self
                .lctx
                .type_of(*id)
                .cloned()
                .ok_or(TypeError::UnknownFVar(*id)),

            Expr::MVar(id) => Err(TypeError::MetavariableLeft(*id)),

            // `Sort u : Sort (u+1)`.
            Expr::Sort(level) => Ok(Expr::Sort(level.succ())),

            // The environment gives the type, after the universe arguments go in.
            Expr::Const { name, levels } => {
                let decl = self
                    .env
                    .get(name)
                    .ok_or_else(|| TypeError::UnknownConstant(name.clone()))?;
                let params = decl.level_params();
                if params.len() != levels.len() {
                    return Err(TypeError::LevelArity {
                        name: name.clone(),
                        expected: params.len(),
                        got: levels.len(),
                    });
                }
                Ok(decl.ty().instantiate_levels(params, levels))
            }

            Expr::Lit(Literal::Nat(_)) => Ok(Expr::const_("Nat", vec![])),
            Expr::Lit(Literal::Str(_)) => Ok(Expr::const_("String", vec![])),

            // The level is `imax u v`, and that is what makes `Prop`
            // impredicative.
            Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } => {
                let u = self.infer_sort(binder_type)?;
                let id = self.lctx.push(binder_name.clone(), (**binder_type).clone());
                let opened = body.instantiate(&Expr::FVar(id));
                let v = self.infer_sort(&opened);
                self.lctx.pop();
                Ok(Expr::Sort(u.imax(&v?)))
            }

            // Open the binder, infer the body, then close it again.
            Expr::Lam {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                self.infer_sort(binder_type)?;
                let id = self.lctx.push(binder_name.clone(), (**binder_type).clone());
                let opened = body.instantiate(&Expr::FVar(id));
                let body_type = self.infer_type(&opened).map(|ty| ty.abstract_fvar(id));
                self.lctx.pop();
                Ok(Expr::Forall {
                    binder_name: binder_name.clone(),
                    binder_type: binder_type.clone(),
                    body: Arc::new(body_type?),
                    info: *info,
                })
            }

            // The only rule that puts a value into a type.
            Expr::App { fun, arg } => {
                let fun_type = self.infer_type(fun)?;
                let Expr::Forall {
                    binder_type, body, ..
                } = self.whnf(&fun_type)?
                else {
                    return Err(TypeError::not_a_function(fun, fun_type));
                };
                let arg_type = self.infer_type(arg)?;
                if !self.is_def_eq(&arg_type, &binder_type)? {
                    return Err(TypeError::mismatch(arg, (*binder_type).clone(), arg_type));
                }
                Ok(body.instantiate(arg))
            }

            // ζ: substitute the value into the body.
            Expr::Let {
                binder_type,
                value,
                body,
                ..
            } => {
                self.infer_sort(binder_type)?;
                let value_type = self.infer_type(value)?;
                if !self.is_def_eq(&value_type, binder_type)? {
                    return Err(TypeError::mismatch(
                        value,
                        (**binder_type).clone(),
                        value_type,
                    ));
                }
                let opened = body.instantiate(value);
                self.infer_type(&opened)
            }

            Expr::Proj(proj) => self.infer_proj(e, proj),
        }
    }

    /// Returns the type of a projection.
    ///
    /// The field types come from the single constructor of the structure. Each
    /// field before the wanted one gets filled with a projection of the same
    /// term, because a later field can mention an earlier one.
    fn infer_proj(&mut self, whole: &Expr, proj: &Proj) -> TypeResult<Expr> {
        let value_type = self.infer_type(&proj.value)?;
        let value_type = self.whnf(&value_type)?;
        let (head, params) = value_type.unfold_apps();
        let Expr::Const {
            name: inductive,
            levels,
        } = head
        else {
            return Err(TypeError::not_a_structure(whole, value_type.clone()));
        };
        let ctor = self
            .env
            .sole_ctor(inductive)
            .ok_or_else(|| TypeError::not_a_structure(whole, value_type.clone()))?
            .clone();

        let mut ty = ctor.ty.instantiate_levels(&ctor.level_params, levels);
        // Fill the parameters from the type of the term.
        for param in params.iter().take(ctor.num_params as usize) {
            let Expr::Forall { body, .. } = self.whnf(&ty)? else {
                return Err(TypeError::not_a_structure(whole, value_type.clone()));
            };
            ty = body.instantiate(param);
        }
        // Walk past each earlier field.
        for index in 0..proj.index {
            let Expr::Forall { body, .. } = self.whnf(&ty)? else {
                return Err(TypeError::BadProjection {
                    structure: proj.structure.clone(),
                    index: proj.index,
                });
            };
            let earlier = Expr::Proj(Proj {
                structure: proj.structure.clone(),
                index,
                value: proj.value.clone(),
            });
            ty = body.instantiate(&earlier);
        }
        let Expr::Forall { binder_type, .. } = self.whnf(&ty)? else {
            return Err(TypeError::BadProjection {
                structure: proj.structure.clone(),
                index: proj.index,
            });
        };
        Ok((*binder_type).clone())
    }

    /// Returns the level of `e`, and fails if `e` is not a type.
    pub fn infer_sort(&mut self, e: &Expr) -> TypeResult<Level> {
        let ty = self.infer_type(e)?;
        match self.whnf(&ty)? {
            Expr::Sort(level) => Ok(level),
            got => Err(TypeError::not_a_type(e, got)),
        }
    }

    /// Checks that `e` has the type `expected`.
    pub fn check(&mut self, e: &Expr, expected: &Expr) -> TypeResult<()> {
        // A proof of something that is not a type means nothing.
        self.infer_sort(expected)?;
        let got = self.infer_type(e)?;
        if self.is_def_eq(&got, expected)? {
            return Ok(());
        }
        Err(TypeError::mismatch(e, expected.clone(), got))
    }

    /// Checks one declaration: its type is a type, and its value has that type.
    ///
    /// This is the entry point of the level 1 checkpoint in `docs/ROADMAP.md`.
    pub fn check_declaration(&mut self, decl: &Declaration) -> TypeResult<()> {
        self.infer_sort(decl.ty())?;
        let value = match decl {
            Declaration::Definition(d) => Some(&d.value),
            Declaration::Theorem(d) => Some(&d.value),
            Declaration::Opaque(d) => Some(&d.value),
            _ => None,
        };
        if let Some(value) = value {
            let got = self.infer_type(value)?;
            if !self.is_def_eq(&got, decl.ty())? {
                return Err(TypeError::mismatch(value, decl.ty().clone(), got));
            }
        }
        Ok(())
    }
}
