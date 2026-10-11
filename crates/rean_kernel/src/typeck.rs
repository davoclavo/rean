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
//! Plus proof irrelevance, projection of a constructor, K-like ι reduction for
//! `Eq.rec`, the two quotient rules, and direct computation on a `Nat` literal.
//!
//! # What is still missing
//!
//! | Missing | Effect |
//! |---|---|
//! | recursor re-derivation | the recursor and its ι rules are trusted as given |
//! | positivity for a nested inductive | skipped, not checked. See [`crate::positivity`]. |
//! | a full level normal form | a hard pair of open levels can fail to match |
//! | big number arithmetic | a literal past `u128` stays stuck rather than compute |

use crate::environment::{
    ConstructorVal, Declaration, Environment, InductiveVal, QuotKind, RecursorRule, RecursorVal,
};
use crate::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, Proj, Sub, mix_hashes};
use crate::level::Level;
use crate::local::LocalContext;
use crate::nat_lit::{self, NatShape};
use crate::positivity::{self, PositivityError};
use rean_core::Name;
use std::collections::HashMap;
use std::fmt;

/// The largest number of reduction steps that [`TypeChecker::whnf`] will take.
///
/// The theory says that reduction terminates. A corrupt input file does not
/// have to obey the theory, so the loop needs a bound.
/// How much of a term one reduction step may be charged for.
///
/// See [`Expr::size_up_to`] for why the count has a cap at all.
const SIZE_CAP: u32 = 100_000;

/// How large a term must be before the `whnf` cache takes an interest in it.
///
/// A lookup costs a hash and then an [`Expr::alpha_eq`] against each answer in
/// the bucket. For a small term that is as much work as the reduction it would
/// save, so the cache ignores one. The number comes from a sweep.
const CACHE_MIN_SIZE: u32 = 4;

/// How many hash buckets the `whnf` cache keeps before it starts again.
///
/// A cache of answers nobody asks for is only memory. The number is a round
/// one, and `REAN_FUEL` is the knob that matters more.
const CACHE_CAP: usize = 200_000;

/// How much work one declaration may take.
///
/// `whnf` already has a step limit, and that is not enough. A comparison of two
/// large terms calls `whnf` again and again, and nothing bounded the total. A
/// run over the Lean prelude went from 78 seconds to no answer at all after the
/// level normal form improved, because a pair that used to fail fast on a
/// universe mismatch now went on to explore a term the size of a module.
///
/// So the checker carries fuel. Each reduction step and each comparison spends
/// one unit, and the budget resets for every declaration. A declaration that
/// runs out is reported as a failure with a clear reason, which is the honest
/// answer: we did not check it.
///
/// This is a bound, not a fix. The real cure is the one Lean uses: cache the
/// loose bound variable range in every node so substitution can skip a closed
/// subterm without walking it, and cache the result of a comparison. Both are
/// in the roadmap.
const FUEL: u64 = 20_000_000;

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
    /// The declaration took more work than the budget allows.
    OutOfFuel(u64),
    /// A constructor type is not acceptable, so the inductive declaration is
    /// not sound. This is the check that stops a user from proving `False`.
    BadConstructor {
        ctor: Name,
        inductive: Name,
        reason: PositivityError,
    },
    /// A recursor does not match the inductive type that it claims to
    /// eliminate. Without this check, a file can smuggle in an arbitrary
    /// axiom disguised as a recursor, and prove `False`.
    BadRecursor { recursor: Name, reason: String },
    /// A declaration uses a universe parameter that it does not declare.
    UndeclaredUniverse { declaration: Name, param: Name },
    /// A declaration lists one universe parameter twice.
    RepeatedUniverse { declaration: Name, param: Name },
    /// The environment already holds this name.
    DuplicateDeclaration(Name),
    /// A safe declaration uses one that is not safe.
    UnsafeDependency { declaration: Name, dependency: Name },
    /// A constructor field lives in a larger universe than its inductive type.
    FieldTooLarge {
        ctor: Name,
        inductive: Name,
        field: u32,
        field_level: String,
        limit: String,
    },
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
            TypeError::OutOfFuel(budget) => {
                format!(
                    "this declaration needed more than {budget} units of work, \
                     so it was not checked"
                )
            }
            TypeError::BadConstructor {
                ctor,
                inductive,
                reason,
            } => {
                let detail = match reason {
                    PositivityError::NotStrictlyPositive { field } => format!(
                        "field {field} uses `{inductive}` in a position that is not \
                         strictly positive. Such a declaration can prove `False`."
                    ),
                    PositivityError::TooFewBinders { expected } => {
                        format!("the type needs {expected} binders and has fewer")
                    }
                    PositivityError::WrongResult => {
                        format!("it does not return `{inductive}`")
                    }
                };
                format!("the constructor `{ctor}` is not acceptable: {detail}")
            }
            TypeError::BadRecursor { recursor, reason } => {
                format!("the recursor `{recursor}` is not acceptable: {reason}")
            }
            TypeError::UndeclaredUniverse { declaration, param } => format!(
                "`{declaration}` uses the universe parameter `{param}` and does not declare it"
            ),
            TypeError::RepeatedUniverse { declaration, param } => {
                format!("`{declaration}` lists the universe parameter `{param}` twice")
            }
            TypeError::DuplicateDeclaration(name) => {
                format!("the environment already holds `{name}`")
            }
            TypeError::FieldTooLarge {
                ctor,
                inductive,
                field,
                field_level,
                limit,
            } => format!(
                "field {field} of `{ctor}` lives in `Sort {field_level}` and `{inductive}` \
                 only reaches `Sort {limit}`"
            ),
            TypeError::UnsafeDependency {
                declaration,
                dependency,
            } => format!(
                "`{declaration}` is safe and it uses `{dependency}`, which is not. \
                 An unsafe declaration may not terminate, so a proof must not rest on one."
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

/// A checker over one environment.
pub struct TypeChecker<'e> {
    env: &'e Environment,
    lctx: LocalContext,
    /// The declarations under check, which may refer to each other.
    ///
    /// A recursor needs this. The ι rule for `Nat.succ` rewrites to a term
    /// that calls `Nat.rec` again, so checking `Nat.rec` needs the type of
    /// `Nat.rec`, and the environment does not hold it yet. Putting the
    /// declaration here lets the check ask "are these rules consistent with
    /// the type that this declaration claims?", which is the right question.
    ///
    /// A **mutual** group needs more than one. The rule of `A.rec` for a
    /// constructor that carries a `B` calls `B.rec`, so the two recursors only
    /// make sense together. The export format puts a whole mutual group on one
    /// line for exactly this reason.
    pending: Vec<Declaration>,
    /// What is left of the work budget for the declaration under check.
    fuel: u64,
    /// The budget that each declaration starts with. See [`FUEL`].
    budget: u64,
    /// Answers that [`Self::whnf`] already found, by the hash of the question.
    ///
    /// The checker reduces the same subterm again and again while it unfolds
    /// one well founded definition, and the profile showed it: the heaviest
    /// frame was the drop of a term that a reduction built and discarded.
    ///
    /// The key is a hash, so **one bucket can hold more than one answer**. A
    /// lookup compares the question with [`Expr::alpha_eq`] before it trusts
    /// the answer. A proof checker may not be probably right.
    whnf_cache: HashMap<u64, Vec<(Expr, Expr)>>,
    /// Answers that [`Self::is_def_eq`] already found.
    ///
    /// The same discipline as [`Self::whnf_cache`]. The key mixes the hash of
    /// both sides, and a hit is confirmed against both questions.
    ///
    /// A **negative** answer is cached as well as a positive one. `Ok(false)`
    /// means the two terms are not equal, which is a decision; a comparison
    /// that ran out of budget returns `Err` instead, and no error is cached.
    def_eq_cache: HashMap<u64, Vec<(Expr, Expr, bool)>>,
}

impl<'e> TypeChecker<'e> {
    /// Sets the work budget for each declaration. See [`FUEL`].
    ///
    /// A benchmark over a large file may want a smaller budget, so that one
    /// heavy declaration costs seconds rather than minutes. A smaller budget
    /// reports more declarations as unchecked, which is the honest trade.
    pub fn set_fuel(&mut self, fuel: u64) {
        self.budget = fuel;
        self.fuel = fuel;
    }

    /// Builds a checker with an empty local context.
    pub fn new(env: &'e Environment) -> Self {
        TypeChecker {
            env,
            lctx: LocalContext::new(),
            pending: Vec::new(),
            fuel: FUEL,
            budget: FUEL,
            whnf_cache: HashMap::new(),
            def_eq_cache: HashMap::new(),
        }
    }

    /// Looks up a declaration, and sees the ones under check as well.
    fn lookup(&self, name: &Name) -> Option<&Declaration> {
        if let Some(found) = self.pending.iter().find(|decl| decl.name() == name) {
            return Some(found);
        }
        self.env.get(name)
    }

    /// Makes a group of declarations visible to each other, then runs `body`.
    ///
    /// A mutual group arrives on one line of the export file, and its members
    /// refer to each other, so a checker must see all of them at once. The
    /// group is **not** added to the environment. It is only visible while
    /// `body` runs.
    pub fn with_group<R>(&mut self, group: &[Declaration], body: impl FnOnce(&mut Self) -> R) -> R {
        // δ reads the declarations under check, so an answer from before this
        // group may rest on a different set of them.
        self.clear_caches();
        let saved = std::mem::replace(&mut self.pending, group.to_vec());
        let out = body(self);
        self.pending = saved;
        self.clear_caches();
        out
    }

    /// Spends one unit of the work budget.
    fn spend(&mut self) -> TypeResult<()> {
        self.spend_many(1)
    }

    /// Spends `units` of the work budget.
    fn spend_many(&mut self, units: u32) -> TypeResult<()> {
        match self.fuel.checked_sub(u64::from(units)) {
            Some(left) => {
                self.fuel = left;
                Ok(())
            }
            None => {
                self.fuel = 0;
                // The message names the budget that this run set, not the
                // default. `REAN_FUEL` overrides it, and a report that still
                // printed the default was simply false.
                Err(TypeError::OutOfFuel(self.budget))
            }
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
        let worth_it = e.size_up_to(CACHE_MIN_SIZE) >= CACHE_MIN_SIZE;
        let key = if worth_it { e.hash_value() } else { 0 };
        if worth_it
            && let Some(bucket) = self.whnf_cache.get(&key)
            && let Some((_, answer)) = bucket.iter().find(|(question, _)| question.alpha_eq(e))
        {
            return Ok(answer.clone());
        }
        let (answer, steps) = self.whnf_uncached(e)?;
        // A term that was already in weak head normal form is not worth an
        // entry. Finding that out again costs one `whnf_step` that fires no
        // rule, and the entry would cost two clones and the memory to hold
        // them. Most calls are of that kind.
        if worth_it && steps > 0 {
            self.remember_whnf(key, e, &answer);
        }
        Ok(answer)
    }

    /// Stores one answer of [`Self::whnf`].
    ///
    /// The cache is cleared for each declaration, because a term that mentions
    /// a free variable only means something in the context that holds it. It
    /// also has a cap, because the Lean prelude would otherwise fill memory
    /// with answers that no later declaration asks for.
    fn remember_whnf(&mut self, key: u64, question: &Expr, answer: &Expr) {
        if self.whnf_cache.len() >= CACHE_CAP {
            self.whnf_cache.clear();
        }
        self.whnf_cache
            .entry(key)
            .or_default()
            .push((question.clone(), answer.clone()));
    }

    /// Reduces to weak head normal form, and asks no cache.
    ///
    /// Returns the result and the number of rules that fired, so that the
    /// caller can decide whether the answer is worth keeping.
    fn whnf_uncached(&mut self, e: &Expr) -> TypeResult<(Expr, u32)> {
        let mut current = e.clone();
        // The budget is the only bound this loop needs, and it is a real one.
        // `whnf_step` spends a unit before it tries any rule, so the loop
        // cannot run more times than the budget holds. A second limit of its
        // own was redundant, and it fired on 108 correct declarations of the
        // Lean prelude once the caches made each step cheap enough to reach it.
        let mut steps = 0u32;
        loop {
            match self.whnf_step(&current)? {
                Some(next) => {
                    // A step can make the term larger, and the ι rule often
                    // does. So the budget pays for the **size of what the step
                    // produced**, not merely for the step.
                    //
                    // Counting steps alone makes the budget meaningless: one
                    // `BitVec` theorem of the Lean prelude reduced for minutes
                    // inside a budget of two million steps, because every step
                    // substituted a bigger term than the last.
                    self.spend_many(next.size_up_to(SIZE_CAP))?;
                    current = next;
                    steps = steps.saturating_add(1);
                }
                None => return Ok((current, steps)),
            }
        }
    }

    /// Does one reduction step at the head, or returns `None` if none applies.
    fn whnf_step(&mut self, e: &Expr) -> TypeResult<Option<Expr>> {
        self.spend()?;
        let (head, borrowed) = e.unfold_apps();
        // The arguments stay borrowed until a rule actually fires. Cloning
        // them first cost a whole `Vec` of deep copies per reduction step,
        // and most steps do not fire.
        let cloned = || -> Vec<Expr> { borrowed.iter().map(|arg| (*arg).clone()).collect() };

        // ζ: a `let` in the head position substitutes its value.
        if let Expr::Let { value, body, .. } = head {
            return Ok(Some(body.instantiate(value).apps(cloned())));
        }

        // β: a lambda in the head position takes its first argument.
        if let Some(next) = e.beta_step() {
            return Ok(Some(next));
        }

        // A projection of a constructor application takes the field.
        if let Expr::Proj(proj) = head
            && let Some(field) = self.proj_step(proj)?
        {
            return Ok(Some(field.apps(cloned())));
        }

        if let Expr::Const { name, levels } = head {
            let args = cloned();
            // The kernel computes on a `Nat` literal directly.
            if let Some(next) = self.nat_step(name, &args)? {
                return Ok(Some(next));
            }
            // And on a string literal.
            if let Some(next) = self.string_step(name, &args)? {
                return Ok(Some(next));
            }
            // ι: a recursor applied to a constructor rewrites to its rule.
            if let Some(next) = self.iota_step(name, levels, &args)? {
                return Ok(Some(next));
            }
            // The quotient rules, for `Quot.lift` and `Quot.ind`.
            if let Some(next) = self.quot_step(name, &args)? {
                return Ok(Some(next));
            }
            // δ: a definition unfolds to its value.
            if let Some(decl) = self.lookup(name)
                && let Some(value) = decl.unfoldable_value()
            {
                let value = value.instantiate_levels(decl.level_params(), levels);
                return Ok(Some(value.apps(args)));
            }
        }

        Ok(None)
    }

    /// Computes a function on two `Nat` literals.
    ///
    /// Without this step, `2 + 3` would unfold through `Nat.rec` once per unit,
    /// so a real program would exhaust the reduction budget.
    fn nat_step(&mut self, name: &Name, args: &[Expr]) -> TypeResult<Option<Expr>> {
        if !nat_lit::is_binop(name) || args.len() < 2 {
            return Ok(None);
        }
        // A `Bool` result needs the constructors to exist.
        if nat_lit::returns_bool(name) && !self.env.contains(&Name::from_dotted("Bool.true")) {
            return Ok(None);
        }
        let left = self.whnf(&args[0])?;
        let right = self.whnf(&args[1])?;
        let (Some(a), Some(b)) = (nat_lit::value(&left), nat_lit::value(&right)) else {
            return Ok(None);
        };
        let Some(out) = nat_lit::binop(name, a, b) else {
            // The answer does not fit in a `u128`. Stay stuck rather than lie.
            return Ok(None);
        };
        Ok(Some(out.apps(args[2..].iter().cloned())))
    }

    /// Computes a function of one string literal.
    fn string_step(&mut self, name: &Name, args: &[Expr]) -> TypeResult<Option<Expr>> {
        if !nat_lit::is_string_op(name) || args.is_empty() {
            return Ok(None);
        }
        let only = self.whnf(&args[0])?;
        let Some(text) = nat_lit::str_value(&only) else {
            return Ok(None);
        };
        let Some(out) = nat_lit::string_op(name, text) else {
            return Ok(None);
        };
        Ok(Some(out.apps(args[1..].iter().cloned())))
    }

    /// Applies a quotient rule.
    ///
    /// ```text
    /// Quot.lift α r β f h (Quot.mk α r a)  ~>  f a
    /// Quot.ind  α r β h   (Quot.mk α r a)  ~>  h a
    /// ```
    ///
    /// `Quot` is a kernel primitive. You cannot build it from an inductive
    /// declaration, so it needs its own rule. See chapter 0, section 0.14.
    fn quot_step(&mut self, name: &Name, args: &[Expr]) -> TypeResult<Option<Expr>> {
        let Some(Declaration::Quot(quot)) = self.lookup(name) else {
            return Ok(None);
        };
        // `lift` takes the function at 3 and the quotient at 5.
        // `ind` takes the proof at 3 and the quotient at 4.
        let (function_index, major_index) = match quot.kind {
            QuotKind::Lift => (3usize, 5usize),
            QuotKind::Ind => (3usize, 4usize),
            QuotKind::Type | QuotKind::Ctor => return Ok(None),
        };
        if args.len() <= major_index {
            return Ok(None);
        }
        let major = self.whnf(&args[major_index])?;
        let (head, mk_args) = major.unfold_apps();
        let Expr::Const { name: mk, .. } = head else {
            return Ok(None);
        };
        let Some(Declaration::Quot(mk_decl)) = self.lookup(mk) else {
            return Ok(None);
        };
        if mk_decl.kind != QuotKind::Ctor || mk_args.len() < 3 {
            return Ok(None);
        }
        // `Quot.mk α r a` carries the value in its third argument.
        let value = mk_args[2].clone();
        let out = args[function_index].clone().app(value);
        Ok(Some(out.apps(args[major_index + 1..].iter().cloned())))
    }

    /// Reduces a projection whose target is a constructor application.
    fn proj_step(&mut self, proj: &Proj) -> TypeResult<Option<Expr>> {
        let mut value = self.whnf(&proj.value)?;
        if let Some(as_ctor) = nat_lit::to_ctor_if_lit(&value) {
            value = as_ctor;
        }
        // The first field of a string literal is its byte array. The second is
        // a proof, and no rule has to produce a proof.
        if proj.index == 0
            && let Some(text) = nat_lit::str_value(&value)
        {
            return Ok(Some(nat_lit::str_bytes(text)));
        }
        let (head, args) = value.unfold_apps();
        let Expr::Const { name, .. } = head else {
            return Ok(None);
        };
        let Some(Declaration::Constructor(ctor)) = self.lookup(name) else {
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
        let Some(Declaration::Recursor(rec)) = self.lookup(name) else {
            return Ok(None);
        };
        let rec = rec.clone();
        let major_index = rec.major_index();
        if args.len() <= major_index {
            return Ok(None);
        }

        let mut major = self.whnf(&args[major_index])?;
        // A `Nat` literal must behave like a constructor application here.
        // `3` becomes `Nat.succ 2`, so the `Nat.succ` rule can fire.
        if let Some(as_ctor) = nat_lit::to_ctor_if_lit(&major) {
            major = as_ctor;
        }
        // A K-like recursor reduces even when the major premise is a variable.
        if let Some(as_ctor) = self.ctor_when_k(&rec, &major)? {
            major = as_ctor;
        }
        // A structure has one constructor and no index, so a term of that type
        // is its own fields. Rebuilding it lets the ι rule fire on a variable.
        if let Some(as_ctor) = self.ctor_when_struct(&rec, &major)? {
            major = as_ctor;
        }
        let (major_head, major_args) = major.unfold_apps();
        let Expr::Const { name: ctor, .. } = major_head else {
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

    /// Returns the number of parameters of `name`, if `name` is a structure.
    ///
    /// Three conditions decide that, and Lean's kernel asks for the same three.
    /// See [`Self::ctor_when_struct`] for what each one prevents. The method
    /// returns the parameter count rather than a `bool`, so that a caller which
    /// needs the count does not have to look the declaration up twice.
    fn structure_params(&self, name: &Name) -> Option<u32> {
        match self.lookup(name) {
            Some(Declaration::Inductive(ind))
                if ind.num_indices == 0 && !ind.is_rec && ind.ctors.len() == 1 =>
            {
                Some(ind.num_params)
            }
            _ => None,
        }
    }

    /// Rebuilds the major premise as a constructor application, by eta for
    /// structures.
    ///
    /// A **structure** is an inductive type with one constructor and no index.
    /// Every term of such a type is the constructor applied to that term's own
    /// fields, so
    ///
    /// ```text
    /// x : ByteArray    ~>    ByteArray.mk x.0
    /// ```
    ///
    /// holds for any `x`, even an opaque variable. The ι rule needs its major
    /// premise in constructor form, and this rule supplies one. Without it the
    /// kernel cannot reduce `ByteArray.push x b`, because `push` matches on
    /// `⟨bs⟩` and `x` is not yet of that shape.
    ///
    /// Three conditions keep the rule sound, and Lean checks the same three:
    ///
    /// - **One constructor.** With two, the term could be either one.
    /// - **No index.** An index can differ between the term and the rebuilt
    ///   one, as it does for `Eq`, and then the two are not the same type.
    /// - **Not recursive.** A field of the type itself would make the rebuilt
    ///   term grow without end.
    fn ctor_when_struct(&mut self, rec: &RecursorVal, major: &Expr) -> TypeResult<Option<Expr>> {
        // The rule reads the type of the major premise, so the premise must be
        // closed. See the guard in `struct_eta_eq` for why that matters.
        if major.has_loose_bvars() {
            return Ok(None);
        }
        // Already a constructor application, so there is nothing to do.
        if let (Expr::Const { name, .. }, _) = major.unfold_apps()
            && matches!(self.lookup(name), Some(Declaration::Constructor(_)))
        {
            return Ok(None);
        }
        // This test is cheap, and the next step is not. Most recursors of the
        // prelude are over a type that is no structure, such as `Nat` or
        // `List`, and for those the rule can never fire. Asking first keeps the
        // call to `infer_type` out of the common path. It was the heaviest
        // frame in a profile once this rule existed.
        if !rec
            .all
            .iter()
            .any(|name| self.structure_params(name).is_some())
        {
            return Ok(None);
        }
        let major_type = self.infer_type(major)?;
        let major_type = self.whnf(&major_type)?;
        let (head, type_args) = major_type.unfold_apps();
        let Expr::Const {
            name: inductive,
            levels,
        } = head
        else {
            return Ok(None);
        };
        // The type must be the one this recursor speaks about, and it must be
        // the structure itself, not a sibling in the same mutual group.
        if !rec.all.contains(inductive) {
            return Ok(None);
        }
        let Some(num_params) = self.structure_params(inductive) else {
            return Ok(None);
        };
        let num_params = num_params as usize;
        let Some(ctor) = self.env.sole_ctor(inductive) else {
            return Ok(None);
        };
        let ctor_name = ctor.name.clone();
        let num_fields = ctor.num_fields;
        if type_args.len() < num_params {
            return Ok(None);
        }
        let mut out = Expr::Const {
            name: ctor_name,
            levels: levels.clone(),
        }
        .apps(type_args[..num_params].iter().map(|arg| (*arg).clone()));
        for index in 0..num_fields {
            out = out.app(Expr::Proj(Proj {
                structure: inductive.clone(),
                index,
                value: Sub::new(major.clone()),
            }));
        }
        Ok(Some(out))
    }

    /// Builds the constructor application for a K-like recursor.
    ///
    /// `Eq.rec` is the example. `Eq` has one constructor, `Eq.refl`, and that
    /// constructor has no field. So a proof of `a = b` carries no information
    /// beyond its own existence, and the recursor may reduce even when the
    /// proof is an opaque variable.
    ///
    /// The method reads the **type** of the major premise, takes the inductive
    /// and its parameters from that type, and builds the sole constructor from
    /// them. It then checks that the result has the same type, so that an index
    /// mismatch cannot slip through.
    fn ctor_when_k(&mut self, rec: &RecursorVal, major: &Expr) -> TypeResult<Option<Expr>> {
        if !rec.k {
            return Ok(None);
        }
        // The rule reads the type of the major premise, so the premise must be
        // closed. See the guard in `struct_eta_eq` for why that matters.
        if major.has_loose_bvars() {
            return Ok(None);
        }
        // Already a constructor application, so there is nothing to do.
        if let (Expr::Const { name, .. }, _) = major.unfold_apps()
            && matches!(self.lookup(name), Some(Declaration::Constructor(_)))
        {
            return Ok(None);
        }
        let major_type = self.infer_type(major)?;
        let major_type = self.whnf(&major_type)?;
        let (head, type_args) = major_type.unfold_apps();
        let Expr::Const {
            name: inductive,
            levels,
        } = head
        else {
            return Ok(None);
        };
        if !rec.all.contains(inductive) {
            return Ok(None);
        }
        let Some(ctor) = self.env.sole_ctor(inductive) else {
            return Ok(None);
        };
        // K-like reduction only makes sense when the constructor has no field.
        if ctor.num_fields != 0 {
            return Ok(None);
        }
        let ctor_app = Expr::Const {
            name: ctor.name.clone(),
            levels: levels.clone(),
        }
        .apps(
            type_args
                .iter()
                .take(ctor.num_params as usize)
                .map(|a| (*a).clone()),
        );
        let ctor_type = self.infer_type(&ctor_app)?;
        if self.is_def_eq(&ctor_type, &major_type)? {
            return Ok(Some(ctor_app));
        }
        Ok(None)
    }

    // --- definitional equality ------------------------------------------

    /// Returns `true` if `a` and `b` are the same term by computation.
    pub fn is_def_eq(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        // The cheap test. Most comparisons stop here, and it costs no fuel.
        if a.alpha_eq(b) {
            return Ok(true);
        }
        // Past that test the work can be unbounded, so the answer is worth
        // keeping whatever the size of the two terms. See chapter 10.
        let key = mix_hashes(a.hash_value(), b.hash_value());
        if let Some(bucket) = self.def_eq_cache.get(&key)
            && let Some((.., answer)) = bucket
                .iter()
                .find(|(left, right, _)| left.alpha_eq(a) && right.alpha_eq(b))
        {
            return Ok(*answer);
        }
        let answer = self.is_def_eq_uncached(a, b)?;
        self.remember_def_eq(key, a, b, answer);
        Ok(answer)
    }

    /// Clears every cache. See [`Self::whnf_cache`].
    fn clear_caches(&mut self) {
        self.whnf_cache.clear();
        self.def_eq_cache.clear();
    }

    /// Stores one answer of [`Self::is_def_eq`].
    fn remember_def_eq(&mut self, key: u64, a: &Expr, b: &Expr, answer: bool) {
        if self.def_eq_cache.len() >= CACHE_CAP {
            self.def_eq_cache.clear();
        }
        self.def_eq_cache
            .entry(key)
            .or_default()
            .push((a.clone(), b.clone(), answer));
    }

    /// Compares two terms, and asks no cache.
    fn is_def_eq_uncached(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        self.spend()?;
        // **Compare before you unfold.**
        //
        // `whnf` below unfolds the head of each side, and δ on a definition can
        // replace a small term with an enormous one. But two terms with the
        // same head and equal arguments are equal by congruence, and finding
        // that out costs only the arguments.
        //
        // `Nat.div x y ≡ Nat.div x y` is the shape, and the Lean prelude is
        // full of it. The old order unfolded `Nat.div` on both sides first, so
        // one theorem of character validity asked for more than 32 **billion**
        // units of work. Lean's kernel asks this question first for the same
        // reason.
        //
        // A `false` answer proves nothing, so it falls through to the full
        // comparison below. Only a `true` answer is a decision.
        if self.spine_eq(a, b)? {
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

        // A `Nat` literal against the matching constructor chain.
        if self.nat_lit_eq(&a, &b)? {
            return Ok(true);
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
        // η for a structure: `S.mk p.1 p.2` is the same term as `p`.
        if self.struct_eta_eq(&a, &b)? || self.struct_eta_eq(&b, &a)? {
            return Ok(true);
        }
        // A type with one term has only one term, so any two of them are equal.
        if self.unit_like_eq(&a, &b)? {
            return Ok(true);
        }
        // Proof irrelevance: all proofs of one proposition are equal.
        self.proof_irrelevant(&a, &b)
    }

    /// Compares two terms of a type that has exactly one term.
    ///
    /// `Unit` is the example. It is a structure with one constructor and no
    /// field, so every term of it is `Unit.unit`, and
    ///
    /// ```text
    /// (a : Unit)  ≡  (b : Unit)
    /// ```
    ///
    /// holds for any `a` and `b`. This is η for a structure again, read on both
    /// sides at once: `a ≡ ⟨⟩ ≡ b`. [`Self::struct_eta_eq`] cannot see it,
    /// because that rule needs one side to be a constructor already, and here
    /// neither side is. `Unit.ext` of the Lean prelude needs this rule.
    ///
    /// The two types must be the same. Without that test the rule would equate
    /// terms of two different one-term types.
    fn unit_like_eq(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        // The rule asks for a type, so both sides must be closed. See the guard
        // in `struct_eta_eq` for why a comparison helper must decline and never
        // error.
        if a.has_loose_bvars() || b.has_loose_bvars() {
            return Ok(false);
        }
        let a_type = self.infer_type(a)?;
        let a_type = self.whnf(&a_type)?;
        let (head, _) = a_type.unfold_apps();
        let Expr::Const { name, .. } = head else {
            return Ok(false);
        };
        if self.structure_params(name).is_none() {
            return Ok(false);
        }
        let Some(ctor) = self.env.sole_ctor(name) else {
            return Ok(false);
        };
        // One term exists only when the constructor carries nothing.
        if ctor.num_fields != 0 {
            return Ok(false);
        }
        let b_type = self.infer_type(b)?;
        self.is_def_eq(&a_type, &b_type)
    }

    /// Compares a `Nat` literal with a constructor chain.
    ///
    /// `1` and `Nat.succ Nat.zero` are the same number, so the kernel must say
    /// so. The literal shrinks by one on each step, so the recursion ends.
    fn nat_lit_eq(&mut self, a: &Expr, b: &Expr) -> TypeResult<bool> {
        let (number, other) = match (nat_lit::value(a), nat_lit::value(b)) {
            (Some(n), None) => (n, b),
            (None, Some(n)) => (n, a),
            // Two literals already compared by value, and two non literals are
            // not this method's business.
            _ => return Ok(false),
        };
        match nat_lit::shape(other) {
            Some(NatShape::Zero) => Ok(number == 0),
            Some(NatShape::Succ(inner)) => {
                if number == 0 {
                    return Ok(false);
                }
                self.is_def_eq(&nat_lit::lit(number - 1), inner)
            }
            None => Ok(false),
        }
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
        let id = self.lctx.push(name.clone(), left_type.to_expr());
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
        let Expr::Lam {
            binder_name,
            binder_type,
            body,
            ..
        } = lam
        else {
            return Ok(false);
        };
        if matches!(other, Expr::Lam { .. }) {
            return Ok(false);
        }
        // Open the binder into a free variable, then compare `body` with
        // `other x`.
        //
        // The first version stayed in de Bruijn and compared `body` with
        // `other` lifted and applied to `BVar 0`. That is correct as far as the
        // shapes go, and it leaves **both sides open**, so nothing inside the
        // comparison can ask for a type. Proof irrelevance needs a type, and
        // without it `Option.pbind_join` of the Lean prelude fails: it is eta
        // on a dependent function whose second argument matches only because
        // all proofs of one proposition are equal.
        //
        // This is the same lesson as chapter 2, section 2.7. A free variable is
        // not only an optimisation. It is what keeps a term closed, and a
        // closed term is what lets a later step ask for its type.
        let id = self.lctx.push(binder_name.clone(), binder_type.to_expr());
        let opened = body.instantiate(&Expr::FVar(id));
        let applied = other.clone().app(Expr::FVar(id));
        let same = self.is_def_eq(&opened, &applied);
        self.lctx.pop();
        same
    }

    /// Returns `true` if `built` rebuilds `whole` field by field.
    ///
    /// A structure has one constructor and no index, so a term of that type is
    /// fully determined by its fields. `S.mk p.1 p.2` and `p` are therefore the
    /// same term. Lean calls this eta for structures.
    fn struct_eta_eq(&mut self, built: &Expr, whole: &Expr) -> TypeResult<bool> {
        // The rule asks for the type of `whole`, so `whole` must be closed. A
        // loose bound variable has no type.
        //
        // This guard is not decoration. `eta_eq` builds `other x` under a new
        // binder, which is open on purpose, and hands it to `is_def_eq`. Without
        // the guard, `infer_type` returns `LooseBVar` and the error leaves
        // `is_def_eq` entirely, so a whole declaration fails for a rule that
        // simply did not apply. `Option.pbind_join` of the Lean prelude is one
        // such declaration: its term is closed, and we made the loose variable
        // ourselves.
        //
        // A comparison helper must decline, never error.
        if built.has_loose_bvars() || whole.has_loose_bvars() {
            return Ok(false);
        }
        let (head, args) = built.unfold_apps();
        let Expr::Const { name, .. } = head else {
            return Ok(false);
        };
        let Some(Declaration::Constructor(ctor)) = self.lookup(name) else {
            return Ok(false);
        };
        let ctor = ctor.clone();
        if ctor.num_fields == 0 || args.len() != (ctor.num_params + ctor.num_fields) as usize {
            return Ok(false);
        }
        // The rule needs a structure: one constructor and no index.
        match self.lookup(&ctor.induct) {
            Some(Declaration::Inductive(ind)) if ind.ctors.len() == 1 && ind.num_indices == 0 => {}
            _ => return Ok(false),
        }
        // The other side must belong to the same structure, else a projection
        // of it has no meaning.
        let whole_type = self.infer_type(whole)?;
        let whole_type = self.whnf(&whole_type)?;
        let (whole_head, _) = whole_type.unfold_apps();
        match whole_head {
            Expr::Const { name, .. } if *name == ctor.induct => {}
            _ => return Ok(false),
        }
        let args: Vec<Expr> = args.into_iter().cloned().collect();
        for index in 0..ctor.num_fields {
            let field = &args[(ctor.num_params + index) as usize];
            let projected = Expr::Proj(Proj {
                structure: ctor.induct.clone(),
                index,
                value: Sub::new(whole.clone()),
            });
            if !self.is_def_eq(field, &projected)? {
                return Ok(false);
            }
        }
        Ok(true)
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
                    .lookup(name)
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
                let id = self.lctx.push(binder_name.clone(), binder_type.to_expr());
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
                let id = self.lctx.push(binder_name.clone(), binder_type.to_expr());
                let opened = body.instantiate(&Expr::FVar(id));
                let body_type = self.infer_type(&opened).map(|ty| ty.abstract_fvar(id));
                self.lctx.pop();
                Ok(Expr::Forall {
                    binder_name: binder_name.clone(),
                    binder_type: binder_type.clone(),
                    body: Sub::new(body_type?),
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
                    return Err(TypeError::mismatch(arg, binder_type.to_expr(), arg_type));
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
                        binder_type.to_expr(),
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
        // A missing constructor is not the same fault as a type that is no
        // structure, and saying so saves the reader a wrong hunt. The export is
        // in topological order, so this happens when the constructor itself was
        // rejected and never entered the environment.
        if let Some(Declaration::Inductive(ind)) = self.lookup(inductive)
            && let [only] = ind.ctors.as_slice()
            && self.lookup(only).is_none()
        {
            return Err(TypeError::UnknownConstant(only.clone()));
        }
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
        Ok(binder_type.to_expr())
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

    /// Runs the strict positivity check for one constructor.
    ///
    /// The inductive type that owns the constructor must already be in the
    /// environment. The export format lists it first, so a harness that walks
    /// the file in order satisfies that.
    ///
    /// A nested inductive type is skipped, not rejected. See
    /// [`crate::positivity`].
    pub fn check_positivity(&mut self, ctor: &crate::ConstructorVal) -> TypeResult<()> {
        let Some(Declaration::Inductive(inductive)) = self.lookup(&ctor.induct) else {
            // Without the inductive type there is nothing to check against.
            // `infer_sort` on the constructor type already reported the
            // unknown constant.
            return Ok(());
        };
        let names = if inductive.all.is_empty() {
            vec![inductive.name.clone()]
        } else {
            inductive.all.clone()
        };
        // A nested declaration gets the weaker rule. See `crate::positivity`.
        let check = if inductive.num_nested > 0 {
            positivity::check_nested_constructor
        } else {
            positivity::check_constructor
        };
        check(&ctor.ty, ctor.num_params, ctor.num_fields, &names).map_err(|reason| {
            TypeError::BadConstructor {
                ctor: ctor.name.clone(),
                inductive: ctor.induct.clone(),
                reason,
            }
        })?;
        self.check_field_universes(ctor)
    }

    /// Checks that every field of a constructor fits inside the universe of
    /// its inductive type.
    ///
    /// An inductive type declares a `Sort`, and a constructor field has a
    /// `Sort` of its own. If a field were larger, the inductive type would
    /// hold something bigger than itself, and that is the shape of Russell's
    /// paradox.
    ///
    /// `Prop` is the exception, because `Prop` is impredicative. A proposition
    /// may quantify over anything. See chapter 0, section 0.10.
    ///
    /// The order on levels is only partly decidable, and
    /// [`Level::is_leq`] answers `None` when it cannot tell. This check then
    /// **accepts**. A check that refused what it did not understand would
    /// refuse correct Lean.
    pub fn check_field_universes(&mut self, ctor: &crate::ConstructorVal) -> TypeResult<()> {
        let Some(Declaration::Inductive(inductive)) = self.lookup(&ctor.induct) else {
            return Ok(());
        };
        let inductive = inductive.clone();

        // The universe that the inductive type declares.
        let mut ind_type = inductive.ty.clone();
        while let Expr::Forall { body, .. } = self.whnf(&ind_type)? {
            ind_type = body.to_expr();
        }
        let Expr::Sort(limit) = ind_type else {
            return Ok(());
        };
        // `Prop` may hold anything.
        if limit.normalize().is_zero() {
            return Ok(());
        }

        let mark = self.lctx.len();
        let outcome = self.walk_field_universes(ctor, &inductive, &limit);
        self.truncate_locals(mark);
        outcome
    }

    fn walk_field_universes(
        &mut self,
        ctor: &crate::ConstructorVal,
        inductive: &InductiveVal,
        limit: &Level,
    ) -> TypeResult<()> {
        let mut ty = ctor.ty.clone();
        for _ in 0..ctor.num_params {
            let Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } = self.whnf(&ty)?
            else {
                return Ok(());
            };
            let id = self.lctx.push(binder_name, binder_type.to_expr());
            ty = body.instantiate(&Expr::FVar(id));
        }
        for field in 0..ctor.num_fields {
            let Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } = self.whnf(&ty)?
            else {
                return Ok(());
            };
            let field_level = self.infer_sort(&binder_type)?;
            if field_level.is_leq(limit) == Some(false) {
                return Err(TypeError::FieldTooLarge {
                    ctor: ctor.name.clone(),
                    inductive: inductive.name.clone(),
                    field,
                    field_level: field_level.to_string(),
                    limit: limit.to_string(),
                });
            }
            let id = self.lctx.push(binder_name, binder_type.to_expr());
            ty = body.instantiate(&Expr::FVar(id));
        }
        Ok(())
    }

    /// Removes every local variable added after `len`.
    fn truncate_locals(&mut self, len: usize) {
        while self.lctx.len() > len {
            self.lctx.pop();
        }
    }

    /// Checks that a safe declaration uses no unsafe one.
    ///
    /// An `unsafe` or `partial` declaration may not terminate. The kernel
    /// evaluates a term while it checks it, so a proof that rests on one could
    /// make the checker diverge, and a term that does not terminate can be
    /// given any type at all.
    ///
    /// An unsafe declaration may use anything. That is what the word means.
    pub fn check_safety(&mut self, decl: &Declaration) -> TypeResult<()> {
        if decl.is_unsafe() {
            return Ok(());
        }
        let mut uses = Vec::new();
        decl.collect_dependencies(&mut uses);
        for dependency in uses {
            if let Some(found) = self.lookup(&dependency)
                && found.is_unsafe()
            {
                return Err(TypeError::UnsafeDependency {
                    declaration: decl.name().clone(),
                    dependency,
                });
            }
        }
        Ok(())
    }

    /// Checks that every universe parameter a declaration uses is declared,
    /// and that it declares none twice.
    ///
    /// A parameter that is used and not declared is a free universe variable,
    /// and a free universe variable has no meaning.
    pub fn check_universes(&mut self, decl: &Declaration) -> TypeResult<()> {
        let declared = decl.level_params();
        for (index, param) in declared.iter().enumerate() {
            if declared[..index].contains(param) {
                return Err(TypeError::RepeatedUniverse {
                    declaration: decl.name().clone(),
                    param: param.clone(),
                });
            }
        }
        let mut used = Vec::new();
        decl.ty().collect_level_params(&mut used);
        if let Some(value) = declaration_value(decl) {
            value.collect_level_params(&mut used);
        }
        for param in used {
            if !declared.contains(&param) {
                return Err(TypeError::UndeclaredUniverse {
                    declaration: decl.name().clone(),
                    param,
                });
            }
        }
        Ok(())
    }

    /// Checks a recursor against the inductive type that it claims to
    /// eliminate.
    ///
    /// Without this check a file can declare a recursor with any type at all,
    /// and the kernel will believe it. That turns a recursor into an untracked
    /// axiom, and an untracked axiom proves `False`.
    ///
    /// The check has two halves:
    ///
    /// 1. **Shape.** There is one rule per constructor and no more, there is at
    ///    least one motive, and the declared type has enough binders.
    /// 2. **Each ι rule is type correct.** For every constructor, build the
    ///    term that the ι rule rewrites, work out the type that the recursor
    ///    promises for it, and check that the right hand side of the rule
    ///    delivers that type.
    ///
    /// Half 2 is the property that makes ι sound. A rule that delivers a
    /// different type lets you transport a term into a type it does not
    /// inhabit.
    ///
    /// A mutual recursor, with more than one motive, is **skipped**. The
    /// fixture has none, and a wrong check is worse than a missing one.
    pub fn check_recursor(&mut self, rec: &RecursorVal) -> TypeResult<()> {
        let bad = |reason: String| TypeError::BadRecursor {
            recursor: rec.name.clone(),
            reason,
        };

        if rec.num_motives == 0 {
            return Err(bad("a recursor needs at least one motive".to_string()));
        }

        // The mutual group, in the order the declaration gives.
        let mut group: Vec<InductiveVal> = Vec::new();
        for name in &rec.all {
            let Some(Declaration::Inductive(found)) = self.lookup(name) else {
                // Without the inductive type there is nothing to check against.
                return Ok(());
            };
            group.push(found.clone());
        }
        if group.is_empty() {
            return Ok(());
        }
        // A nested declaration is the one shape these checks cannot read.
        //
        // Lean compiles `inductive Rose | node : List Rose → Rose` into an
        // auxiliary type, and the recursor speaks about that type. So
        // `Rose.rec` reports two motives while its group lists one type, and
        // `Rose.rec_1` has rules for `List.nil` and `List.cons`, which belong
        // to no type in its group at all. Every count below would fire on a
        // correct declaration.
        //
        // So a nested recursor is **trusted**, and this is the one place the
        // checker still takes a recursor on faith. Chapter 7, section 7.5.
        if group.iter().any(|i| i.num_nested > 0) {
            return Ok(());
        }
        if rec.num_motives as usize != group.len() {
            return Err(bad(format!(
                "it has {} motives and its group has {} types",
                rec.num_motives,
                group.len()
            )));
        }

        // Which type does it take apart? The one that owns its rules. Reading
        // it from the rules needs no naming convention.
        let target = match rec.rules.first() {
            Some(first) => {
                let Some(Declaration::Constructor(owner)) = self.lookup(&first.ctor) else {
                    return Err(bad(format!("`{}` is not a constructor", first.ctor)));
                };
                let target_name = owner.induct.clone();
                let Some(index) = group.iter().position(|i| i.name == target_name) else {
                    return Err(bad(format!(
                        "its rules are for `{target_name}`, which is not in its own group"
                    )));
                };
                group[index].clone()
            }
            None => {
                // No rule at all. That is honest only for a type with no
                // constructor, such as `False`.
                let [only] = group.as_slice() else {
                    return Ok(());
                };
                if !only.ctors.is_empty() {
                    return Err(bad(format!(
                        "it has no rules and `{}` has {} constructors",
                        only.name,
                        only.ctors.len()
                    )));
                }
                only.clone()
            }
        };

        if rec.num_params != target.num_params || rec.num_indices != target.num_indices {
            return Err(bad(format!(
                "it claims {} parameters and {} indices, and `{}` has {} and {}",
                rec.num_params, rec.num_indices, target.name, target.num_params, target.num_indices
            )));
        }
        // Only the target's constructors can be the major premise, so the
        // rules must cover exactly those.
        if rec.rules.len() != target.ctors.len() {
            return Err(bad(format!(
                "it has {} rules and `{}` has {} constructors",
                rec.rules.len(),
                target.name,
                target.ctors.len()
            )));
        }
        for ctor in &target.ctors {
            if rec.rule_for(ctor).is_none() {
                return Err(bad(format!("it has no rule for `{ctor}`")));
            }
        }
        // The induction is simultaneous, so there is one minor premise per
        // constructor of every type in the group.
        let total: usize = group.iter().map(|i| i.ctors.len()).sum();
        if rec.num_minors as usize != total {
            return Err(bad(format!(
                "it has {} minor premises and its group has {total} constructors",
                rec.num_minors
            )));
        }

        let mark = self.lctx.len();
        // The rules call the recursor again, so the check needs its type. A
        // group may already have put it there.
        let seen = self.pending.iter().any(|decl| decl.name() == &rec.name);
        if !seen {
            self.pending.push(Declaration::Recursor(rec.clone()));
        }
        let outcome = self.check_recursor_rules(rec, &group, &target, &bad);
        if !seen {
            self.pending.pop();
        }
        self.truncate_locals(mark);
        outcome
    }

    /// The second half of [`TypeChecker::check_recursor`].
    fn check_recursor_rules(
        &mut self,
        rec: &RecursorVal,
        group: &[InductiveVal],
        target: &InductiveVal,
        bad: &dyn Fn(String) -> TypeError,
    ) -> TypeResult<()> {
        // Open the parameters, the motive and the minor premises.
        let mut residual = rec.ty.clone();
        let mut prefix = Vec::new();
        for _ in 0..rec.num_prefix() {
            let Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } = self.whnf(&residual)?
            else {
                return Err(bad("its type has too few binders".to_string()));
            };
            let id = self.lctx.push(binder_name, binder_type.to_expr());
            prefix.push(Expr::FVar(id));
            residual = body.instantiate(&Expr::FVar(id));
        }

        self.check_elimination_universe(rec, target, &prefix, bad)?;
        self.check_minor_premises(rec, group, &prefix, bad)?;

        for rule in &rec.rules {
            let Some(Declaration::Constructor(ctor)) = self.lookup(&rule.ctor) else {
                continue;
            };
            let ctor = ctor.clone();
            if ctor.num_fields != rule.num_fields {
                return Err(bad(format!(
                    "the rule for `{}` says {} fields and the constructor has {}",
                    rule.ctor, rule.num_fields, ctor.num_fields
                )));
            }
            let mark = self.lctx.len();
            let outcome = self.check_one_rule(rec, &ctor, rule, &prefix, &residual, bad);
            self.truncate_locals(mark);
            outcome?;
        }
        Ok(())
    }

    /// Checks that one ι rule delivers the type that the recursor promises.
    fn check_one_rule(
        &mut self,
        rec: &RecursorVal,
        ctor: &crate::ConstructorVal,
        rule: &RecursorRule,
        prefix: &[Expr],
        residual: &Expr,
        bad: &dyn Fn(String) -> TypeError,
    ) -> TypeResult<()> {
        // Build the constructor application. Its parameters come from the
        // recursor's own parameter binders, and its fields get fresh variables.
        let mut ctor_type = ctor.ty.clone();
        let mut ctor_args: Vec<Expr> = Vec::new();
        for index in 0..ctor.num_params as usize {
            let Expr::Forall { body, .. } = self.whnf(&ctor_type)? else {
                return Err(bad(format!(
                    "the type of `{}` has too few binders",
                    ctor.name
                )));
            };
            let arg = prefix
                .get(index)
                .cloned()
                .ok_or_else(|| bad("its type has too few parameters".to_string()))?;
            ctor_args.push(arg.clone());
            ctor_type = body.instantiate(&arg);
        }
        for _ in 0..ctor.num_fields {
            let Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } = self.whnf(&ctor_type)?
            else {
                return Err(bad(format!(
                    "the type of `{}` has too few binders",
                    ctor.name
                )));
            };
            let id = self.lctx.push(binder_name, binder_type.to_expr());
            ctor_args.push(Expr::FVar(id));
            ctor_type = body.instantiate(&Expr::FVar(id));
        }

        // `ctor_type` is now the inductive type applied to parameters and
        // indices. The indices come after the parameters.
        let (_, applied) = ctor_type.unfold_apps();
        let indices: Vec<Expr> = applied
            .into_iter()
            .skip(ctor.num_params as usize)
            .cloned()
            .collect();
        if indices.len() != rec.num_indices as usize {
            return Err(bad(format!(
                "`{}` gives {} indices and the recursor expects {}",
                ctor.name,
                indices.len(),
                rec.num_indices
            )));
        }

        let major = Expr::Const {
            name: ctor.name.clone(),
            levels: ctor
                .level_params
                .iter()
                .map(|name| Level::Param(name.clone()))
                .collect(),
        }
        .apps(ctor_args.iter().cloned());

        // Work out the type that the recursor promises for that term.
        let mut promised = residual.clone();
        for index in &indices {
            let Expr::Forall { body, .. } = self.whnf(&promised)? else {
                return Err(bad("its type has too few index binders".to_string()));
            };
            promised = body.instantiate(index);
        }
        let Expr::Forall { body, .. } = self.whnf(&promised)? else {
            return Err(bad(
                "its type has no binder for the major premise".to_string()
            ));
        };
        let promised = body.instantiate(&major);

        // And what the rule actually delivers.
        let delivered = rule
            .rhs
            .clone()
            .apps(prefix.iter().cloned())
            .apps(ctor_args[ctor.num_params as usize..].iter().cloned());
        let got = self.infer_type(&delivered)?;
        if !self.is_def_eq(&got, &promised)? {
            return Err(bad(format!(
                "the rule for `{}` delivers `{}` and the type promises `{}`",
                ctor.name,
                self.lctx.pretty(&got),
                self.lctx.pretty(&promised)
            )));
        }
        Ok(())
    }

    /// Checks that the minor premises are the ones induction requires.
    ///
    /// Chapter 5 checked that every ι rule is **type correct**. That is not
    /// enough. A recursor could offer minor premises of some other shape, keep
    /// its rules type correct, and still not be an induction principle. Then it
    /// is an axiom again, only a quieter one.
    ///
    /// So this method **derives** the minor premise that each constructor needs
    /// and compares it with the one the file declared. For a constructor
    ///
    /// ```text
    /// c : (params) → (f₁ : F₁) … (f_m : F_m) → I params idx
    /// ```
    ///
    /// the premise is
    ///
    /// ```text
    /// (f₁ : F₁) … (f_m : F_m) → (one hypothesis per recursive field)
    ///                         → motive idx (c params f₁ … f_m)
    /// ```
    ///
    /// A field is **recursive** when its own result type is the inductive type
    /// again. `Nat.succ` has one such field, so its premise gains `motive n`.
    ///
    /// The comparison uses [`TypeChecker::is_def_eq`], so a binder name or a
    /// harmless redex does not matter.
    fn check_minor_premises(
        &mut self,
        rec: &RecursorVal,
        group: &[InductiveVal],
        prefix: &[Expr],
        bad: &dyn Fn(String) -> TypeError,
    ) -> TypeResult<()> {
        let params: Vec<Expr> = prefix
            .iter()
            .take(rec.num_params as usize)
            .cloned()
            .collect();
        // One motive per type in the group, in group order.
        let motives: Vec<Expr> = prefix
            .iter()
            .skip(rec.num_params as usize)
            .take(rec.num_motives as usize)
            .cloned()
            .collect();
        if motives.len() != group.len() {
            return Err(bad("its type has too few motive binders".to_string()));
        }
        let first_minor = rec.num_params as usize + rec.num_motives as usize;

        // The minor premises run in group order, then constructor order.
        let mut slot = 0usize;
        for (group_index, inductive) in group.iter().enumerate() {
            for ctor_name in &inductive.ctors {
                let Some(Declaration::Constructor(ctor)) = self.lookup(ctor_name) else {
                    return Err(bad(format!("`{ctor_name}` is not a constructor")));
                };
                let ctor = ctor.clone();
                let Some(Expr::FVar(declared_id)) = prefix.get(first_minor + slot) else {
                    return Err(bad(format!(
                        "its type has no binder for the minor premise of `{ctor_name}`"
                    )));
                };
                let Some(declared) = self.lctx.type_of(*declared_id).cloned() else {
                    return Err(bad("a minor premise left the context".to_string()));
                };
                let derived =
                    self.derive_minor_premise(group, group_index, &ctor, &params, &motives, bad)?;
                if !self.is_def_eq(&declared, &derived)? {
                    return Err(bad(format!(
                        "the minor premise for `{}` is `{}` and induction needs `{}`",
                        ctor_name,
                        self.lctx.pretty(&declared),
                        self.lctx.pretty(&derived)
                    )));
                }
                slot += 1;
            }
        }
        Ok(())
    }

    /// Builds the minor premise that induction over one constructor needs.
    fn derive_minor_premise(
        &mut self,
        group: &[InductiveVal],
        group_index: usize,
        ctor: &ConstructorVal,
        params: &[Expr],
        motives: &[Expr],
        bad: &dyn Fn(String) -> TypeError,
    ) -> TypeResult<Expr> {
        let mark = self.lctx.len();
        let outcome = self.derive_minor_inner(group, group_index, ctor, params, motives, bad);
        self.truncate_locals(mark);
        outcome
    }

    fn derive_minor_inner(
        &mut self,
        group: &[InductiveVal],
        group_index: usize,
        ctor: &ConstructorVal,
        params: &[Expr],
        motives: &[Expr],
        bad: &dyn Fn(String) -> TypeError,
    ) -> TypeResult<Expr> {
        let ind = &group[group_index];
        let motive = &motives[group_index];
        // Fill the parameters from the recursor's own parameter binders.
        let mut ty = ctor.ty.clone();
        for param in params.iter().take(ctor.num_params as usize) {
            let Expr::Forall { body, .. } = self.whnf(&ty)? else {
                return Err(bad(format!("`{}` has too few binders", ctor.name)));
            };
            ty = body.instantiate(param);
        }

        // Open one variable per field.
        let mut fields: Vec<(Name, Expr, FVarId)> = Vec::new();
        for _ in 0..ctor.num_fields {
            let Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } = self.whnf(&ty)?
            else {
                return Err(bad(format!("`{}` has too few binders", ctor.name)));
            };
            let field_type = binder_type.to_expr();
            let id = self.lctx.push(binder_name.clone(), field_type.clone());
            fields.push((binder_name, field_type, id));
            ty = body.instantiate(&Expr::FVar(id));
        }

        // What is left is the inductive type applied to parameters and indices.
        let (_, applied) = ty.unfold_apps();
        let indices: Vec<Expr> = applied
            .into_iter()
            .skip(ind.num_params as usize)
            .cloned()
            .collect();

        let ctor_app = Expr::Const {
            name: ctor.name.clone(),
            levels: ctor
                .level_params
                .iter()
                .map(|name| Level::Param(name.clone()))
                .collect(),
        }
        .apps(params.iter().take(ctor.num_params as usize).cloned())
        .apps(fields.iter().map(|(_, _, id)| Expr::FVar(*id)));

        // The conclusion of the premise.
        let mut result = motive.clone().apps(indices.iter().cloned()).app(ctor_app);

        // One induction hypothesis per recursive field, after the fields.
        let mut hypotheses = Vec::new();
        for (_, field_type, id) in &fields {
            if let Some(hypothesis) =
                self.induction_hypothesis(group, field_type, &Expr::FVar(*id), motives)?
            {
                hypotheses.push(hypothesis);
            }
        }
        for hypothesis in hypotheses.into_iter().rev() {
            result = Expr::Forall {
                binder_name: Name::from_dotted("ih"),
                binder_type: Sub::new(hypothesis),
                body: Sub::new(result),
                info: BinderInfo::Default,
            };
        }
        // Then close the field binders, innermost first.
        for (name, field_type, id) in fields.into_iter().rev() {
            result = Expr::Forall {
                binder_name: name,
                binder_type: Sub::new(field_type),
                body: Sub::new(result.abstract_fvar(id)),
                info: BinderInfo::Default,
            };
        }
        Ok(result)
    }

    /// Returns the induction hypothesis for one field, if the field is
    /// recursive.
    ///
    /// A field of type `(xs) → I params idx` gives the hypothesis
    /// `(xs) → motive idx (field xs)`. A field whose result is anything else
    /// gives none.
    fn induction_hypothesis(
        &mut self,
        group: &[InductiveVal],
        field_type: &Expr,
        field: &Expr,
        motives: &[Expr],
    ) -> TypeResult<Option<Expr>> {
        let mark = self.lctx.len();
        let outcome = self.induction_hypothesis_inner(group, field_type, field, motives);
        self.truncate_locals(mark);
        outcome
    }

    fn induction_hypothesis_inner(
        &mut self,
        group: &[InductiveVal],
        field_type: &Expr,
        field: &Expr,
        motives: &[Expr],
    ) -> TypeResult<Option<Expr>> {
        // Strip the field's own binders.
        let mut ty = field_type.clone();
        let mut binders: Vec<(Name, Expr, FVarId)> = Vec::new();
        while let Expr::Forall {
            binder_name,
            binder_type,
            body,
            ..
        } = self.whnf(&ty)?
        {
            let inner = binder_type.to_expr();
            let id = self.lctx.push(binder_name.clone(), inner.clone());
            binders.push((binder_name, inner, id));
            ty = body.instantiate(&Expr::FVar(id));
        }

        // Is the result one of the types in the group? A mutual group has one
        // motive per type, and the hypothesis must use the right one.
        let (head, applied) = ty.unfold_apps();
        let Expr::Const { name, .. } = head else {
            return Ok(None);
        };
        let Some(group_index) = group.iter().position(|i| i.name == *name) else {
            return Ok(None);
        };
        let indices: Vec<Expr> = applied
            .into_iter()
            .skip(group[group_index].num_params as usize)
            .cloned()
            .collect();

        let applied_field = field
            .clone()
            .apps(binders.iter().map(|(_, _, id)| Expr::FVar(*id)));
        let mut result = motives[group_index]
            .clone()
            .apps(indices)
            .app(applied_field);
        for (name, binder_type, id) in binders.into_iter().rev() {
            result = Expr::Forall {
                binder_name: name,
                binder_type: Sub::new(binder_type),
                body: Sub::new(result.abstract_fvar(id)),
                info: BinderInfo::Default,
            };
        }
        Ok(Some(result))
    }

    /// Checks that a `Prop` valued inductive type does not eliminate into a
    /// larger universe.
    ///
    /// `Prop` carries no information beyond the fact that it holds, so you must
    /// not extract data from a proof. Two shapes are the exception, and Lean
    /// permits both:
    ///
    /// - no constructor at all, as in `False`
    /// - one constructor whose every field is itself a proof, as in `Eq` and
    ///   `And`
    ///
    /// Those are the subsingletons. They have at most one element, so nothing
    /// can leak.
    fn check_elimination_universe(
        &mut self,
        rec: &RecursorVal,
        ind: &crate::InductiveVal,
        prefix: &[Expr],
        bad: &dyn Fn(String) -> TypeError,
    ) -> TypeResult<()> {
        // Is the inductive type a `Prop`?
        let mut ind_type = ind.ty.clone();
        while let Expr::Forall { body, .. } = self.whnf(&ind_type)? {
            ind_type = body.to_expr();
        }
        let Expr::Sort(level) = ind_type else {
            return Ok(());
        };
        if !level.normalize().is_zero() {
            return Ok(());
        }
        if self.is_subsingleton(ind)? {
            return Ok(());
        }

        // Where does the motive land?
        let Some(Expr::FVar(motive)) = prefix.get(rec.num_params as usize) else {
            return Ok(());
        };
        let Some(motive_type) = self.lctx.type_of(*motive).cloned() else {
            return Ok(());
        };
        let mut result = motive_type;
        while let Expr::Forall { body, .. } = self.whnf(&result)? {
            result = body.to_expr();
        }
        if let Expr::Sort(motive_level) = result
            && !motive_level.normalize().is_zero()
        {
            return Err(bad(format!(
                "`{}` is a Prop with more than one element, so it must not \
                 eliminate into `Sort {motive_level}`",
                ind.name
            )));
        }
        Ok(())
    }

    /// Returns `true` if the inductive type has at most one element.
    fn is_subsingleton(&mut self, ind: &crate::InductiveVal) -> TypeResult<bool> {
        let [only] = ind.ctors.as_slice() else {
            // No constructor at all, as in `False`.
            return Ok(ind.ctors.is_empty());
        };
        let Some(Declaration::Constructor(ctor)) = self.lookup(only) else {
            return Ok(false);
        };
        let ctor = ctor.clone();
        let mark = self.lctx.len();
        let outcome = self.every_field_is_a_proof(&ctor);
        self.truncate_locals(mark);
        outcome
    }

    /// Returns `true` if the constructor makes its type a subsingleton.
    ///
    /// A field is acceptable when either of two things holds:
    ///
    /// 1. Its type is itself a `Prop`, so the field carries no data.
    /// 2. The field appears among the **indices** of the result type. Then the
    ///    index already pins the field down, so the field carries nothing that
    ///    the type does not already say.
    ///
    /// Rule 2 is the one that `Acc` needs, and leaving it out is a false
    /// rejection. `Acc.intro : (x : α) → (∀ y, r y x → Acc r y) → Acc r x` has
    /// a data field `x`, and `x` is the index of `Acc r x`. Lean permits
    /// `Acc.rec` to eliminate into any sort, and the Lean prelude relies on it.
    fn every_field_is_a_proof(&mut self, ctor: &crate::ConstructorVal) -> TypeResult<bool> {
        let mut ty = ctor.ty.clone();
        for _ in 0..ctor.num_params {
            let Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } = self.whnf(&ty)?
            else {
                return Ok(false);
            };
            let id = self.lctx.push(binder_name, binder_type.to_expr());
            ty = body.instantiate(&Expr::FVar(id));
        }

        // Open every field, and remember which ones carry data.
        let mut data_fields: Vec<FVarId> = Vec::new();
        for _ in 0..ctor.num_fields {
            let Expr::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } = self.whnf(&ty)?
            else {
                return Ok(false);
            };
            let level = self.infer_sort(&binder_type)?;
            let id = self.lctx.push(binder_name, binder_type.to_expr());
            if !level.normalize().is_zero() {
                data_fields.push(id);
            }
            ty = body.instantiate(&Expr::FVar(id));
        }
        if data_fields.is_empty() {
            return Ok(true);
        }

        // What is left is the inductive type applied to parameters and indices.
        let (_, applied) = ty.unfold_apps();
        let indices: Vec<Expr> = applied
            .into_iter()
            .skip(ctor.num_params as usize)
            .cloned()
            .collect();

        // Every data field must be pinned down by an index.
        Ok(data_fields
            .iter()
            .all(|id| indices.iter().any(|index| mentions_fvar(index, *id))))
    }

    /// Checks one declaration: its type is a type, and its value has that type.    /// Checks one declaration: its type is a type, and its value has that type.
    ///
    /// This is the entry point of the level 1 checkpoint in `docs/ROADMAP.md`.
    pub fn check_declaration(&mut self, decl: &Declaration) -> TypeResult<()> {
        // Every declaration gets the whole budget, so one heavy neighbour does
        // not starve the rest of the file.
        self.fuel = self.budget;
        // And fresh caches. An answer about a free variable of the last
        // declaration means nothing here.
        self.whnf_cache.clear();
        self.def_eq_cache.clear();
        if self.env.contains(decl.name()) {
            return Err(TypeError::DuplicateDeclaration(decl.name().clone()));
        }
        self.check_universes(decl)?;
        self.check_safety(decl)?;
        self.infer_sort(decl.ty())?;
        // A constructor and a recursor are where a user hands the kernel a new
        // rule, so they are where the kernel must push back.
        match decl {
            Declaration::Constructor(ctor) => self.check_positivity(ctor)?,
            Declaration::Recursor(rec) => self.check_recursor(rec)?,
            _ => {}
        }
        if let Some(value) = declaration_value(decl) {
            let got = self.infer_type(value)?;
            if !self.is_def_eq(&got, decl.ty())? {
                return Err(TypeError::mismatch(value, decl.ty().clone(), got));
            }
        }
        Ok(())
    }
}

/// Returns `true` if `id` occurs anywhere in `e`.
fn mentions_fvar(e: &Expr, id: FVarId) -> bool {
    match e {
        Expr::FVar(found) => *found == id,
        Expr::App { fun, arg } => mentions_fvar(fun, id) || mentions_fvar(arg, id),
        Expr::Lam {
            binder_type, body, ..
        }
        | Expr::Forall {
            binder_type, body, ..
        } => mentions_fvar(binder_type, id) || mentions_fvar(body, id),
        Expr::Let {
            binder_type,
            value,
            body,
            ..
        } => mentions_fvar(binder_type, id) || mentions_fvar(value, id) || mentions_fvar(body, id),
        Expr::Proj(proj) => mentions_fvar(&proj.value, id),
        Expr::BVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Const { .. } | Expr::Lit(_) => false,
    }
}

/// Returns the value that a declaration must be checked against, if it has one.
///
/// An `Opaque` value is included. Opacity hides a value from the δ rule. It does
/// not excuse the value from being correct.
fn declaration_value(decl: &Declaration) -> Option<&Expr> {
    match decl {
        Declaration::Definition(d) => Some(&d.value),
        Declaration::Theorem(d) => Some(&d.value),
        Declaration::Opaque(d) => Some(&d.value),
        _ => None,
    }
}
