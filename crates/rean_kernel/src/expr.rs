//! Kernel terms and the three operations that move a variable.
//!
//! # Why de Bruijn indices
//!
//! A bound variable in [`Expr`] has no name. It has a number: the count of
//! binders between the use and the binder that owns it.
//!
//! ```text
//! fun x => fun y => x        becomes   Lam (Lam (BVar 1))
//! fun x => fun y => y        becomes   Lam (Lam (BVar 0))
//! ```
//!
//! Two terms that differ only in the names of their bound variables therefore
//! become the same `Expr`. A type checker compares types on every step, so this
//! property removes a whole class of bugs and a whole class of slow paths.
//!
//! The cost is that substitution must renumber. [`Expr::lift`] and
//! [`Expr::instantiate`] do that work.
//!
//! # Why free variables keep a separate variant
//!
//! The elaborator opens a binder to look inside the body. It replaces the bound
//! variable with a [`Expr::FVar`], which carries an identifier and never
//! changes number. The elaborator can then walk the body with no renumbering at
//! all. [`Expr::abstract_fvar`] closes the binder again at the end.

use crate::level::Level;
use rean_core::Name;
use std::fmt;
use std::sync::Arc;

/// The identifier of a free variable in the local context.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FVarId(pub u64);

/// The identifier of a metavariable, which is a hole that unification fills.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct MVarId(pub u64);

/// How the elaborator treats an argument at a call site.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum BinderInfo {
    /// `(x : A)`. The caller writes the argument.
    #[default]
    Default,
    /// `{x : A}`. The elaborator infers the argument from the other arguments.
    Implicit,
    /// `⦃x : A⦄`. Like `Implicit`, but the elaborator waits for the next
    /// explicit argument before it infers.
    StrictImplicit,
    /// `[x : A]`. The elaborator searches the instances for the argument.
    InstImplicit,
}

impl BinderInfo {
    /// Returns the pair of brackets that the source uses for this binder.
    pub fn brackets(&self) -> (&'static str, &'static str) {
        match self {
            BinderInfo::Default => ("(", ")"),
            BinderInfo::Implicit => ("{", "}"),
            BinderInfo::StrictImplicit => ("⦃", "⦄"),
            BinderInfo::InstImplicit => ("[", "]"),
        }
    }
}

/// A literal that the kernel knows without a definition.
///
/// `Nat` keeps the digits as text, because a Lean `Nat` has no upper bound.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Literal {
    Nat(Arc<str>),
    Str(Arc<str>),
}

/// A projection out of a structure, such as the `.1` of `p.1`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Proj {
    /// The structure that owns the field, such as `Prod`.
    pub structure: Name,
    /// The position of the field, counted from 0.
    pub index: u32,
    /// The term that the projection reads.
    pub value: Sub,
}

/// A subterm, and the one fact about it that the kernel asks for most.
///
/// `loose` is one more than the largest **loose** bound variable index inside,
/// or zero when there is none. So `loose == 0` means "closed", and
/// `loose <= depth` means "nothing in here points at or past `depth`".
///
/// That one number turns the central operation of the kernel from a walk into a
/// test. Substitution used to traverse a subterm to discover that nothing
/// changed, and `Expr::instantiate_at` was the heaviest frame in a profile of
/// the Lean prelude. Now it asks `loose` and stops.
///
/// The number costs nothing to keep. Every node computes it from its children
/// in constant time, so building a term pays O(1) per node rather than O(size).
/// The real Lean kernel stores the same number in every expression header.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Sub {
    expr: Arc<Expr>,
    loose: u32,
    size: u32,
    hash: u64,
}

impl Sub {
    /// Wraps a term, computing its loose range from its children.
    pub fn new(expr: Expr) -> Sub {
        let loose = loose_range(&expr);
        let size = size_range(&expr);
        let hash = hash_range(&expr);
        Sub {
            expr: Arc::new(expr),
            loose,
            size,
            hash,
        }
    }

    /// Returns one more than the largest loose bound variable index, or zero.
    pub fn loose(&self) -> u32 {
        self.loose
    }

    /// Returns the node count of the term, saturated at [`u32::MAX`].
    pub fn size(&self) -> u32 {
        self.size
    }

    /// Returns the cached hash of the term.
    pub fn hash(&self) -> u64 {
        self.hash
    }

    /// Returns a copy of the term inside.
    ///
    /// `Sub` is `Clone`, so `(*sub).clone()` would copy the wrapper and not the
    /// term. This method says which one is meant.
    pub fn to_expr(&self) -> Expr {
        (*self.expr).clone()
    }

    /// Returns `true` if nothing inside points at or past `depth`.
    fn settled_at(&self, depth: u32) -> bool {
        self.loose <= depth
    }

    /// [`Expr::lift_opt`] for a subterm, with the O(1) skip.
    fn lift_opt(&self, cutoff: u32, amount: u32) -> Option<Sub> {
        // Nothing in here points at or past the cutoff, so nothing moves.
        if self.settled_at(cutoff) {
            return None;
        }
        self.expr.lift_opt(cutoff, amount).map(Sub::new)
    }

    /// [`Expr::instantiate_at`] for a subterm, with the O(1) skip.
    fn instantiate_at(&self, depth: u32, value: &Expr) -> Option<Sub> {
        // The binder being discharged is at `depth`, and nothing in here
        // reaches it. This test is why the cached range exists.
        if self.settled_at(depth) {
            return None;
        }
        self.expr.instantiate_at(depth, value).map(Sub::new)
    }

    /// [`Expr::abstract_at`] for a subterm.
    ///
    /// There is no skip here. The cached range says where the **bound**
    /// variables reach, and this operation looks for a **free** one, so the
    /// number says nothing about it.
    fn abstract_at(&self, depth: u32, fvar: FVarId) -> Option<Sub> {
        self.expr.abstract_at(depth, fvar).map(Sub::new)
    }
}

impl std::ops::Deref for Sub {
    type Target = Expr;

    fn deref(&self) -> &Expr {
        &self.expr
    }
}

/// Computes the loose range of one node from its children, in constant time.
///
/// Going under a binder discharges index zero, so the body's range drops by
/// one.
fn loose_range(e: &Expr) -> u32 {
    match e {
        Expr::BVar(index) => index + 1,
        Expr::App { fun, arg } => fun.loose.max(arg.loose),
        Expr::Lam {
            binder_type, body, ..
        }
        | Expr::Forall {
            binder_type, body, ..
        } => binder_type.loose.max(body.loose.saturating_sub(1)),
        Expr::Let {
            binder_type,
            value,
            body,
            ..
        } => binder_type
            .loose
            .max(value.loose)
            .max(body.loose.saturating_sub(1)),
        Expr::Proj(proj) => proj.value.loose,
        Expr::FVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Const { .. } | Expr::Lit(_) => 0,
    }
}

/// Mixes a value into a hash. This is the FNV-1a step.
///
/// The kernel needs a hash that is cheap to compute, not one that resists an
/// attack, so a multiply and an exclusive or are enough.
fn mix(state: u64, value: u64) -> u64 {
    (state ^ value).wrapping_mul(0x0000_0100_0000_01b3)
}

/// Combines two hashes into one, for a cache whose key is a pair of terms.
///
/// The result depends on the order, which is right: [`TypeChecker::is_def_eq`]
/// stores the two sides as it received them.
///
/// [`TypeChecker::is_def_eq`]: crate::typeck::TypeChecker::is_def_eq
pub fn mix_hashes(first: u64, second: u64) -> u64 {
    mix(mix(0xcbf2_9ce4_8422_2325, first), second)
}

/// Hashes a name by its last part and its length, and allocates nothing.
fn hash_name(name: &Name) -> u64 {
    let mut state = mix(0xcbf2_9ce4_8422_2325, name.len() as u64);
    if let Some(last) = name.last_str() {
        for byte in last.as_bytes() {
            state = mix(state, *byte as u64);
        }
    }
    state
}

/// Hashes a term, in constant time, from the hashes of its children.
///
/// This is the third number every node caches, and it exists so that the
/// checker can **look a term up**. See chapter 10.
///
/// The hash is a **filter and not a decision.** Two different terms can share a
/// hash, so a cache that finds an entry must still confirm it with
/// [`Expr::alpha_eq`]. A proof checker may not be probably right.
///
/// So the hash may be coarse, and here it is coarse on purpose in two places.
/// [`Expr::alpha_eq`] compares a universe level by [`Level::is_equiv`] and not
/// by shape, and it ignores a binder name. A hash that read the shape of a level
/// would give two equal terms two different hashes, and every lookup of them
/// would miss. So this skips both.
fn hash_range(e: &Expr) -> u64 {
    match e {
        Expr::BVar(index) => mix(1, *index as u64),
        Expr::FVar(id) => mix(2, id.0),
        Expr::MVar(id) => mix(3, id.0),
        // The levels are compared by equivalence, so the hash leaves them out.
        Expr::Sort(_) => 4,
        Expr::Const { name, levels } => mix(mix(5, hash_name(name)), levels.len() as u64),
        Expr::App { fun, arg } => mix(mix(6, fun.hash), arg.hash),
        // The binder name is not compared, so the hash leaves it out.
        Expr::Lam {
            binder_type,
            body,
            info,
            ..
        } => mix(mix(mix(7, binder_type.hash), body.hash), *info as u64),
        Expr::Forall {
            binder_type,
            body,
            info,
            ..
        } => mix(mix(mix(8, binder_type.hash), body.hash), *info as u64),
        Expr::Let {
            binder_type,
            value,
            body,
            ..
        } => mix(mix(mix(9, binder_type.hash), value.hash), body.hash),
        Expr::Lit(Literal::Nat(text)) | Expr::Lit(Literal::Str(text)) => {
            let mut state = mix(10, text.len() as u64);
            for byte in text.as_bytes() {
                state = mix(state, *byte as u64);
            }
            state
        }
        Expr::Proj(proj) => mix(
            mix(mix(11, hash_name(&proj.structure)), proj.index as u64),
            proj.value.hash,
        ),
    }
}

/// Counts the nodes of a term, in constant time, from the counts of its
/// children.
///
/// This is the second number every node caches, and it exists for the same
/// reason as the first. The checker charges fuel by the size of each term a
/// reduction produces, so it asks for this count after every single step.
/// A walk of the term would make that accounting cost as much as the reduction.
///
/// The count saturates. A term that shares subterms through [`Arc`] is small in
/// memory and can still be enormous as a tree, and the caller clamps the number
/// to a limit anyway.
fn size_range(e: &Expr) -> u32 {
    match e {
        Expr::App { fun, arg } => 1u32.saturating_add(fun.size).saturating_add(arg.size),
        Expr::Lam {
            binder_type, body, ..
        }
        | Expr::Forall {
            binder_type, body, ..
        } => 1u32
            .saturating_add(binder_type.size)
            .saturating_add(body.size),
        Expr::Let {
            binder_type,
            value,
            body,
            ..
        } => 1u32
            .saturating_add(binder_type.size)
            .saturating_add(value.size)
            .saturating_add(body.size),
        Expr::Proj(proj) => 1u32.saturating_add(proj.value.size),
        Expr::BVar(_)
        | Expr::FVar(_)
        | Expr::MVar(_)
        | Expr::Sort(_)
        | Expr::Const { .. }
        | Expr::Lit(_) => 1,
    }
}

/// A kernel term.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    /// A bound variable, by de Bruijn index.
    BVar(u32),
    /// A free variable from the local context.
    FVar(FVarId),
    /// A hole that unification must fill.
    MVar(MVarId),
    /// A universe, such as `Prop` or `Type 3`.
    Sort(Level),
    /// A name from the environment, with its universe arguments.
    Const { name: Name, levels: Vec<Level> },
    /// An application of one argument. `f x y` is `App(App(f, x), y)`.
    App { fun: Sub, arg: Sub },
    /// A lambda, such as `fun (x : A) => b`.
    Lam {
        binder_name: Name,
        binder_type: Sub,
        body: Sub,
        info: BinderInfo,
    },
    /// A function type, such as `(x : A) → B`. `A → B` is the case where `B`
    /// does not use `x`.
    Forall {
        binder_name: Name,
        binder_type: Sub,
        body: Sub,
        info: BinderInfo,
    },
    /// A local definition, such as `let x : A := v; b`.
    Let {
        binder_name: Name,
        binder_type: Sub,
        value: Sub,
        body: Sub,
    },
    /// A literal.
    Lit(Literal),
    /// A projection out of a structure.
    Proj(Proj),
}

impl Expr {
    // --- constructors ---------------------------------------------------

    /// Builds a bound variable.
    pub fn bvar(index: u32) -> Expr {
        Expr::BVar(index)
    }

    /// Builds `Sort n`. `Sort 0` is `Prop` and `Sort 1` is `Type`.
    pub fn sort(level: Level) -> Expr {
        Expr::Sort(level)
    }

    /// Builds `Prop`.
    pub fn prop() -> Expr {
        Expr::Sort(Level::Zero)
    }

    /// Builds `Type n`. The kernel stores `Type n` as `Sort (n + 1)`.
    pub fn type_(n: u32) -> Expr {
        Expr::Sort(Level::of_nat(n + 1))
    }

    /// Builds a reference to a name in the environment.
    pub fn const_(name: impl Into<Name>, levels: Vec<Level>) -> Expr {
        Expr::Const {
            name: name.into(),
            levels,
        }
    }

    /// Applies `self` to one argument.
    pub fn app(self, arg: Expr) -> Expr {
        Expr::App {
            fun: Sub::new(self),
            arg: Sub::new(arg),
        }
    }

    /// Applies `self` to every argument in order.
    pub fn apps(self, args: impl IntoIterator<Item = Expr>) -> Expr {
        args.into_iter().fold(self, Expr::app)
    }

    /// Builds a lambda with an explicit binder.
    pub fn lam(binder_name: impl Into<Name>, binder_type: Expr, body: Expr) -> Expr {
        Expr::Lam {
            binder_name: binder_name.into(),
            binder_type: Sub::new(binder_type),
            body: Sub::new(body),
            info: BinderInfo::Default,
        }
    }

    /// Builds a function type with an explicit binder.
    pub fn forall(binder_name: impl Into<Name>, binder_type: Expr, body: Expr) -> Expr {
        Expr::Forall {
            binder_name: binder_name.into(),
            binder_type: Sub::new(binder_type),
            body: Sub::new(body),
            info: BinderInfo::Default,
        }
    }

    /// Builds `A → B`, which is a `Forall` whose body ignores the binder.
    pub fn arrow(from: Expr, to: Expr) -> Expr {
        // The body must move under one new binder, so it needs a lift.
        Expr::forall("a", from, to.lift(0, 1))
    }

    /// Builds a `let`.
    pub fn let_(binder_name: impl Into<Name>, binder_type: Expr, value: Expr, body: Expr) -> Expr {
        Expr::Let {
            binder_name: binder_name.into(),
            binder_type: Sub::new(binder_type),
            value: Sub::new(value),
            body: Sub::new(body),
        }
    }

    /// Builds a natural number literal from its digits.
    pub fn nat(digits: impl Into<Arc<str>>) -> Expr {
        Expr::Lit(Literal::Nat(digits.into()))
    }

    /// Builds a string literal.
    pub fn str(value: impl Into<Arc<str>>) -> Expr {
        Expr::Lit(Literal::Str(value.into()))
    }

    // --- shape ----------------------------------------------------------

    /// Splits an application into the head and the list of arguments.
    ///
    /// `f x y` gives `(f, [x, y])`. A term that is not an application gives
    /// itself and an empty list.
    pub fn unfold_apps(&self) -> (&Expr, Vec<&Expr>) {
        let mut head = self;
        let mut args = Vec::new();
        while let Expr::App { fun, arg } = head {
            args.push(&**arg);
            head = fun;
        }
        args.reverse();
        (head, args)
    }

    /// Counts the nodes of `self`, and stops at `limit`.
    ///
    /// A reduction step can make a term **larger**, so a budget that counts
    /// steps does not bound the work. Charging a step by the size of what it
    /// produced does.
    ///
    /// Every subterm caches its own count, so this costs O(1) and not a walk of
    /// the term. The checker asks for the count after every reduction step, and
    /// a walk made the accounting as expensive as the work it accounts for.
    ///
    /// The count stops at `limit` for a reason. An `Expr` shares its subterms
    /// through [`Arc`], so a term that is small in memory can be enormous as a
    /// tree.
    pub fn size_up_to(&self, limit: u32) -> u32 {
        size_range(self).min(limit)
    }

    /// Returns the hash of `self`, in constant time.
    ///
    /// Two terms that [`Expr::alpha_eq`] accepts have the same hash. Two terms
    /// with the same hash are **not** necessarily equal, so a caller that finds
    /// a term by its hash must confirm the find. See [`hash_range`].
    pub fn hash_value(&self) -> u64 {
        hash_range(self)
    }

    /// Returns `true` if a bound variable in `self` points outside `self`.
    ///
    /// A closed term has no loose variable. The kernel only accepts closed
    /// terms at the top level.
    pub fn has_loose_bvars(&self) -> bool {
        self.has_loose_bvars_from(0)
    }

    /// Returns `true` if the loose bound variable `index` occurs in `self`.
    ///
    /// Call this method on the body of a binder with `index` of 0 to ask one
    /// question: does the body use the binder? A `Forall` whose body does not
    /// use its binder is a plain arrow `A → B`.
    pub fn has_loose_bvar(&self, index: u32) -> bool {
        self.has_loose_bvar_at(index, 0)
    }

    fn has_loose_bvar_at(&self, index: u32, depth: u32) -> bool {
        match self {
            Expr::BVar(i) => *i == index + depth,
            Expr::App { fun, arg } => {
                fun.has_loose_bvar_at(index, depth) || arg.has_loose_bvar_at(index, depth)
            }
            Expr::Lam {
                binder_type, body, ..
            }
            | Expr::Forall {
                binder_type, body, ..
            } => {
                binder_type.has_loose_bvar_at(index, depth)
                    || body.has_loose_bvar_at(index, depth + 1)
            }
            Expr::Let {
                binder_type,
                value,
                body,
                ..
            } => {
                binder_type.has_loose_bvar_at(index, depth)
                    || value.has_loose_bvar_at(index, depth)
                    || body.has_loose_bvar_at(index, depth + 1)
            }
            Expr::Proj(proj) => proj.value.has_loose_bvar_at(index, depth),
            Expr::FVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Const { .. } | Expr::Lit(_) => {
                false
            }
        }
    }

    fn has_loose_bvars_from(&self, depth: u32) -> bool {
        match self {
            Expr::BVar(index) => *index >= depth,
            Expr::App { fun, arg } => {
                fun.has_loose_bvars_from(depth) || arg.has_loose_bvars_from(depth)
            }
            Expr::Lam {
                binder_type, body, ..
            }
            | Expr::Forall {
                binder_type, body, ..
            } => binder_type.has_loose_bvars_from(depth) || body.has_loose_bvars_from(depth + 1),
            Expr::Let {
                binder_type,
                value,
                body,
                ..
            } => {
                binder_type.has_loose_bvars_from(depth)
                    || value.has_loose_bvars_from(depth)
                    || body.has_loose_bvars_from(depth + 1)
            }
            Expr::Proj(proj) => proj.value.has_loose_bvars_from(depth),
            Expr::FVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Const { .. } | Expr::Lit(_) => {
                false
            }
        }
    }

    /// Replaces each universe parameter of `self` with the level at the same
    /// position in `args`.
    ///
    /// The δ rule needs this method. A call site writes `List.{0}`, and the
    /// stored value of `List` speaks about `u`, so the value must take the `0`
    /// before the checker uses it.
    pub fn instantiate_levels(&self, params: &[Name], args: &[Level]) -> Expr {
        if params.is_empty() {
            return self.clone();
        }
        match self {
            Expr::Sort(level) => Expr::Sort(level.substitute(params, args)),
            Expr::Const { name, levels } => Expr::Const {
                name: name.clone(),
                levels: levels.iter().map(|l| l.substitute(params, args)).collect(),
            },
            Expr::App { fun, arg } => Expr::App {
                fun: Sub::new(fun.instantiate_levels(params, args)),
                arg: Sub::new(arg.instantiate_levels(params, args)),
            },
            Expr::Lam {
                binder_name,
                binder_type,
                body,
                info,
            } => Expr::Lam {
                binder_name: binder_name.clone(),
                binder_type: Sub::new(binder_type.instantiate_levels(params, args)),
                body: Sub::new(body.instantiate_levels(params, args)),
                info: *info,
            },
            Expr::Forall {
                binder_name,
                binder_type,
                body,
                info,
            } => Expr::Forall {
                binder_name: binder_name.clone(),
                binder_type: Sub::new(binder_type.instantiate_levels(params, args)),
                body: Sub::new(body.instantiate_levels(params, args)),
                info: *info,
            },
            Expr::Let {
                binder_name,
                binder_type,
                value,
                body,
            } => Expr::Let {
                binder_name: binder_name.clone(),
                binder_type: Sub::new(binder_type.instantiate_levels(params, args)),
                value: Sub::new(value.instantiate_levels(params, args)),
                body: Sub::new(body.instantiate_levels(params, args)),
            },
            Expr::Proj(proj) => Expr::Proj(Proj {
                structure: proj.structure.clone(),
                index: proj.index,
                value: Sub::new(proj.value.instantiate_levels(params, args)),
            }),
            other => other.clone(),
        }
    }

    /// Adds every constant name in `self` to `out`.
    ///
    /// A driver uses this to see what a declaration depends on, so that it can
    /// tell a real failure from one that only rests on an earlier failure.
    pub fn collect_constants(&self, out: &mut Vec<Name>) {
        match self {
            Expr::Const { name, .. } => {
                if !out.contains(name) {
                    out.push(name.clone());
                }
            }
            Expr::App { fun, arg } => {
                fun.collect_constants(out);
                arg.collect_constants(out);
            }
            Expr::Lam {
                binder_type, body, ..
            }
            | Expr::Forall {
                binder_type, body, ..
            } => {
                binder_type.collect_constants(out);
                body.collect_constants(out);
            }
            Expr::Let {
                binder_type,
                value,
                body,
                ..
            } => {
                binder_type.collect_constants(out);
                value.collect_constants(out);
                body.collect_constants(out);
            }
            Expr::Proj(proj) => {
                if !out.contains(&proj.structure) {
                    out.push(proj.structure.clone());
                }
                proj.value.collect_constants(out);
            }
            Expr::BVar(_) | Expr::FVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Lit(_) => {}
        }
    }

    /// Adds every universe parameter name in `self` to `out`.
    ///
    /// A declaration must list every parameter that its type and its value
    /// use. Anything else is a free universe variable, and a free universe
    /// variable has no meaning.
    pub fn collect_level_params(&self, out: &mut Vec<Name>) {
        match self {
            Expr::Sort(level) => level.collect_params(out),
            Expr::Const { levels, .. } => {
                for level in levels {
                    level.collect_params(out);
                }
            }
            Expr::App { fun, arg } => {
                fun.collect_level_params(out);
                arg.collect_level_params(out);
            }
            Expr::Lam {
                binder_type, body, ..
            }
            | Expr::Forall {
                binder_type, body, ..
            } => {
                binder_type.collect_level_params(out);
                body.collect_level_params(out);
            }
            Expr::Let {
                binder_type,
                value,
                body,
                ..
            } => {
                binder_type.collect_level_params(out);
                value.collect_level_params(out);
                body.collect_level_params(out);
            }
            Expr::Proj(proj) => proj.value.collect_level_params(out),
            Expr::BVar(_) | Expr::FVar(_) | Expr::MVar(_) | Expr::Lit(_) => {}
        }
    }

    // --- comparison ------------------------------------------------------

    /// Returns `true` if `self` and `other` are the same term up to binder
    /// names.
    ///
    /// `Expr` keeps `binder_name` for the printer only. The de Bruijn index
    /// already carries the meaning, so a comparison must skip that field.
    /// The derived `==` does not skip it:
    ///
    /// ```
    /// use rean_kernel::Expr;
    /// let nat = Expr::const_("Nat", vec![]);
    /// let with_x = Expr::lam("x", nat.clone(), Expr::bvar(0));
    /// let with_y = Expr::lam("y", nat.clone(), Expr::bvar(0));
    /// assert!(with_x != with_y);
    /// assert!(with_x.alpha_eq(&with_y));
    /// ```
    ///
    /// This method still compares [`BinderInfo`]. Whether the kernel should
    /// ignore that field as well is a separate question, and chapter 2 revisits
    /// it.
    pub fn alpha_eq(&self, other: &Expr) -> bool {
        match (self, other) {
            (Expr::BVar(a), Expr::BVar(b)) => a == b,
            (Expr::FVar(a), Expr::FVar(b)) => a == b,
            (Expr::MVar(a), Expr::MVar(b)) => a == b,
            (Expr::Sort(a), Expr::Sort(b)) => a.is_equiv(b),
            (
                Expr::Const {
                    name: n1,
                    levels: l1,
                },
                Expr::Const {
                    name: n2,
                    levels: l2,
                },
            ) => n1 == n2 && l1.len() == l2.len() && l1.iter().zip(l2).all(|(a, b)| a.is_equiv(b)),
            (Expr::App { fun: f1, arg: a1 }, Expr::App { fun: f2, arg: a2 }) => {
                f1.alpha_eq(f2) && a1.alpha_eq(a2)
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
            ) => i1 == i2 && t1.alpha_eq(t2) && b1.alpha_eq(b2),
            (
                Expr::Let {
                    binder_type: t1,
                    value: v1,
                    body: b1,
                    ..
                },
                Expr::Let {
                    binder_type: t2,
                    value: v2,
                    body: b2,
                    ..
                },
            ) => t1.alpha_eq(t2) && v1.alpha_eq(v2) && b1.alpha_eq(b2),
            (Expr::Lit(a), Expr::Lit(b)) => a == b,
            (Expr::Proj(a), Expr::Proj(b)) => {
                a.structure == b.structure && a.index == b.index && a.value.alpha_eq(&b.value)
            }
            _ => false,
        }
    }

    // --- the three variable operations -----------------------------------

    /// Adds `amount` to every bound variable whose index is at least `cutoff`.
    ///
    /// A term moves under a new binder. Its loose variables must then count one
    /// binder more. This method does that renumber.
    pub fn lift(&self, cutoff: u32, amount: u32) -> Expr {
        if amount == 0 || loose_range(self) <= cutoff {
            return self.clone();
        }
        self.lift_opt(cutoff, amount)
            .unwrap_or_else(|| self.clone())
    }

    /// The worker for [`Expr::lift`]. `None` means "nothing changed".
    ///
    /// Returning `None` instead of a rebuilt copy is the whole performance
    /// story of this module. A profile of the Lean prelude showed
    /// `Arc<Expr>::drop_slow` as the single heaviest frame, far above the
    /// substitution itself: the old code rebuilt every node of every subterm,
    /// even where nothing changed, and then dropped the lot.
    ///
    /// With `None`, an unchanged subterm keeps its existing `Arc`, so the cost
    /// is one reference count bump instead of a deep copy and a deep drop.
    fn lift_opt(&self, cutoff: u32, amount: u32) -> Option<Expr> {
        match self {
            Expr::BVar(index) if *index >= cutoff => Some(Expr::BVar(index + amount)),
            Expr::App { fun, arg } => {
                let new_fun = fun.lift_opt(cutoff, amount);
                let new_arg = arg.lift_opt(cutoff, amount);
                rebuild_app(fun, arg, new_fun, new_arg)
            }
            Expr::Lam {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let new_type = binder_type.lift_opt(cutoff, amount);
                let new_body = body.lift_opt(cutoff + 1, amount);
                rebuild_binder(
                    true,
                    binder_name,
                    binder_type,
                    body,
                    *info,
                    new_type,
                    new_body,
                )
            }
            Expr::Forall {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let new_type = binder_type.lift_opt(cutoff, amount);
                let new_body = body.lift_opt(cutoff + 1, amount);
                rebuild_binder(
                    false,
                    binder_name,
                    binder_type,
                    body,
                    *info,
                    new_type,
                    new_body,
                )
            }
            Expr::Let {
                binder_name,
                binder_type,
                value,
                body,
            } => {
                let new_type = binder_type.lift_opt(cutoff, amount);
                let new_value = value.lift_opt(cutoff, amount);
                let new_body = body.lift_opt(cutoff + 1, amount);
                rebuild_let(
                    binder_name,
                    binder_type,
                    value,
                    body,
                    new_type,
                    new_value,
                    new_body,
                )
            }
            Expr::Proj(proj) => proj
                .value
                .lift_opt(cutoff, amount)
                .map(|value| rebuild_proj(proj, value)),
            _ => None,
        }
    }

    /// Replaces the bound variable `0` of `self` with `value`.
    ///
    /// Call this method on the body of a binder, not on the binder. A beta
    /// step is `Lam(body).instantiate(arg)`, which [`Expr::beta`] does.
    pub fn instantiate(&self, value: &Expr) -> Expr {
        if loose_range(self) == 0 {
            // A closed term has no binder to discharge.
            return self.clone();
        }
        self.instantiate_at(0, value)
            .unwrap_or_else(|| self.clone())
    }

    /// The worker for [`Expr::instantiate`]. `None` means "nothing changed".
    ///
    /// See [`Expr::lift_opt`] for why it returns an `Option`.
    fn instantiate_at(&self, depth: u32, value: &Expr) -> Option<Expr> {
        match self {
            // This use points at the binder that disappears.
            Expr::BVar(index) if *index == depth => Some(value.lift(0, depth)),
            // This use points further out, so one binder less now stands
            // between.
            Expr::BVar(index) if *index > depth => Some(Expr::BVar(index - 1)),
            Expr::App { fun, arg } => {
                let new_fun = fun.instantiate_at(depth, value);
                let new_arg = arg.instantiate_at(depth, value);
                rebuild_app(fun, arg, new_fun, new_arg)
            }
            Expr::Lam {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let new_type = binder_type.instantiate_at(depth, value);
                let new_body = body.instantiate_at(depth + 1, value);
                rebuild_binder(
                    true,
                    binder_name,
                    binder_type,
                    body,
                    *info,
                    new_type,
                    new_body,
                )
            }
            Expr::Forall {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let new_type = binder_type.instantiate_at(depth, value);
                let new_body = body.instantiate_at(depth + 1, value);
                rebuild_binder(
                    false,
                    binder_name,
                    binder_type,
                    body,
                    *info,
                    new_type,
                    new_body,
                )
            }
            Expr::Let {
                binder_name,
                binder_type,
                value: bound,
                body,
            } => {
                let new_type = binder_type.instantiate_at(depth, value);
                let new_value = bound.instantiate_at(depth, value);
                let new_body = body.instantiate_at(depth + 1, value);
                rebuild_let(
                    binder_name,
                    binder_type,
                    bound,
                    body,
                    new_type,
                    new_value,
                    new_body,
                )
            }
            Expr::Proj(proj) => proj
                .value
                .instantiate_at(depth, value)
                .map(|inner| rebuild_proj(proj, inner)),
            _ => None,
        }
    }

    /// Replaces the free variable `fvar` with a new bound variable `0`.
    ///
    /// This operation is the reverse of [`Expr::instantiate`]. The elaborator
    /// uses it to close a binder after it finishes the body.
    pub fn abstract_fvar(&self, fvar: FVarId) -> Expr {
        self.abstract_at(0, fvar).unwrap_or_else(|| self.clone())
    }

    /// The worker for [`Expr::abstract_fvar`]. `None` means "nothing changed".
    fn abstract_at(&self, depth: u32, fvar: FVarId) -> Option<Expr> {
        match self {
            Expr::FVar(id) if *id == fvar => Some(Expr::BVar(depth)),
            Expr::App { fun, arg } => {
                let new_fun = fun.abstract_at(depth, fvar);
                let new_arg = arg.abstract_at(depth, fvar);
                rebuild_app(fun, arg, new_fun, new_arg)
            }
            Expr::Lam {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let new_type = binder_type.abstract_at(depth, fvar);
                let new_body = body.abstract_at(depth + 1, fvar);
                rebuild_binder(
                    true,
                    binder_name,
                    binder_type,
                    body,
                    *info,
                    new_type,
                    new_body,
                )
            }
            Expr::Forall {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let new_type = binder_type.abstract_at(depth, fvar);
                let new_body = body.abstract_at(depth + 1, fvar);
                rebuild_binder(
                    false,
                    binder_name,
                    binder_type,
                    body,
                    *info,
                    new_type,
                    new_body,
                )
            }
            Expr::Let {
                binder_name,
                binder_type,
                value,
                body,
            } => {
                let new_type = binder_type.abstract_at(depth, fvar);
                let new_value = value.abstract_at(depth, fvar);
                let new_body = body.abstract_at(depth + 1, fvar);
                rebuild_let(
                    binder_name,
                    binder_type,
                    value,
                    body,
                    new_type,
                    new_value,
                    new_body,
                )
            }
            Expr::Proj(proj) => proj
                .value
                .abstract_at(depth, fvar)
                .map(|inner| rebuild_proj(proj, inner)),
            _ => None,
        }
    }

    // --- reduction ------------------------------------------------------

    /// Does one beta step at the head of the application spine.
    ///
    /// `f x y` is `App(App(f, x), y)`, so the lambda sits at the bottom of the
    /// left side, not at the top. The method therefore splits the spine first.
    /// Returns `None` if the head is not a lambda or if there is no argument.
    pub fn beta_step(&self) -> Option<Expr> {
        let (head, args) = self.unfold_apps();
        let Expr::Lam { body, .. } = head else {
            return None;
        };
        let first = *args.first()?;
        let reduced = body.instantiate(first);
        // The remaining arguments apply to the result of the step.
        Some(reduced.apps(args[1..].iter().map(|arg| (*arg).clone())))
    }

    /// Repeats [`Expr::beta_step`] at the head until no step applies.
    ///
    /// This function is not a full evaluator. It does not unfold a definition
    /// and it does not look inside a binder. A real kernel adds delta, zeta,
    /// iota, and eta to this list.
    pub fn beta(&self) -> Expr {
        let mut current = self.clone();
        while let Some(next) = current.beta_step() {
            current = next;
        }
        current
    }

    // --- printing -------------------------------------------------------

    /// Renders `self` with names instead of indices.
    ///
    /// The printer gives each binder a fresh name, so that no inner binder
    /// hides an outer one. A free variable prints as `_f<id>`, because this
    /// method has no local context to read. Use
    /// [`LocalContext::pretty`][crate::LocalContext::pretty] when you have one.
    pub fn pretty(&self) -> String {
        self.pretty_with(&|_| None)
    }

    /// Renders `self`, and asks `fvar_name` for the name of a free variable.
    ///
    /// An error message must say `a → a`, not `_f0 → _f0`. The caller holds the
    /// names, so the caller supplies them.
    pub fn pretty_with(&self, fvar_name: &dyn Fn(FVarId) -> Option<String>) -> String {
        let mut out = String::new();
        let mut names = Vec::new();
        self.write_pretty(&mut out, &mut names, 0, fvar_name);
        out
    }

    fn write_pretty(
        &self,
        out: &mut String,
        names: &mut Vec<String>,
        prec: u8,
        fvar: &dyn Fn(FVarId) -> Option<String>,
    ) {
        // The precedence levels are: 0 for a binder body, 1 for an argument of
        // an arrow, and 2 for an argument of an application.
        match self {
            Expr::BVar(index) => {
                // Index 0 is the nearest binder, which is the last name.
                match names.len().checked_sub(*index as usize + 1) {
                    Some(slot) => out.push_str(&names[slot]),
                    None => out.push_str(&format!("#{index}")),
                }
            }
            Expr::FVar(id) => match fvar(*id) {
                Some(name) => out.push_str(&name),
                None => out.push_str(&format!("_f{}", id.0)),
            },
            Expr::MVar(id) => out.push_str(&format!("?m{}", id.0)),
            Expr::Sort(level) => match level.to_nat() {
                Some(0) => out.push_str("Prop"),
                Some(1) => out.push_str("Type"),
                Some(n) => out.push_str(&format!("Type {}", n - 1)),
                None => out.push_str(&format!("Sort {level}")),
            },
            Expr::Const { name, levels } => {
                out.push_str(&name.to_string());
                if !levels.is_empty() {
                    let parts: Vec<String> = levels.iter().map(Level::to_string).collect();
                    out.push_str(&format!(".{{{}}}", parts.join(", ")));
                }
            }
            Expr::Lit(Literal::Nat(digits)) => out.push_str(digits),
            Expr::Lit(Literal::Str(value)) => out.push_str(&format!("{value:?}")),
            Expr::Proj(proj) => {
                proj.value.write_pretty(out, names, 2, fvar);
                out.push_str(&format!(".{}", proj.index + 1));
            }
            Expr::App { .. } => {
                let (head, args) = self.unfold_apps();
                let wrap = prec >= 2;
                if wrap {
                    out.push('(');
                }
                head.write_pretty(out, names, 2, fvar);
                for arg in args {
                    out.push(' ');
                    arg.write_pretty(out, names, 2, fvar);
                }
                if wrap {
                    out.push(')');
                }
            }
            Expr::Lam {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let wrap = prec >= 1;
                if wrap {
                    out.push('(');
                }
                let (open, close) = info.brackets();
                let name = fresh(binder_name, names);
                out.push_str("fun ");
                out.push_str(open);
                out.push_str(&format!("{name} : "));
                binder_type.write_pretty(out, names, 0, fvar);
                out.push_str(close);
                out.push_str(" => ");
                names.push(name);
                body.write_pretty(out, names, 0, fvar);
                names.pop();
                if wrap {
                    out.push(')');
                }
            }
            Expr::Forall {
                binder_name,
                binder_type,
                body,
                info,
            } => {
                let wrap = prec >= 1;
                if wrap {
                    out.push('(');
                }
                let name = fresh(binder_name, names);
                // A body that ignores the binder prints as a plain arrow.
                if !body.has_loose_bvar(0) && *info == BinderInfo::Default {
                    binder_type.write_pretty(out, names, 1, fvar);
                    out.push_str(" → ");
                    names.push(name);
                    body.write_pretty(out, names, 0, fvar);
                    names.pop();
                } else {
                    let (open, close) = info.brackets();
                    out.push_str(open);
                    out.push_str(&format!("{name} : "));
                    binder_type.write_pretty(out, names, 0, fvar);
                    out.push_str(close);
                    out.push_str(" → ");
                    names.push(name);
                    body.write_pretty(out, names, 0, fvar);
                    names.pop();
                }
                if wrap {
                    out.push(')');
                }
            }
            Expr::Let {
                binder_name,
                binder_type,
                value,
                body,
            } => {
                let wrap = prec >= 1;
                if wrap {
                    out.push('(');
                }
                let name = fresh(binder_name, names);
                out.push_str(&format!("let {name} : "));
                binder_type.write_pretty(out, names, 0, fvar);
                out.push_str(" := ");
                value.write_pretty(out, names, 0, fvar);
                out.push_str("; ");
                names.push(name);
                body.write_pretty(out, names, 0, fvar);
                names.pop();
                if wrap {
                    out.push(')');
                }
            }
        }
    }
}

/// Rebuilds an application, reusing an unchanged side.
///
/// `None` in, `None` out. See [`Expr::lift_opt`].
fn rebuild_app(fun: &Sub, arg: &Sub, new_fun: Option<Sub>, new_arg: Option<Sub>) -> Option<Expr> {
    if new_fun.is_none() && new_arg.is_none() {
        return None;
    }
    Some(Expr::App {
        fun: keep(fun, new_fun),
        arg: keep(arg, new_arg),
    })
}

/// Rebuilds a lambda or a function type, reusing an unchanged part.
fn rebuild_binder(
    lambda: bool,
    binder_name: &Name,
    binder_type: &Sub,
    body: &Sub,
    info: BinderInfo,
    new_type: Option<Sub>,
    new_body: Option<Sub>,
) -> Option<Expr> {
    if new_type.is_none() && new_body.is_none() {
        return None;
    }
    let binder_name = binder_name.clone();
    let binder_type = keep(binder_type, new_type);
    let body = keep(body, new_body);
    Some(if lambda {
        Expr::Lam {
            binder_name,
            binder_type,
            body,
            info,
        }
    } else {
        Expr::Forall {
            binder_name,
            binder_type,
            body,
            info,
        }
    })
}

/// Rebuilds a `let`, reusing an unchanged part.
fn rebuild_let(
    binder_name: &Name,
    binder_type: &Sub,
    value: &Sub,
    body: &Sub,
    new_type: Option<Sub>,
    new_value: Option<Sub>,
    new_body: Option<Sub>,
) -> Option<Expr> {
    if new_type.is_none() && new_value.is_none() && new_body.is_none() {
        return None;
    }
    Some(Expr::Let {
        binder_name: binder_name.clone(),
        binder_type: keep(binder_type, new_type),
        value: keep(value, new_value),
        body: keep(body, new_body),
    })
}

/// Rebuilds a projection around a changed target.
fn rebuild_proj(proj: &Proj, value: Sub) -> Expr {
    Expr::Proj(Proj {
        structure: proj.structure.clone(),
        index: proj.index,
        value,
    })
}

/// Keeps the existing `Arc` when nothing changed, so the cost is one reference
/// count bump rather than a deep copy.
fn keep(original: &Sub, replacement: Option<Sub>) -> Sub {
    replacement.unwrap_or_else(|| original.clone())
}

/// Returns a name that no name in `used` matches.
fn fresh(binder_name: &Name, used: &[String]) -> String {
    let base = match binder_name.last_str() {
        Some(text) if !text.is_empty() => text.to_string(),
        _ => "x".to_string(),
    };
    if !used.contains(&base) {
        return base;
    }
    for suffix in 1u32.. {
        let candidate = format!("{base}{suffix}");
        if !used.contains(&candidate) {
            return candidate;
        }
    }
    unreachable!("the loop always finds a free name")
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.pretty())
    }
}

#[cfg(test)]
mod tests {
    use super::{BinderInfo, Expr, FVarId, Proj, Sub};
    use crate::level::Level;
    use rean_core::Name;

    fn nat() -> Expr {
        Expr::const_("Nat", vec![])
    }

    /// `fun x => fun y => x`, which is `const`.
    fn const_fn() -> Expr {
        Expr::lam("x", nat(), Expr::lam("y", nat(), Expr::bvar(1)))
    }

    #[test]
    fn de_bruijn_makes_the_names_irrelevant() {
        let with_x = Expr::lam("x", nat(), Expr::bvar(0));
        let with_y = Expr::lam("y", nat(), Expr::bvar(0));
        // The binder name differs, so the terms are not equal as data.
        assert_ne!(with_x, with_y);
        // But the index is the same, so the bodies are equal.
        let (Expr::Lam { body: a, .. }, Expr::Lam { body: b, .. }) = (&with_x, &with_y) else {
            panic!("both terms are lambdas");
        };
        assert_eq!(a, b);
    }

    #[test]
    fn a_beta_step_drops_one_binder() {
        let applied = const_fn().app(nat());
        let reduced = applied.beta();
        assert_eq!(reduced, Expr::lam("y", nat(), nat()));
        assert_eq!(reduced.pretty(), "fun (y : Nat) => Nat");
    }

    #[test]
    fn substitution_lifts_a_term_with_loose_variables() {
        // `fun u => (fun x => fun y => x) u`
        let term = Expr::lam("u", nat(), const_fn().app(Expr::bvar(0)));
        let Expr::Lam { body, .. } = &term else {
            panic!("the term is a lambda");
        };
        let reduced = body.beta();
        // The argument `BVar 0` moves under one new binder, so it becomes `BVar 1`.
        assert_eq!(reduced, Expr::lam("y", nat(), Expr::bvar(1)));
        assert_eq!(
            Expr::lam("u", nat(), reduced).pretty(),
            "fun (u : Nat) => fun (y : Nat) => u"
        );
    }

    #[test]
    fn beta_repeats_until_the_head_is_not_a_lambda() {
        let reduced = const_fn().apps([nat(), Expr::prop()]).beta();
        assert_eq!(reduced, nat());
    }

    #[test]
    fn beta_step_returns_none_for_a_term_that_is_not_an_application() {
        assert!(nat().beta_step().is_none());
        assert!(nat().app(nat()).beta_step().is_none());
    }

    #[test]
    fn lift_renumbers_only_the_loose_variables() {
        // `fun y => x y`, where `x` is loose with index 1 inside the body.
        let term = Expr::lam("y", nat(), Expr::bvar(1).app(Expr::bvar(0)));
        let lifted = term.lift(0, 2);
        assert_eq!(
            lifted,
            Expr::lam("y", nat(), Expr::bvar(3).app(Expr::bvar(0)))
        );
    }

    #[test]
    fn lift_by_zero_changes_nothing() {
        assert_eq!(const_fn().lift(0, 5).lift(0, 0), const_fn().lift(0, 5));
    }

    #[test]
    fn loose_variables_show_an_open_term() {
        assert!(!const_fn().has_loose_bvars());
        assert!(Expr::bvar(0).has_loose_bvars());
        assert!(Expr::lam("x", nat(), Expr::bvar(1)).has_loose_bvars());
        assert!(!Expr::lam("x", nat(), Expr::bvar(0)).has_loose_bvars());
    }

    #[test]
    fn abstract_fvar_closes_a_binder_again() {
        let f = FVarId(7);
        // The elaborator opened `fun x => x + 0` and now holds `_f7 + 0`.
        let open = Expr::const_("Nat.add", vec![]).apps([Expr::FVar(f), Expr::nat("0")]);
        let closed = Expr::lam("x", nat(), open.abstract_fvar(f));
        assert_eq!(closed.pretty(), "fun (x : Nat) => Nat.add x 0");
        assert!(!closed.has_loose_bvars());
    }

    #[test]
    fn abstract_and_instantiate_are_inverse() {
        let f = FVarId(1);
        let open = Expr::FVar(f).app(Expr::nat("2"));
        let closed = open.abstract_fvar(f);
        assert_eq!(closed.instantiate(&Expr::FVar(f)), open);
    }

    #[test]
    fn unfold_apps_splits_the_head_from_the_arguments() {
        let term = nat().apps([Expr::nat("1"), Expr::nat("2")]);
        let (head, args) = term.unfold_apps();
        assert_eq!(head, &nat());
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], &Expr::nat("1"));
    }

    #[test]
    fn arrow_prints_without_a_binder_name() {
        let term = Expr::arrow(nat(), nat());
        assert_eq!(term.pretty(), "Nat → Nat");
        // The body must not use the binder.
        let Expr::Forall { body, .. } = &term else {
            panic!("an arrow is a forall");
        };
        assert!(!body.has_loose_bvar(0));
    }

    #[test]
    fn a_dependent_forall_prints_the_binder() {
        // `(α : Type) → α → α`, the type of the identity function.
        let term = Expr::forall(
            "α",
            Expr::type_(0),
            Expr::arrow(Expr::bvar(0), Expr::bvar(0)),
        );
        assert_eq!(term.pretty(), "(α : Type) → α → α");
    }

    #[test]
    fn an_implicit_binder_prints_braces() {
        let term = Expr::Forall {
            binder_name: Name::from_dotted("α"),
            binder_type: Sub::new(Expr::type_(0)),
            body: Sub::new(Expr::bvar(0)),
            info: BinderInfo::Implicit,
        };
        assert_eq!(term.pretty(), "{α : Type} → α");
    }

    #[test]
    fn the_printer_renames_a_shadowed_binder() {
        // `fun x => fun x => x` must not print two binders with one name.
        let term = Expr::lam("x", nat(), Expr::lam("x", nat(), Expr::bvar(1)));
        assert_eq!(term.pretty(), "fun (x : Nat) => fun (x1 : Nat) => x");
    }

    #[test]
    fn a_loose_variable_prints_its_index() {
        assert_eq!(Expr::bvar(3).pretty(), "#3");
    }

    #[test]
    fn sorts_print_with_their_lean_names() {
        assert_eq!(Expr::prop().pretty(), "Prop");
        assert_eq!(Expr::type_(0).pretty(), "Type");
        assert_eq!(Expr::type_(2).pretty(), "Type 2");
        assert_eq!(Expr::sort(Level::param("u")).pretty(), "Sort u");
    }

    #[test]
    fn a_constant_prints_its_universe_arguments() {
        let term = Expr::const_("List", vec![Level::param("u")]);
        assert_eq!(term.pretty(), "List.{u}");
    }

    #[test]
    fn a_nested_application_gets_brackets() {
        let term = nat().app(nat().app(nat()));
        assert_eq!(term.pretty(), "Nat (Nat Nat)");
    }

    #[test]
    fn a_let_prints_its_value_and_its_body() {
        let term = Expr::let_("n", nat(), Expr::nat("2"), Expr::bvar(0));
        assert_eq!(term.pretty(), "let n : Nat := 2; n");
    }

    #[test]
    fn has_loose_bvar_asks_about_one_binder() {
        // `fun y => x`, where the body uses the outer binder and not `y`.
        let body = Expr::lam("y", nat(), Expr::bvar(1));
        assert!(body.has_loose_bvar(0));
        assert!(!body.has_loose_bvar(1));
        // `fun y => y` uses no outer binder at all.
        let closed = Expr::lam("y", nat(), Expr::bvar(0));
        assert!(!closed.has_loose_bvar(0));
    }

    #[test]
    fn a_projection_counts_from_one_in_the_output() {
        let term = Expr::Proj(Proj {
            structure: Name::from_dotted("Prod"),
            index: 0,
            value: Sub::new(Expr::FVar(FVarId(0))),
        });
        assert_eq!(term.pretty(), "_f0.1");
    }
}
