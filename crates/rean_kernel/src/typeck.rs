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
use crate::expr::{
    BinderInfo, Expr, FVarId, KeyMap, KeySet, Literal, MVarId, Proj, Sub, mix_hashes,
};
use crate::level::Level;
use crate::local::LocalContext;
use crate::nat_lit::{self, NatShape};
use crate::positivity::{self, PositivityError};
use crate::tally;
use rean_core::Name;
use std::fmt;

/// How deep [`TypeChecker::read_nat`] will force a nested arithmetic argument.
///
/// To compute `Nat.sub a b` the kernel must reduce `a` and `b` first, and if
/// `a` is itself `Nat.sub c d` then reducing it reduces `c`, and so on. That
/// descent is a mutual recursion between `read_nat` and `whnf`, and chapter 15,
/// section 15.11, found it overflowing a **32 GB** stack. So it has to be
/// bounded.
///
/// # Why this counts nesting and not work
///
/// Counting work is the better looking design and it was built and measured.
/// Chapter 17 has the table. A read may spend a few hundred units and then give
/// up, which reads trivial arguments at any depth and bounds the pathological
/// ones by the thing that actually hurts.
///
/// It is **much worse**, and the reason is the shape of the failure. A read
/// that declines on nesting costs **nothing**: the guard is a comparison. A
/// read that declines on work has spent its whole allowance first, and the
/// arithmetic of the signed integer family is genuinely too deep to read, so
/// the kernel pays that allowance millions of times over.
///
/// | limit on one read | the signed integer slice | time |
/// |---|---|---|
/// | **16 levels of nesting** | **16,583 of 16,584** | **205 s** |
/// | 1,000 units of work | 15,737 of 16,584 | 743 s |
/// | 200 units of work | 15,681 of 16,584 | 1,125 s |
///
/// Eight hundred declarations and four times the time. The cheap refusal wins,
/// and the lesson generalises: **when a guard fires often, what it costs to
/// fire matters more than what it measures.**
///
/// One half of the work version is kept, in [`TypeChecker::read_nat`]: a term
/// that is **already** a numeral is read before the guard, at no cost. The
/// instrument that justified the whole experiment found the kernel declining
/// to read the number zero 63 times in one declaration, and that part was
/// real.
const NAT_DEPTH_LIMIT: u32 = 16;

/// How many `Nat.succ` layers [`TypeChecker::read_nat`] will peel.
///
/// Reading a number through its constructor form is what chapter 13 is about,
/// and the case that needed it was one layer deep:
/// `Nat.succ (OfNat.ofNat Nat 1 ..)`.
///
/// Without a limit the reader walks the whole tower, reducing as it goes, and
/// `nat_step` tries it on **every** step whose head is a `Nat` operation. The
/// same tower is then walked again and again, and `read_nat` became the
/// heaviest frame in a profile of the prelude, level with `whnf` itself.
///
/// So read a few layers and give up. Giving up is only slower, never wrong:
/// the kernel falls back to unfolding the definition, which is what it did
/// before chapter 13.
const SUCC_LIMIT: u32 = 16;

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
///
/// # The number comes from a sweep
///
/// Chapter 13 chose 20,000,000 by sweeping, and chapter 17 had to sweep again,
/// because the **meter** changed. A walk of a term is now charged before it
/// happens, so the same work costs more units than it did. The whole prelude,
/// 59,349 declarations:
///
/// | budget | checked | failed | time |
/// |---|---|---|---|
/// | 20,000,000 | 55,751 | 82 | 189 s |
/// | **40,000,000** | **55,835** | 72 | 231 s |
/// | 100,000,000 | 55,843 | 68 | 260 s |
///
/// The third row buys 8 declarations for 29 seconds, and the second buys 84 for
/// 42. So the default moved to 40,000,000.
///
/// **A number chosen by measurement has to be measured again when the thing it
/// measures changes.**
const FUEL: u64 = 40_000_000;

/// How many bytes of stack the kernel may use before it declines.
///
/// The kernel walks a term by recursion, and one rule makes that recursion
/// unbounded: to reduce a recursor the kernel must first reduce the **major
/// premise**, and that premise can itself be a recursor application. The depth
/// is then the depth of the term, and the term is one that the reduction built.
///
/// A work budget does not bound it. Chapter 15, section 15.11, measured the
/// same 345 seconds at four billion units and at sixteen billion, which is what
/// a **crash** looks like beside a timeout: the run died of a 32 GB stack before
/// it could spend the budget. A hundred times the default budget over the whole
/// prelude did the same thing at 4 GB. A checker that aborts cannot report.
///
/// # Why this counts bytes and not levels
///
/// The first version of this guard counted **levels**, as Lean's `maxRecDepth`
/// does, and the measurement refused it. On the deepest declaration of the
/// prelude a 512 MB stack held 100,000 levels and died at 200,000, so a level
/// costs about 5 KB; but the chain that actually goes deep is
/// `whnf -> reduce -> whnf`, whose frames are far smaller than that. A count
/// set for the fat path refuses work the thin path could finish, and a count
/// set for the thin path crashes on the fat one. **There is no right count.**
///
/// So the kernel measures the thing it is running out of. It records the stack
/// address where a declaration started and compares it with the address of a
/// local on each entry, which is two instructions and no counter at all.
///
/// This default is the 8 MB that a **main thread** gets, less a margin, because
/// a library cannot know its stack. The driver chooses the stack, so it sets
/// this from `REAN_STACK` and the two stop being independent.
const STACK_BUDGET: usize = 6 * 1024 * 1024;

/// Returns the address of a local, which is where the stack is now.
///
/// The hint keeps the local on the stack. Without it the optimiser is free to
/// hold it in a register, and the address of a register is not a thing.
fn stack_pointer() -> usize {
    let probe = 0u8;
    std::hint::black_box(&probe) as *const u8 as usize
}

/// What [`TypeChecker::read_nat`] found out about a term.
///
/// Three outcomes and not two, and the difference between the last two is a
/// **cache** bug that cost 2,421,228 reduction steps on one declaration of the
/// prelude.
///
/// `read_nat` remembers the terms that are not numbers, because `nat_step` asks
/// about the same term on every reduction step. But a read that stops at
/// [`NAT_DEPTH_LIMIT`] has found out **nothing** about the term, and the old
/// version returned the same `None` for both. So a term that is a perfectly
/// good number, read once while the reader happened to be sixteen levels deep,
/// was remembered as "not a number" for the rest of the declaration, and every
/// later attempt declined at once without looking.
///
/// A cache may hold an answer. It may not hold the absence of one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum NatRead {
    /// The term is this number.
    Number(u128),
    /// The term is not a number, and nothing will make it one. Worth
    /// remembering.
    NotANumber,
    /// A limit stopped the attempt, so there is no answer to remember.
    Declined,
}

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
    /// The kernel ran out of the stack it is allowed to use.
    ///
    /// This is a limit and not a fault in the declaration, exactly like
    /// [`TypeError::OutOfFuel`]. See [`STACK_BUDGET`].
    OutOfStack(usize),
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
    ///
    /// The payload is boxed, for the reason this enum's own comment gives: it
    /// sits in the return value of the hot path. It holds two names and two
    /// rendered levels, and chapter 18 gave a [`Name`] two numbers of its own,
    /// which pushed this variant to 132 bytes and `clippy` noticed.
    FieldTooLarge(Box<FieldTooLarge>),
}

/// Why a constructor field does not fit in its inductive type.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FieldTooLarge {
    pub ctor: Name,
    pub inductive: Name,
    pub field: u32,
    pub field_level: String,
    pub limit: String,
}

impl TypeError {
    /// Returns `true` for an error about a **limit** rather than about a term.
    ///
    /// Several rules of [`TypeChecker::is_def_eq`] ask a question that may
    /// fail, and a failure there means "this rule does not apply" and not "the
    /// declaration is wrong". A limit is the exception: it must travel out, or
    /// the report blames the wrong cause, and a report that blames the wrong
    /// cause is worse than no report.
    pub fn is_a_limit(&self) -> bool {
        matches!(self, TypeError::OutOfFuel(_) | TypeError::OutOfStack(_))
    }

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
            TypeError::OutOfStack(budget) => format!(
                "the kernel used the {} MiB of stack it is allowed, so it was \
                 not checked. REAN_STACK raises it",
                budget / (1024 * 1024)
            ),
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
            TypeError::FieldTooLarge(it) => format!(
                "field {} of `{}` lives in `Sort {}` and `{}` only reaches `Sort {}`",
                it.field, it.ctor, it.field_level, it.inductive, it.limit
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

thread_local! {
    /// Every `whnf` question the run has asked, by hash. An instrument, and it
    /// fills only when `REAN_TALLY` is set. See [`TypeChecker::whnf`].
    static ASKED_EVER: std::cell::RefCell<std::collections::HashSet<u64>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
}

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
    whnf_cache: KeyMap<u64, Vec<(Expr, Expr)>>,
    /// Answers that [`Self::is_def_eq`] already found.
    ///
    /// The same discipline as [`Self::whnf_cache`]. The key mixes the hash of
    /// both sides, and a hit is confirmed against both questions.
    ///
    /// A **negative** answer is cached as well as a positive one. `Ok(false)`
    /// means the two terms are not equal, which is a decision; a comparison
    /// that ran out of budget returns `Err` instead, and no error is cached.
    def_eq_cache: KeyMap<u64, Vec<(Expr, Expr, bool)>>,
    /// Types that [`Self::infer_type`] already found.
    ///
    /// The same discipline again. Proof irrelevance asks for the type of both
    /// sides of every comparison, and the answer for one term never changes
    /// inside one declaration.
    infer_cache: KeyMap<u64, Vec<(Expr, Expr)>>,
    /// Answers that [`Self::whnf_core`] already found.
    ///
    /// A core answer and a full answer are answers to different questions, so
    /// they cannot share one map.
    core_cache: KeyMap<u64, Vec<(Expr, Expr)>>,
    /// Terms that [`Self::read_nat`] has already found are not numbers.
    ///
    /// `nat_step` is tried on **every** reduction step whose head is a `Nat`
    /// operation, and each try forces both arguments. A term that is not a
    /// number stays one, so the second try can answer at once.
    ///
    /// This is the one cache in the kernel that needs **no confirmation**, and
    /// the reason is worth keeping. Chapter 10 insists that a hash only finds
    /// an answer and `alpha_eq` decides, because two terms can share a hash.
    /// Here a collision makes the kernel call a number "not a number", so it
    /// declines and unfolds the definition instead. That is slower and it is
    /// not wrong. A cache may skip its confirmation exactly when being wrong
    /// costs time rather than truth.
    not_a_number: KeySet<u64>,
    /// Numbers that [`Self::read_nat`] has already found.
    ///
    /// The other half of [`Self::not_a_number`], and it was missing for a
    /// reason that is worth keeping: the kernel asks the same question far
    /// more often than anybody would guess. On one declaration of the prelude
    /// **one term was read 5,290,885 times**, always with the same answer, and
    /// the instrument that found that out is three lines of `eprintln!` on the
    /// path that declined.
    ///
    /// This cache keeps chapter 10's rule, and [`Self::not_a_number`] does
    /// not. A hash **finds** the entry here and [`Expr::alpha_eq`]
    /// **decides**, because a wrong number is a wrong answer. The exception
    /// that the negative cache enjoys does not apply: being wrong there costs
    /// time, and being wrong here would cost the truth.
    numbers: KeyMap<u64, Vec<(Expr, u128)>>,
    /// How many arithmetic arguments [`Self::read_nat`] is forcing right now.
    ///
    /// See [`SUCC_LIMIT`] for the other half of the same story.
    nat_depth: u32,
    /// How deep that may go. See [`NAT_DEPTH_LIMIT`].
    nat_depth_limit: u32,
    /// Where the stack was when this declaration started, or zero.
    ///
    /// Zero means "not taken yet", so the first entry records it. See
    /// [`STACK_BUDGET`].
    stack_base: usize,
    /// How many bytes of stack this run allows. See [`STACK_BUDGET`].
    stack_budget: usize,
    /// The most stack that the declaration under check has used.
    ///
    /// A report that says "out of stack" is more useful beside the number that
    /// a declaration which **passed** needed, because the two together say
    /// whether the limit is close or far.
    deepest: usize,
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

    /// Sets how deep [`Self::read_nat`] may force a nested argument.
    ///
    /// A knob because it is a **trade**, and both sides of it are measured in
    /// chapter 17. A shallow limit sends the kernel down the unary path and
    /// costs work. A deep one reads the arithmetic and costs stack. There is no
    /// value that is right for every declaration, so there is a number that
    /// can be swept.
    pub fn set_nat_depth_limit(&mut self, limit: u32) {
        self.nat_depth_limit = limit;
    }

    /// Sets how many bytes of stack the kernel may use. See [`STACK_BUDGET`].
    ///
    /// The caller that chooses the thread chooses this. Set it **below** the
    /// real stack, because the guard can only act where it is asked, and the
    /// work between two entries needs room of its own.
    pub fn set_stack_budget(&mut self, bytes: usize) {
        self.stack_budget = bytes;
    }

    /// Returns the stack budget of this run, in bytes.
    pub fn stack_budget(&self) -> usize {
        self.stack_budget
    }

    /// Returns the most stack used since the last declaration started.
    pub fn deepest(&self) -> usize {
        self.deepest
    }

    /// Builds a checker with an empty local context.
    pub fn new(env: &'e Environment) -> Self {
        TypeChecker {
            env,
            lctx: LocalContext::new(),
            pending: Vec::new(),
            fuel: FUEL,
            budget: FUEL,
            whnf_cache: KeyMap::default(),
            def_eq_cache: KeyMap::default(),
            infer_cache: KeyMap::default(),
            core_cache: KeyMap::default(),
            not_a_number: KeySet::default(),
            numbers: KeyMap::default(),
            nat_depth: 0,
            nat_depth_limit: NAT_DEPTH_LIMIT,
            stack_base: 0,
            stack_budget: STACK_BUDGET,
            deepest: 0,
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
        // A new group starts a new tally, so that the rows a report prints
        // belong to the declaration it names.
        tally::clear();
        self.deepest = 0;
        // A new group starts from wherever this call sits, which is the frame
        // the next check will grow out of.
        self.stack_base = stack_pointer();
        let saved = std::mem::replace(&mut self.pending, group.to_vec());
        let out = body(self);
        self.pending = saved;
        self.clear_caches();
        out
    }

    /// Declines when the stack is nearly spent. See [`STACK_BUDGET`].
    ///
    /// Three functions recurse into each other over the shape of a term:
    /// [`Self::whnf`], [`Self::is_def_eq`] and [`Self::infer_type`]. Every deep
    /// chain this kernel has ever overflowed a stack with went through one of
    /// them, so a test at those three doors bounds them all.
    ///
    /// There is nothing to undo on the way out. The measurement is the address
    /// of a local, so it falls as the stack unwinds, by itself.
    ///
    /// # Why this is a test and not a wrapper
    ///
    /// The first version took a closure: `self.deeper(|tc| tc.whnf_inner(e))`.
    /// It reads better, and it adds a frame of its own to every level of a
    /// recursion whose depth is the depth of the term. That is stack spent to
    /// measure stack, in the one place where the resource is the thing being
    /// saved.
    #[inline]
    fn check_stack(&mut self) -> TypeResult<()> {
        let here = stack_pointer();
        if self.stack_base == 0 {
            self.stack_base = here;
        }
        // The stack grows **down**, so the base is the larger address. A caller
        // that entered from a shallower frame than the base saturates to zero,
        // which is right: it has used none of the allowance.
        let used = self.stack_base.saturating_sub(here);
        if used >= self.stack_budget {
            return Err(TypeError::OutOfStack(self.stack_budget));
        }
        if used > self.deepest {
            self.deepest = used;
        }
        Ok(())
    }

    /// Spends one unit of the work budget.
    fn spend(&mut self) -> TypeResult<()> {
        self.spend_many(1)
    }

    /// Spends `units` of the work budget.
    fn spend_many(&mut self, units: u32) -> TypeResult<()> {
        self.spend_units(u64::from(units))
    }

    /// Charges for a walk of `term`, before the walk happens.
    ///
    /// Every node caches its size, so this is O(1), and the size as a **tree**
    /// is what a substitution will rebuild. See the `App` case of
    /// [`Self::infer_type`].
    fn charge_walk(&mut self, term: &Sub) -> TypeResult<()> {
        self.spend_units(u64::from(term.size()))
    }

    /// Spends `units` of the work budget, counted in nodes.
    fn spend_units(&mut self, units: u64) -> TypeResult<()> {
        match self.fuel.checked_sub(units) {
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
        self.check_stack()?;
        let worth_it = e.size_up_to(CACHE_MIN_SIZE) >= CACHE_MIN_SIZE;
        let key = if worth_it { e.hash_value() } else { 0 };
        if worth_it && tally::on() {
            tally::total(|| "whnf asked".to_string(), 1);
            // A set that is never cleared, so it can tell a question that is
            // new to the **run** from one that is new to this declaration.
            // That difference is what a cache which outlived a declaration
            // would collect, and it is the only honest way to price one before
            // building it.
            if ASKED_EVER.with(|seen| seen.borrow_mut().insert(key)) {
                tally::total(|| "whnf question new to the run".to_string(), 1);
            }
        }
        if worth_it
            && let Some(bucket) = self.whnf_cache.get(&key)
            && let Some((_, answer)) = bucket.iter().find(|(question, _)| question.alpha_eq(e))
        {
            tally::total(|| "whnf answered by a cache".to_string(), 1);
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
        self.reduce(e, true)
    }

    /// Reduces to weak head normal form **without** δ.
    ///
    /// Shares the cache with [`Self::whnf`] by key, because a core answer and a
    /// full answer are different answers to different questions. So this keeps
    /// its own.
    fn whnf_core(&mut self, e: &Expr) -> TypeResult<Expr> {
        self.check_stack()?;
        let key = e.hash_value();
        if let Some(bucket) = self.core_cache.get(&key)
            && let Some((_, answer)) = bucket.iter().find(|(question, _)| question.alpha_eq(e))
        {
            return Ok(answer.clone());
        }
        let (answer, steps) = self.reduce(e, false)?;
        if steps > 0 {
            if self.core_cache.len() >= CACHE_CAP {
                self.core_cache.clear();
            }
            self.core_cache
                .entry(key)
                .or_default()
                .push((e.clone(), answer.clone()));
        }
        Ok(answer)
    }

    /// The loop behind [`Self::whnf`] and [`Self::whnf_core`].
    fn reduce(&mut self, e: &Expr, delta: bool) -> TypeResult<(Expr, u32)> {
        let mut current = e.clone();
        // The budget is the only bound this loop needs, and it is a real one.
        // `whnf_step` spends a unit before it tries any rule, so the loop
        // cannot run more times than the budget holds. A second limit of its
        // own was redundant, and it fired on 108 correct declarations of the
        // Lean prelude once the caches made each step cheap enough to reach it.
        let mut steps = 0u32;
        loop {
            let built_before = crate::expr::nodes_built();
            match self.whnf_step_with(&current, delta)? {
                Some(next) => {
                    // A step costs **one, plus every node it built**.
                    //
                    // Each half of that answers a way of getting this wrong.
                    //
                    // The `one` is there because counting only growth would
                    // let a reduction run for ever as long as the term never
                    // grew. So the budget bounds the number of steps too.
                    //
                    // The `added` is there because an ι step can make a term
                    // **larger**, and one step can then cost unboundedly much.
                    // One `BitVec` theorem of the prelude reduced for minutes
                    // inside a budget of two million steps. Summed over a
                    // reduction, the added parts telescope, so the budget
                    // bounds the total growth from the first term to the last.
                    //
                    // The earlier version charged the **whole size** of each
                    // term produced. That reads as caution and is really a
                    // mistake: an `Expr` shares its subterms through `Arc`, so
                    // one subterm counts once per place it appears, and a
                    // reduction of a thousand steps charged the same shared
                    // structure a thousand times over. The checker was paying
                    // for a tree it never built.
                    let charge = 1u64
                        .saturating_add(crate::expr::nodes_built().saturating_sub(built_before));
                    tally::add(|| "units of work charged".to_string(), charge);
                    self.spend_units(charge)?;
                    current = next;
                    steps = steps.saturating_add(1);
                }
                None => return Ok((current, steps)),
            }
        }
    }

    /// Does one reduction step at the head, or returns `None` if none applies.
    /// Does one reduction step, with δ switched on or off.
    ///
    /// Everything except δ is called **core** reduction, and
    /// [`Self::lazy_delta`] needs the two separated: it reduces both sides by
    /// core only, and then chooses **one** of them to unfold.
    fn whnf_step_with(&mut self, e: &Expr, delta: bool) -> TypeResult<Option<Expr>> {
        self.spend()?;
        let (head, borrowed) = e.unfold_apps();
        // The arguments stay borrowed until a rule actually fires. Cloning
        // them first cost a whole `Vec` of deep copies per reduction step,
        // and most steps do not fire.
        let cloned = || -> Vec<Expr> { borrowed.iter().map(|arg| (*arg).clone()).collect() };

        // ζ: a `let` in the head position substitutes its value.
        if let Expr::Let { value, body, .. } = head {
            tally::bump(|| "zeta".to_string());
            return Ok(Some(body.instantiate(value).apps(cloned())));
        }

        // β: a lambda in the head position takes its first argument.
        if let Some(next) = e.beta_step() {
            tally::bump(|| "beta".to_string());
            return Ok(Some(next));
        }

        // A projection of a constructor application takes the field.
        if let Expr::Proj(proj) = head
            && let Some(field) = self.proj_step(proj)?
        {
            tally::bump(|| format!("proj {}.{}", proj.structure, proj.index));
            return Ok(Some(field.apps(cloned())));
        }

        if let Expr::Const { name, levels } = head {
            tally::bump(|| format!("met head {name}"));
            let args = cloned();
            // The kernel computes on a `Nat` literal directly.
            if let Some(next) = self.nat_step(name, &args)? {
                tally::bump(|| format!("nat {name}"));
                return Ok(Some(next));
            }
            // And on a function of one number, such as `Nat.pred`.
            if let Some(next) = self.nat_unary_step(name, &args)? {
                tally::bump(|| format!("nat {name}"));
                return Ok(Some(next));
            }
            // And on a string literal.
            if let Some(next) = self.string_step(name, &args)? {
                tally::bump(|| format!("string {name}"));
                return Ok(Some(next));
            }
            // ι: a recursor applied to a constructor rewrites to its rule.
            if let Some(next) = self.iota_step(name, levels, &args)? {
                tally::bump(|| format!("iota {name}"));
                return Ok(Some(next));
            }
            // The quotient rules, for `Quot.lift` and `Quot.ind`.
            if let Some(next) = self.quot_step(name, &args)? {
                tally::bump(|| format!("quot {name}"));
                return Ok(Some(next));
            }
            // δ: a definition unfolds to its value.
            if delta
                && let Some(decl) = self.lookup(name)
                && let Some(value) = decl.unfoldable_value()
            {
                tally::bump(|| format!("delta {name}"));
                let value = value.instantiate_levels(decl.level_params(), levels);
                return Ok(Some(value.apps(args)));
            }
        }

        tally::bump(|| "no rule applies".to_string());
        Ok(None)
    }

    /// Computes a function on two `Nat` literals.
    ///
    /// Without this step, `2 + 3` would unfold through `Nat.rec` once per unit,
    /// so a real program would exhaust the reduction budget.
    fn nat_step(&mut self, name: &Name, args: &[Expr]) -> TypeResult<Option<Expr>> {
        if !nat_lit::is_binop(name) {
            return Ok(None);
        }
        if args.len() < 2 {
            tally::bump(|| format!("declined {name}: fewer than two arguments"));
            return Ok(None);
        }
        // A `Bool` result needs the constructors to exist.
        if nat_lit::returns_bool(name) && !self.env.contains(&Name::from_dotted("Bool.true")) {
            return Ok(None);
        }
        let (NatRead::Number(a), NatRead::Number(b)) =
            (self.read_nat(&args[0])?, self.read_nat(&args[1])?)
        else {
            tally::bump(|| format!("declined {name}: a number could not be read"));
            return Ok(None);
        };
        let Some(out) = nat_lit::binop(name, a, b) else {
            // The answer does not fit in a `u128`. Stay stuck rather than lie.
            tally::bump(|| format!("declined {name}: the arithmetic overflowed"));
            return Ok(None);
        };
        Ok(Some(out.apps(args[2..].iter().cloned())))
    }

    /// Computes a function of one `Nat`, such as `Nat.pred`.
    ///
    /// Only a function, never a **constructor**. See [`nat_lit::unop`] for the
    /// loop that `Nat.succ` caused when it was on that list.
    fn nat_unary_step(&mut self, name: &Name, args: &[Expr]) -> TypeResult<Option<Expr>> {
        if !nat_lit::is_unop(name) || args.is_empty() {
            return Ok(None);
        }
        let NatRead::Number(value) = self.read_nat(&args[0])? else {
            return Ok(None);
        };
        let Some(out) = nat_lit::unop(name, value) else {
            return Ok(None);
        };
        Ok(Some(out.apps(args[1..].iter().cloned())))
    }

    /// Reads a number out of `e`, in either of the two forms it can take.
    ///
    /// `2`, `Nat.succ 1` and `Nat.succ (Nat.succ Nat.zero)` are the same
    /// number. A literal was enough for a **comparison**, because `is_def_eq`
    /// has [`Self::nat_lit_eq`] for the other form.
    ///
    /// It was not enough for **computation**, and the cost was extreme. The
    /// kernel computes `Nat.ble a b` in one step only when it can read both
    /// numbers. Given `Nat.ble Nat.Linear.fixedVar (Nat.succ 1)` it read the
    /// second argument as "not a number", declined, and δ then unfolded
    /// `Nat.ble` into the structural recursion that defines it. That recursion
    /// walks its **first** argument through `Nat.brecOn`, and
    /// `Nat.Linear.fixedVar` is 100,000,000. So the checker counted down from a
    /// hundred million, one `Nat.succ` at a time, to answer a comparison that
    /// one machine instruction settles. Chapter 13 has the measurement.
    ///
    /// The reduction has to happen **inside** the loop. `whnf` is weak head
    /// only, so `Nat.succ (OfNat.ofNat Nat 1 ..)` keeps an unreduced argument,
    /// and a reader that only looked at the surface stopped one layer in.
    ///
    /// The loop ends because each step takes a strictly smaller term.
    fn read_nat(&mut self, e: &Expr) -> TypeResult<NatRead> {
        // **Ask the caches before the depth guard, not after.**
        //
        // The guard used to come first, and it is the only exit that
        // remembers nothing. So a term it declined was asked again on the next
        // reduction step, and the next, with no record that the question had
        // ever been put. On one declaration of the prelude the **same term**
        // reached this line 5,290,885 times.
        //
        // An answer that is already known is known at any depth. The guard is
        // about how far to **descend**, and a cache hit descends nowhere.
        let key = e.hash_value();
        if let Some(bucket) = self.numbers.get(&key)
            && let Some((_, value)) = bucket.iter().find(|(term, _)| term.alpha_eq(e))
        {
            return Ok(NatRead::Number(*value));
        }
        if self.not_a_number.contains(&key) {
            return Ok(NatRead::NotANumber);
        }
        // A term that is **already** a numeral answers at any depth and at any
        // cost, because there is no descent to make. 63 declines of the number
        // zero in one declaration are what this line is for.
        if let Some(found) = nat_lit::value(e) {
            return Ok(NatRead::Number(found));
        }
        if self.nat_depth >= self.nat_depth_limit {
            // Not an answer about the term, so nothing is remembered.
            tally::bump(|| "declined read_nat: nested too deep".to_string());
            return Ok(NatRead::Declined);
        }
        self.nat_depth += 1;
        let answer = self.read_nat_inner(e);
        self.nat_depth -= 1;
        // **Only a real answer is remembered.** A `Declined` means a limit
        // stopped the read somewhere below, which says nothing about this
        // term. See [`NatRead`] for what remembering it cost.
        match answer {
            Ok(NatRead::NotANumber) => {
                if self.not_a_number.len() >= CACHE_CAP {
                    self.not_a_number.clear();
                }
                self.not_a_number.insert(key);
            }
            Ok(NatRead::Number(value)) => {
                if self.numbers.len() >= CACHE_CAP {
                    self.numbers.clear();
                }
                self.numbers
                    .entry(key)
                    .or_default()
                    .push((e.clone(), value));
            }
            _ => {}
        }
        answer
    }

    /// The body of [`Self::read_nat`], inside the depth guard.
    fn read_nat_inner(&mut self, e: &Expr) -> TypeResult<NatRead> {
        let mut extra: u128 = 0;
        let mut current = self.whnf(e)?;
        for _ in 0..SUCC_LIMIT {
            if let Some(found) = nat_lit::value(&current) {
                return Ok(match found.checked_add(extra) {
                    Some(sum) => NatRead::Number(sum),
                    // The number is real and larger than a `u128`. That is a
                    // limit of this module, not a fact about the term.
                    None => {
                        tally::bump(|| "declined read_nat: past u128".to_string());
                        NatRead::Declined
                    }
                });
            }
            match nat_lit::shape(&current) {
                Some(NatShape::Zero) => return Ok(NatRead::Number(extra)),
                Some(NatShape::Succ(inner)) => {
                    let Some(next) = extra.checked_add(1) else {
                        tally::bump(|| "declined read_nat: past u128".to_string());
                        return Ok(NatRead::Declined);
                    };
                    extra = next;
                    let inner = inner.clone();
                    current = self.whnf(&inner)?;
                }
                // The head is neither a literal nor a `Nat` constructor, so
                // this term is not a number. **This** is the answer the cache
                // exists for.
                None => return Ok(NatRead::NotANumber),
            }
        }
        // A tower taller than `SUCC_LIMIT` is not a numeral anyone wrote.
        tally::bump(|| "declined read_nat: the tower of successors is too tall".to_string());
        Ok(NatRead::Declined)
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
        // The cheap test. Most comparisons stop here, and it costs no fuel and
        // no stack: `alpha_eq` walks the two terms without recursing through
        // any rule.
        if a.alpha_eq(b) {
            return Ok(true);
        }
        self.check_stack()?;
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
        self.infer_cache.clear();
        self.core_cache.clear();
        self.not_a_number.clear();
        self.numbers.clear();
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
        // **Proof irrelevance, before any reduction.**
        //
        // Two proofs of one proposition are equal, so the kernel never has to
        // look at a proof at all. It only has to see that both sides prove the
        // same thing.
        //
        // This used to be the **last** rule, after every reduction above it had
        // already run. A proof of the Lean prelude is built from `Eq.mpr`,
        // `congrArg` and `of_eq_true`, and reducing one of those drags in the
        // whole computation it speaks about.
        match self.proof_irrelevant(a, b) {
            Ok(Some(answer)) => return Ok(answer),
            Ok(None) => {}
            // A limit is the one error that must not be hidden, because a
            // report that blames the wrong cause is worse than no report.
            Err(error) if error.is_a_limit() => return Err(error),
            // Any other error means this rule did not apply, not that the
            // declaration is wrong. The full comparison below decides.
            Err(_) => {}
        }
        let (a, b) = self.lazy_delta(a, b)?;
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
        // Proof irrelevance again, now that both sides are reduced. A term
        // whose type could not be read before may have a readable one now.
        Ok(self.proof_irrelevant(&a, &b)?.unwrap_or(false))
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

    /// Reduces both sides, unfolding **one at a time** and the taller first.
    ///
    /// The old version called `whnf` on each side, which reduces until no rule
    /// applies at the head, δ included. So comparing `f x` with `g y` unfolded
    /// `f` **and** `g` all the way down before looking at either result, and
    /// unfolding a definition of the Lean prelude can be hundreds of thousands
    /// of steps.
    ///
    /// Lean unfolds the **taller** of the two instead, then looks again. Very
    /// often the two sides meet after one unfold, and the other side never has
    /// to be touched. Measured on one declaration here: of the comparisons that
    /// get past the quick tests, **31%** have two different constant heads
    /// where at least one unfolds.
    ///
    /// The height comes from `ReducibilityHints`, which Lean records for this
    /// purpose. See [`Environment::height`].
    ///
    /// Both orders give the same answer, because unfolding a definition never
    /// changes what a term means. This one just asks fewer questions.
    fn lazy_delta(&mut self, a: &Expr, b: &Expr) -> TypeResult<(Expr, Expr)> {
        let mut left = self.whnf_core(a)?;
        let mut right = self.whnf_core(b)?;
        loop {
            // Already the same, so stop before unfolding anything.
            if left.alpha_eq(&right) {
                return Ok((left, right));
            }
            let height_of = |checker: &Self, side: &Expr| -> Option<u32> {
                let (head, _) = side.unfold_apps();
                let Expr::Const { name, .. } = head else {
                    return None;
                };
                // A declaration under check has no recorded height, so treat it
                // as the shortest rather than refuse to unfold it.
                checker.env.height(name).or_else(|| {
                    checker
                        .lookup(name)
                        .and_then(|decl| decl.unfoldable_value().map(|_| 0))
                })
            };
            let tall_left = height_of(self, &left);
            let tall_right = height_of(self, &right);
            let (unfold_left, unfold_right) = match (tall_left, tall_right) {
                (None, None) => return Ok((left, right)),
                (Some(_), None) => (true, false),
                (None, Some(_)) => (false, true),
                // Equal heights give no reason to prefer one, so take both.
                (Some(x), Some(y)) => (x >= y, y >= x),
            };
            if unfold_left {
                let Some(next) = self.delta_step(&left)? else {
                    return Ok((left, right));
                };
                left = self.whnf_core(&next)?;
            }
            if unfold_right {
                let Some(next) = self.delta_step(&right)? else {
                    return Ok((left, right));
                };
                right = self.whnf_core(&next)?;
            }
        }
    }

    /// Unfolds the definition at the head of `e`, once.
    fn delta_step(&mut self, e: &Expr) -> TypeResult<Option<Expr>> {
        self.spend()?;
        let (head, borrowed) = e.unfold_apps();
        let Expr::Const { name, levels } = head else {
            return Ok(None);
        };
        // The name, and not only the rule. A row that says "lazy delta 181"
        // cannot answer "which definition started this", and that was the one
        // question chapter 17 needed it for.
        tally::bump(|| format!("lazy delta {name}"));
        let Some(decl) = self.lookup(name) else {
            return Ok(None);
        };
        let Some(value) = decl.unfoldable_value() else {
            return Ok(None);
        };
        let value = value.instantiate_levels(decl.level_params(), levels);
        Ok(Some(value.apps(borrowed.iter().map(|arg| (*arg).clone()))))
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

    /// Decides `a` and `b` by proof irrelevance, or says the rule does not
    /// apply.
    ///
    /// Three answers, not two, and the third one is the whole point:
    ///
    /// | Answer | Meaning |
    /// |---|---|
    /// | `None` | `a` is not a proof, so this rule has nothing to say. |
    /// | `Some(true)` | both sides prove the same proposition, so they are equal. |
    /// | `Some(false)` | `a` is a proof, and the two propositions are **not** equal. |
    ///
    /// That last row used to be `false`, which the caller read as "the rule did
    /// not apply" and answered by **unfolding the two proofs**. A proof of the
    /// Lean prelude is built on structural recursion, so unfolding one is
    /// hundreds of thousands of ι steps, and all of them are wasted: no
    /// reduction can make two different propositions equal.
    ///
    /// So once the kernel knows `a` is a proof, the comparison of the two
    /// propositions **is** the answer, whichever way it goes. Lean's kernel
    /// returns a three-valued `lbool` here for this reason, and the external
    /// checker `nanoda` reported the same fault from the other direction.
    ///
    /// The test needs the type of each side, so it needs both sides to be
    /// closed. A loose bound variable has no type.
    fn proof_irrelevant(&mut self, a: &Expr, b: &Expr) -> TypeResult<Option<bool>> {
        if a.has_loose_bvars() || b.has_loose_bvars() {
            return Ok(None);
        }
        // A sort and a function type are never proofs, and saying so costs one
        // test instead of three type inferences.
        //
        // `Sort u` has type `Sort (u+1)`, and a function type has type `Sort k`
        // for some `k`. The type of either is therefore a sort, and the type of
        // a sort is `Sort (k+1)`, which is never `Sort 0`. So neither can have
        // a type that is a `Prop`.
        //
        // A **lambda** is not on that list, and must not be: a proof of `p → q`
        // is a lambda.
        //
        // This rule runs on nearly every comparison, and the checker compares
        // types constantly, so most of what it meets is exactly these two
        // shapes. `infer_type` was the second heaviest frame in a profile of
        // the prelude.
        if matches!(a, Expr::Sort(_) | Expr::Forall { .. }) {
            return Ok(None);
        }
        let type_a = self.infer_type(a)?;
        // The type of the type must be `Sort 0`, which is `Prop`.
        let sort = self.infer_type(&type_a)?;
        let Expr::Sort(level) = self.whnf(&sort)? else {
            return Ok(None);
        };
        if !level.normalize().is_zero() {
            return Ok(None);
        }
        // `a` is a proof. From here the comparison of the two propositions is
        // the answer, and a `false` is as final as a `true`.
        let type_b = self.infer_type(b)?;
        Ok(Some(self.is_def_eq(&type_a, &type_b)?))
    }

    // --- the type rules --------------------------------------------------

    /// Returns the type of `e`.
    pub fn infer_type(&mut self, e: &Expr) -> TypeResult<Expr> {
        self.check_stack()?;
        // A leaf is cheaper to type than to look up, so the cache ignores one.
        if matches!(
            e,
            Expr::BVar(_) | Expr::FVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Lit(_)
        ) {
            return self.infer_type_uncached(e);
        }
        let key = e.hash_value();
        if let Some(bucket) = self.infer_cache.get(&key)
            && let Some((_, answer)) = bucket.iter().find(|(question, _)| question.alpha_eq(e))
        {
            return Ok(answer.clone());
        }
        let answer = self.infer_type_uncached(e)?;
        if self.infer_cache.len() >= CACHE_CAP {
            self.infer_cache.clear();
        }
        self.infer_cache
            .entry(key)
            .or_default()
            .push((e.clone(), answer.clone()));
        Ok(answer)
    }

    /// Returns the type of `e`, and asks no cache.
    fn infer_type_uncached(&mut self, e: &Expr) -> TypeResult<Expr> {
        // Reading a type is work, so the budget pays for it.
        //
        // It did not, for twelve chapters, and nothing showed because `whnf`
        // was charged so heavily that the budget always ran out there first.
        // The moment a step was charged for what it **adds**, inference became
        // the unbounded half: the type of a term with six hundred binders is
        // six hundred nested calls, and the budget had nothing to say about it.
        //
        // A guard that only works because another guard is too strict is not a
        // guard. Both halves of the kernel now pay for what they do.
        self.spend()?;
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
                // **Charge for the walk before making it.**
                //
                // `instantiate` rebuilds the body as a **tree**, and a term is
                // a graph, so the two sizes are not the same number. One
                // `bv_decide` lemma of Lean's `Std` has a body of 2,617,556,290
                // nodes as a tree, and that walk happens in **one call** with
                // no reduction step to charge for it. The checker ran for seven
                // minutes inside a twenty million unit budget and was then
                // killed by the operating system for its memory.
                //
                // The size is cached in every node, so asking costs nothing,
                // and it is the exact upper bound on what the walk will build.
                self.charge_walk(&body)?;
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
                return Err(TypeError::FieldTooLarge(Box::new(FieldTooLarge {
                    ctor: ctor.name.clone(),
                    inductive: inductive.name.clone(),
                    field,
                    field_level: field_level.to_string(),
                    limit: limit.to_string(),
                })));
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
        self.clear_caches();
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
