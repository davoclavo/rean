//! Stage 5: **running** a term, rather than checking one.
//!
//! The kernel decides whether a term is correct. This decides what it
//! **computes to**, and those are different jobs with different rules.
//!
//! | | the kernel, stage 4 | the evaluator, stage 5 |
//! |---|---|---|
//! | asks | is this term correct? | what does it come to? |
//! | universes | compares them, substitutes them | **ignores** them |
//! | types | infers them, compares them | ignores them |
//! | proofs | checks them | never looks inside one |
//! | order | reduces the head, weakly | reduces to a value, by need |
//! | budget | fuel, per declaration | a step count, so a loop ends |
//!
//! Three of those rows are why this is so much faster than asking `whnf` for
//! the same answer. The kernel substitutes a universe argument into the value
//! of every definition it unfolds, because a `Sort` has to be compared later.
//! Nothing here will ever compare a `Sort`, so the universes are dropped on
//! the floor.
//!
//! # Why it is lazy
//!
//! An argument becomes a [`Thunk`], and a thunk is forced at most once.
//!
//! That is not a taste in semantics. An elaborated Lean term carries arguments
//! that **must not** be evaluated: the type arguments of a polymorphic
//! function, and the proofs that a dependent function asks for. Lean's own
//! compiler erases them, which it can do because it knows their types. This
//! evaluator has no types, so it does the next best thing and never forces
//! what it is not asked for.
//!
//! The same property makes `Nat.brecOn` affordable. Its course-of-values table
//! holds an answer for every smaller number, and a lazy table only computes the
//! entries that somebody projects.
//!
//! # What it is not
//!
//! It is a tree walking evaluator, not a compiler to machine code. Lean's own
//! stage 5 lowers to LCNF and then to C. This is the step before that, and the
//! roadmap says so: "the kernel term becomes LCNF, then C code **or an
//! interpreter call**".

use rean_core::Name;
use rean_kernel::{Declaration, Environment, Expr, Literal, QuotKind};
use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

mod prim;
pub use prim::{Binop, Compare, Prim};

/// What an `IO` action that worked gives back, by the names Lean has used.
///
/// The first one the environment holds is the one to build. See
/// `Evaluator::io_ok`.
const IO_OK: [&str; 2] = ["EST.Out.ok", "EStateM.Result.ok"];

/// How many steps one evaluation may take.
///
/// A Lean program can loop: `partial def` exists, and a term the kernel never
/// checked can be anything at all. The budget is the same answer the kernel
/// gives, for the same reason, and it is reported rather than hidden.
pub const STEPS: u64 = 50_000_000;

/// How deep the evaluator will recurse.
///
/// The walk is a Rust recursion, so the depth of a term is the depth of the
/// stack. Chapter 24 learned this the hard way in the kernel, where a run died
/// of a 32 GB stack before it could spend its budget.
pub const DEPTH: u32 = 10_000;

/// Why an evaluation stopped.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum EvalError {
    /// The environment holds no declaration of this name.
    Unknown(Name),
    /// A bound variable pointed outside the term.
    LooseBVar(u32),
    /// The evaluation took more than [`STEPS`] steps.
    OutOfSteps(u64),
    /// The evaluation recursed more than [`DEPTH`] levels.
    TooDeep(u32),
    /// A thunk asked for its own value. A term the kernel accepted cannot do
    /// this, so it means the term never was checked.
    Cycle,
    /// The arithmetic left the range of a `u128`.
    ///
    /// A Lean `Nat` has no upper bound and this evaluator holds one in a
    /// machine integer, exactly as `rean_kernel::nat_lit` does. The limit is
    /// named rather than wrapped, because a wrong number is worse than no
    /// number.
    PastU128(&'static str),
    /// A projection asked for a field of something that is not a constructor.
    NotAStructure(String),
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::Unknown(name) => write!(f, "unknown constant `{name}`"),
            EvalError::LooseBVar(index) => {
                write!(f, "bound variable #{index} points outside the term")
            }
            EvalError::OutOfSteps(steps) => write!(
                f,
                "the evaluation took more than {steps} steps, so it was stopped"
            ),
            EvalError::TooDeep(depth) => {
                write!(f, "the evaluation recursed more than {depth} levels deep")
            }
            EvalError::Cycle => f.write_str(
                "a value asked for itself. The kernel refuses a term that can do \
                 this, so this term was never checked",
            ),
            EvalError::PastU128(op) => write!(
                f,
                "`{op}` left the range of a 128 bit number. A Lean `Nat` has no \
                 upper bound and this evaluator does"
            ),
            EvalError::NotAStructure(what) => {
                write!(f, "a projection asked for a field of {what}")
            }
        }
    }
}

impl std::error::Error for EvalError {}

/// The result of running something.
pub type EvalResult<T> = Result<T, EvalError>;

/// What a term comes to.
#[derive(Clone, Debug)]
pub enum Value {
    /// A natural number, in a machine integer.
    ///
    /// `Nat.zero` and `Nat.succ` build one of these rather than a constructor
    /// application, so that arithmetic is arithmetic and not a tower.
    Nat(u128),
    /// A string literal.
    Str(Rc<str>),
    /// A constructor, with the arguments it has been given.
    ///
    /// The arguments are thunks, so `List.cons x xs` holds the tail without
    /// evaluating it.
    Ctor { name: Name, args: Vec<Thunk> },
    /// A function waiting for its next argument.
    Closure { body: Expr, env: Env },
    /// Something that cannot reduce: a type, a proof, an axiom, an opaque
    /// definition, or a free variable.
    ///
    /// The evaluator never looks inside one. That is what makes it safe to
    /// pass a proof to a function that ignores it.
    Opaque { head: Name, args: Vec<Thunk> },
}

impl Value {
    /// Returns the number, if this value is one.
    pub fn as_nat(&self) -> Option<u128> {
        match self {
            Value::Nat(n) => Some(*n),
            _ => None,
        }
    }
}

/// An argument that has not been evaluated yet, or has been evaluated once.
#[derive(Clone, Debug)]
pub struct Thunk(Rc<RefCell<ThunkState>>);

#[derive(Debug)]
enum ThunkState {
    /// Not yet forced.
    Waiting(Expr, Env),
    /// Being forced. Meeting this is a cycle.
    Running,
    /// Forced, and this is the answer.
    Done(Value),
}

impl Thunk {
    /// Makes a thunk that will evaluate `expr` in `env`.
    pub fn waiting(expr: Expr, env: Env) -> Thunk {
        Thunk(Rc::new(RefCell::new(ThunkState::Waiting(expr, env))))
    }

    /// Makes a thunk that is already a value.
    pub fn done(value: Value) -> Thunk {
        Thunk(Rc::new(RefCell::new(ThunkState::Done(value))))
    }
}

/// The values that the bound variables of a term stand for.
///
/// A list and not a vector, because a closure keeps the environment it was
/// made in and many closures share a tail. De Bruijn index zero is the front.
#[derive(Clone, Debug, Default)]
pub struct Env(Option<Rc<EnvNode>>);

#[derive(Debug)]
struct EnvNode {
    head: Thunk,
    tail: Env,
}

impl Env {
    /// The empty environment.
    pub fn new() -> Env {
        Env(None)
    }

    /// Returns a new environment with `thunk` at index zero.
    pub fn with(&self, thunk: Thunk) -> Env {
        Env(Some(Rc::new(EnvNode {
            head: thunk,
            tail: self.clone(),
        })))
    }

    /// Returns what the bound variable at `index` stands for.
    fn get(&self, index: u32) -> Option<&Thunk> {
        let mut node = self.0.as_deref()?;
        for _ in 0..index {
            node = node.tail.0.as_deref()?;
        }
        Some(&node.head)
    }
}

/// Runs terms against one environment of declarations.
pub struct Evaluator<'e> {
    env: &'e Environment,
    steps: u64,
    depth: u32,
    deepest: u32,
}

impl<'e> Evaluator<'e> {
    /// Builds an evaluator over the declarations in `env`.
    pub fn new(env: &'e Environment) -> Evaluator<'e> {
        Evaluator {
            env,
            steps: STEPS,
            depth: 0,
            deepest: 0,
        }
    }

    /// Sets how many steps one evaluation may take. See [`STEPS`].
    pub fn set_steps(&mut self, steps: u64) {
        self.steps = steps;
    }

    /// Returns how many steps are left.
    pub fn steps_left(&self) -> u64 {
        self.steps
    }

    /// Returns the deepest recursion of the last evaluation.
    pub fn deepest(&self) -> u32 {
        self.deepest
    }

    /// Spends one step.
    fn step(&mut self) -> EvalResult<()> {
        match self.steps.checked_sub(1) {
            Some(left) => {
                self.steps = left;
                Ok(())
            }
            None => Err(EvalError::OutOfSteps(STEPS)),
        }
    }

    /// Runs the value of the declaration called `name`.
    pub fn run(&mut self, name: &Name) -> EvalResult<Value> {
        let decl = self
            .env
            .get(name)
            .ok_or_else(|| EvalError::Unknown(name.clone()))?;
        match decl.value() {
            Some(body) => self.eval(&body.clone(), &Env::new()),
            // An axiom or an inductive type has nothing to run.
            None => Ok(Value::Opaque {
                head: name.clone(),
                args: Vec::new(),
            }),
        }
    }

    /// Evaluates `expr` in `env`, to a value.
    pub fn eval(&mut self, expr: &Expr, env: &Env) -> EvalResult<Value> {
        self.step()?;
        if self.depth >= DEPTH {
            return Err(EvalError::TooDeep(DEPTH));
        }
        self.depth += 1;
        if self.depth > self.deepest {
            self.deepest = self.depth;
        }
        let out = self.eval_inner(expr, env);
        self.depth -= 1;
        out
    }

    fn eval_inner(&mut self, expr: &Expr, env: &Env) -> EvalResult<Value> {
        match expr {
            Expr::BVar(index) => {
                let thunk = env.get(*index).ok_or(EvalError::LooseBVar(*index))?.clone();
                self.force(&thunk)
            }
            Expr::Lit(Literal::Nat(digits)) => match digits.parse::<u128>() {
                Ok(n) => Ok(Value::Nat(n)),
                Err(_) => Err(EvalError::PastU128("a literal")),
            },
            Expr::Lit(Literal::Str(text)) => Ok(Value::Str(Rc::from(&**text))),
            Expr::Lam { body, .. } => Ok(Value::Closure {
                body: body.to_expr(),
                env: env.clone(),
            }),
            // A function **type** is not a function. Nothing will look inside
            // it, so it is opaque, and `Sort` is the same.
            Expr::Forall { .. } | Expr::Sort(_) => Ok(Value::Opaque {
                head: Name::from_dotted("Sort"),
                args: Vec::new(),
            }),
            Expr::Let { value, body, .. } => {
                let bound = Thunk::waiting(value.to_expr(), env.clone());
                self.eval(&body.to_expr(), &env.with(bound))
            }
            Expr::Proj(proj) => {
                let whole = self.eval(&proj.value.to_expr(), env)?;
                self.project(&whole, proj.index)
            }
            Expr::App { .. } => {
                let (head, args) = expr.unfold_apps();
                let args: Vec<Thunk> = args
                    .iter()
                    .map(|arg| Thunk::waiting((*arg).clone(), env.clone()))
                    .collect();
                self.apply_head(head, args, env)
            }
            Expr::Const { name, .. } => self.constant(name, Vec::new()),
            Expr::FVar(id) => Ok(Value::Opaque {
                head: Name::from_dotted(&format!("_f{}", id.0)),
                args: Vec::new(),
            }),
            Expr::MVar(id) => Ok(Value::Opaque {
                head: Name::from_dotted(&format!("_m{}", id.0)),
                args: Vec::new(),
            }),
        }
    }

    /// Evaluates the head of an application and gives it the arguments.
    fn apply_head(&mut self, head: &Expr, args: Vec<Thunk>, env: &Env) -> EvalResult<Value> {
        match head {
            // The common case, and the one worth taking apart: a constant
            // applied to a spine. Going through `eval` for the head would make
            // a closure and then take it apart again.
            Expr::Const { name, .. } => self.constant(name, args),
            _ => {
                let head = self.eval(head, env)?;
                self.apply(head, args)
            }
        }
    }

    /// Gives `args` to `value`.
    pub fn apply(&mut self, value: Value, mut args: Vec<Thunk>) -> EvalResult<Value> {
        if args.is_empty() {
            return Ok(value);
        }
        match value {
            Value::Closure { body, env } => {
                let first = args.remove(0);
                let inner = self.eval(&body, &env.with(first))?;
                self.apply(inner, args)
            }
            Value::Ctor {
                name,
                args: mut given,
            } => {
                given.append(&mut args);
                Ok(Value::Ctor { name, args: given })
            }
            Value::Opaque {
                head,
                args: mut given,
            } => {
                given.append(&mut args);
                // **A constant that is waiting has to be asked again.**
                //
                // `Nat.add` is usually the head of an application, and
                // `constant` sees it there and runs the primitive. But an
                // instance hides it: `HAdd.hAdd ... (instHAdd Nat instAddNat)`
                // **projects** `Nat.add` out of a structure, so it arrives here
                // as a value with no arguments, and the arguments arrive after
                // it. Appending them and stopping is how `2 + 2` came to
                // `Nat.add ..2` instead of `4`.
                //
                // A head that the environment knows, or that is a primitive,
                // goes back through `constant` with everything it now has. A
                // head that nothing knows is a `Sort` or a free variable, and
                // those really are opaque.
                if Prim::of(&head).is_some() || self.env.get(&head).is_some() {
                    return self.constant(&head, given);
                }
                Ok(Value::Opaque { head, args: given })
            }
            // A number or a string is not a function. A term the kernel
            // accepted cannot apply one, so this is opaque rather than an
            // error: the evaluator reports what it has, and the checker is the
            // part that refuses nonsense.
            other => Ok(other),
        }
    }

    /// Forces a thunk, at most once. See [`Self::force`].
    pub fn force_thunk(&mut self, thunk: &Thunk) -> EvalResult<Value> {
        self.force(thunk)
    }

    /// Forces a thunk, at most once.
    pub fn force(&mut self, thunk: &Thunk) -> EvalResult<Value> {
        {
            let state = thunk.0.borrow();
            match &*state {
                ThunkState::Done(value) => return Ok(value.clone()),
                ThunkState::Running => return Err(EvalError::Cycle),
                ThunkState::Waiting(..) => {}
            }
        }
        let (expr, env) = {
            let mut state = thunk.0.borrow_mut();
            match std::mem::replace(&mut *state, ThunkState::Running) {
                ThunkState::Waiting(expr, env) => (expr, env),
                // Another borrow changed it under us, which cannot happen on
                // one thread, and the compiler does not know that.
                other => {
                    *state = other;
                    return Err(EvalError::Cycle);
                }
            }
        };
        let value = self.eval(&expr, &env)?;
        *thunk.0.borrow_mut() = ThunkState::Done(value.clone());
        Ok(value)
    }

    /// Takes field `index` out of a structure value.
    pub(crate) fn project(&mut self, whole: &Value, index: u32) -> EvalResult<Value> {
        match whole {
            Value::Ctor { name, args } => {
                let params = self
                    .env
                    .get(name)
                    .and_then(|decl| match decl {
                        Declaration::Constructor(ctor) => Some(ctor.num_params),
                        _ => None,
                    })
                    .unwrap_or(0);
                let slot = params as usize + index as usize;
                match args.get(slot) {
                    Some(field) => self.force(&field.clone()),
                    None => Err(EvalError::NotAStructure(format!(
                        "`{name}`, which has no field {index}"
                    ))),
                }
            }
            Value::Opaque { head, .. } => Err(EvalError::NotAStructure(format!("`{head}`"))),
            other => Err(EvalError::NotAStructure(format!("{}", Shown(other, 1)))),
        }
    }

    /// Evaluates a constant applied to `args`.
    fn constant(&mut self, name: &Name, args: Vec<Thunk>) -> EvalResult<Value> {
        // A primitive first. `Nat.add` on two numbers is one instruction here
        // and a tower of `Nat.succ` without this.
        if let Some(prim) = Prim::of(name) {
            return self.primitive(prim, name, args);
        }
        let Some(decl) = self.env.get(name) else {
            return Err(EvalError::Unknown(name.clone()));
        };
        match decl {
            Declaration::Constructor(ctor) => {
                let name = ctor.name.clone();
                Ok(Value::Ctor { name, args })
            }
            Declaration::Recursor(_) => self.recurse(name, args),
            Declaration::Quot(_) => self.quotient(name, args),
            // A definition, a theorem, or an opaque with a value.
            _ => match decl.value() {
                Some(body) => {
                    let body = body.clone();
                    let head = self.eval(&body, &Env::new())?;
                    self.apply(head, args)
                }
                // An axiom or an inductive type. Nothing to run, and
                // nothing will look inside.
                //
                // An `Opaque` takes the arm above, because it does have a
                // value. Opacity hides that value from the kernel's δ rule,
                // which is a statement about proofs. It does not mean the
                // program cannot run it.
                None => Ok(Value::Opaque {
                    head: name.clone(),
                    args,
                }),
            },
        }
    }
}

impl Evaluator<'_> {
    /// Applies the ι rule: a recursor meets a constructor.
    ///
    /// The shape is the kernel's, in [`rean_kernel`], and the difference is
    /// what is **not** here. No universe substitution, because nothing will
    /// compare a `Sort`. No fuel charged by the size of the result, because
    /// nothing is being proved. And the rule's right hand side is evaluated
    /// once into a closure, which the arguments then enter one at a time.
    fn recurse(&mut self, name: &Name, args: Vec<Thunk>) -> EvalResult<Value> {
        let Some(Declaration::Recursor(rec)) = self.env.get(name) else {
            return Err(EvalError::Unknown(name.clone()));
        };
        let rec = rec.clone();
        let major_index = rec.major_index();
        if args.len() <= major_index {
            // Not applied far enough to take anything apart. It is still a
            // function, and the next application will ask again.
            return Ok(Value::Opaque {
                head: name.clone(),
                args,
            });
        }
        let major = self.force(&args[major_index])?;
        // A number has to behave like a constructor application here, exactly
        // as it does in the kernel: `3` is `Nat.succ 2` when a recursor asks.
        let (ctor, fields): (Name, Vec<Thunk>) = match &major {
            Value::Nat(0) => (Name::from_dotted("Nat.zero"), Vec::new()),
            Value::Nat(n) => (
                Name::from_dotted("Nat.succ"),
                vec![Thunk::done(Value::Nat(n - 1))],
            ),
            Value::Ctor { name, args } => (name.clone(), args.clone()),
            // A proof, an axiom or a free variable. `Eq.rec` on one of those
            // is where the kernel has its K-like rule, and running a program
            // never needs it: the motive is a proof and nobody looks.
            _ => {
                return Ok(Value::Opaque {
                    head: name.clone(),
                    args,
                });
            }
        };
        let Some(rule) = rec.rule_for(&ctor) else {
            return Ok(Value::Opaque {
                head: name.clone(),
                args,
            });
        };
        let wanted = rule.num_fields as usize;
        if fields.len() < wanted {
            return Ok(Value::Opaque {
                head: name.clone(),
                args,
            });
        }
        // The rule takes the parameters, the motives and the minor premises,
        // then the fields of the constructor, then whatever followed the major
        // premise.
        let mut spine: Vec<Thunk> = args[..rec.num_prefix()].to_vec();
        spine.extend(fields[fields.len() - wanted..].iter().cloned());
        spine.extend(args[major_index + 1..].iter().cloned());
        let head = self.eval(&rule.rhs.clone(), &Env::new())?;
        self.apply(head, spine)
    }

    /// Applies a quotient rule: `Quot.lift f h (Quot.mk r a)` runs `f a`.
    ///
    /// `Quot` is a kernel primitive, so it cannot be a definition and it needs
    /// its own rule here as well. The argument positions are the ones the
    /// kernel uses.
    fn quotient(&mut self, name: &Name, args: Vec<Thunk>) -> EvalResult<Value> {
        let Some(Declaration::Quot(quot)) = self.env.get(name) else {
            return Err(EvalError::Unknown(name.clone()));
        };
        let (function_index, major_index) = match quot.kind {
            QuotKind::Lift => (3usize, 5usize),
            QuotKind::Ind => (3usize, 4usize),
            // `Quot` itself is a type and `Quot.mk` is its constructor.
            QuotKind::Type => {
                return Ok(Value::Opaque {
                    head: name.clone(),
                    args,
                });
            }
            QuotKind::Ctor => {
                return Ok(Value::Ctor {
                    name: name.clone(),
                    args,
                });
            }
        };
        if args.len() <= major_index {
            return Ok(Value::Opaque {
                head: name.clone(),
                args,
            });
        }
        let major = self.force(&args[major_index])?;
        // `Quot.mk α r a` carries the value in its third argument.
        let Value::Ctor {
            name: mk,
            args: mk_args,
        } = &major
        else {
            return Ok(Value::Opaque {
                head: name.clone(),
                args,
            });
        };
        if mk_args.len() < 3
            || !matches!(self.env.get(mk), Some(Declaration::Quot(d)) if d.kind == QuotKind::Ctor)
        {
            return Ok(Value::Opaque {
                head: name.clone(),
                args,
            });
        }
        let function = self.force(&args[function_index])?;
        let mut spine = vec![mk_args[2].clone()];
        spine.extend(args[major_index + 1..].iter().cloned());
        self.apply(function, spine)
    }
}

impl Evaluator<'_> {
    /// Returns the text of a value, if it is a string.
    ///
    /// # Ask Lean, do not model the representation
    ///
    /// The first version of this knew what a `String` **is**: a structure over
    /// a `List Char`. That was true of Lean once and it is not true of 4.35,
    /// where a string is a byte array and `String.mk` goes through
    /// `String.ofByteArray`. So `toString` of a list came to
    /// `String.push ..2`, a primitive that had declined, and the program
    /// stopped with a message about a projection.
    ///
    /// So this asks **Lean's own function**, `String.toList`, and walks the
    /// list it gives back. The decoding that function does is real work, and
    /// it is the `utf8DecodeChar` family that chapters 24 and 25 found so
    /// expensive **to check**. Running it is cheap.
    ///
    /// A literal is still a literal, and that is the fast path.
    pub fn text_of(&mut self, value: &Value) -> EvalResult<Option<String>> {
        if let Value::Str(text) = value {
            return Ok(Some(text.to_string()));
        }
        if !matches!(value, Value::Ctor { .. }) {
            return Ok(None);
        }
        let Some(list) = self.ask(&["String.toList", "String.data"], value)? else {
            return Ok(None);
        };
        let mut out = String::new();
        let mut current = list;
        // One cell at a time, so a long string is a loop and not a recursion.
        loop {
            let Value::Ctor { name, args } = &current else {
                return Ok(None);
            };
            match name.last_str() {
                Some("nil") => return Ok(Some(out)),
                Some("cons") if args.len() >= 2 => {
                    let head = self.force(&args[args.len() - 2].clone())?;
                    let Some(code) = self.code_point(&head)? else {
                        return Ok(None);
                    };
                    match char::from_u32(code) {
                        Some(ch) => out.push(ch),
                        None => return Ok(None),
                    }
                    current = self.force(&args[args.len() - 1].clone())?;
                }
                _ => return Ok(None),
            }
        }
    }

    /// Returns the code point of a `Char`.
    ///
    /// Through `Char.toNat`, for the reason [`Self::text_of`] gives: a `Char`
    /// is a structure around a `UInt32` around a `Fin` around a `Nat` in one
    /// version of Lean and something else in the next, and the function that
    /// reads it is stable.
    pub fn code_point(&mut self, value: &Value) -> EvalResult<Option<u32>> {
        if let Value::Nat(n) = value {
            return Ok(u32::try_from(*n).ok());
        }
        match self.ask(&["Char.toNat", "Char.val"], value)? {
            Some(Value::Nat(n)) => Ok(u32::try_from(n).ok()),
            _ => Ok(None),
        }
    }

    /// Applies the first of `names` that the environment holds to `value`.
    ///
    /// This is how the runtime reads a value whose **shape** belongs to the
    /// library rather than to the kernel. A name that Lean renamed is a silent
    /// failure otherwise, and this evaluator has had two of those already.
    fn ask(&mut self, names: &[&str], value: &Value) -> EvalResult<Option<Value>> {
        for candidate in names {
            let name = Name::from_dotted(candidate);
            if self.env.contains(&name) {
                let arg = Thunk::done(value.clone());
                return Ok(Some(self.constant(&name, vec![arg])?));
            }
        }
        Ok(None)
    }

    /// Writes text, as a program's output and not as a report.
    ///
    /// The driver prints its own lines to the standard output as well, so a
    /// reader has to be able to tell which lines are the **program's**. Those
    /// go out as they are; everything the driver says about them is prefixed.
    pub(crate) fn write(&mut self, text: &str, newline: bool) {
        use std::io::Write as _;
        let mut out = std::io::stdout();
        let _ = out.write_all(text.as_bytes());
        if newline {
            let _ = out.write_all(b"\n");
        }
        let _ = out.flush();
    }

    /// Returns the value an `IO` action gives back when it worked.
    ///
    /// The shape is `ok () world`: three implicit type arguments, then the
    /// value, then the state. Nothing looks at the three, because a `match` on
    /// this takes the **last two** arguments and the recursor knows how many
    /// fields there are.
    ///
    /// The **name** is asked of the environment rather than written here.
    /// Lean 4.35 calls it `EST.Out.ok`, with the state typed `Void σ`, and
    /// earlier versions call it `EStateM.Result.ok`. A hardcoded name is a
    /// silent failure one Lean release later: the recursor finds no rule for
    /// the constructor it was handed, stops, and the program runs its **first**
    /// statement and no more. That is how this was found.
    fn io_ok(&self, world: Thunk) -> EvalResult<Value> {
        let hidden = || {
            Thunk::done(Value::Opaque {
                head: Name::from_dotted("Sort"),
                args: Vec::new(),
            })
        };
        let name = IO_OK
            .iter()
            .map(|candidate| Name::from_dotted(candidate))
            .find(|candidate| self.env.contains(candidate))
            .ok_or_else(|| EvalError::Unknown(Name::from_dotted(IO_OK[0])))?;
        Ok(Value::Ctor {
            name,
            args: vec![
                hidden(),
                hidden(),
                hidden(),
                Thunk::done(Value::Ctor {
                    name: Name::from_dotted("Unit.unit"),
                    args: Vec::new(),
                }),
                world,
            ],
        })
    }

    /// Prints a value, forcing what it meets, to a bounded depth.
    ///
    /// [`Shown`] cannot force anything, because it only has the value, so it
    /// prints an argument that nobody has evaluated as `_`. For a **result**
    /// that is the wrong answer: `names = List.cons _ _ _` is true and tells
    /// the reader nothing. This forces as it goes.
    ///
    /// A value whose head is a `String` is asked for its text first, so a
    /// string that the program **built** prints as a string and not as the
    /// byte array it is made of.
    pub fn show_deep(&mut self, value: &Value, depth: u32) -> EvalResult<String> {
        let looks_like_a_string = match value {
            Value::Ctor { name, .. } | Value::Opaque { head: name, .. } => {
                name.to_string().starts_with("String")
            }
            _ => false,
        };
        if looks_like_a_string && let Some(text) = self.text_of(value)? {
            return Ok(format!("{text:?}"));
        }
        Ok(match value {
            Value::Nat(n) => n.to_string(),
            Value::Str(text) => format!("{text:?}"),
            Value::Closure { .. } => "<function>".to_string(),
            Value::Opaque { head, args } if args.is_empty() => head.to_string(),
            Value::Opaque { head, args } => format!("{head} ..{}", args.len()),
            Value::Ctor { name, args } if args.is_empty() => name.to_string(),
            // A list reads as a list. `List.cons α x (List.cons α y ..)` is
            // what it **is**, and `[x, y]` is what it says.
            Value::Ctor { name, .. } if name.to_string().starts_with("List.") => {
                let mut items: Vec<String> = Vec::new();
                let mut current = value.clone();
                let mut left = 100;
                loop {
                    let Value::Ctor { name, args } = &current else {
                        break;
                    };
                    match name.last_str() {
                        Some("nil") => break,
                        Some("cons") if args.len() >= 2 => {
                            if left == 0 {
                                items.push("..".to_string());
                                break;
                            }
                            left -= 1;
                            let head = self.force(&args[args.len() - 2].clone())?;
                            items.push(self.show_deep(&head, depth.saturating_sub(1))?);
                            current = self.force(&args[args.len() - 1].clone())?;
                        }
                        _ => break,
                    }
                }
                format!("[{}]", items.join(", "))
            }
            Value::Ctor { name, args } => {
                if depth == 0 {
                    return Ok(format!("{name} .."));
                }
                let mut out = name.to_string();
                for arg in args.clone() {
                    // An argument that cannot be forced is left as it is. The
                    // printer must not fail where the program did not.
                    match self.force(&arg) {
                        Ok(inner) => {
                            let shown = self.show_deep(&inner, depth - 1)?;
                            out.push_str(&format!(" ({shown})"));
                        }
                        Err(_) => out.push_str(" _"),
                    }
                }
                out
            }
        })
    }

    /// Runs a program: the value of `name`, given a world to act on.
    ///
    /// An `IO a` in Lean is a function from the state of the world, so running
    /// one means handing it that state. Nothing looks inside the token, and
    /// that is the whole of our `IO.RealWorld`.
    pub fn run_main(&mut self, name: &Name) -> EvalResult<Value> {
        let action = self.run(name)?;
        let world = Thunk::done(Value::Opaque {
            head: Name::from_dotted("IO.RealWorld"),
            args: Vec::new(),
        });
        self.apply(action, vec![world])
    }
}

/// A value, printed to a bounded depth. See [`Value`].
pub struct Shown<'v>(pub &'v Value, pub u32);

impl fmt::Display for Shown<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Shown(value, depth) = self;
        match value {
            Value::Nat(n) => write!(f, "{n}"),
            Value::Str(text) => write!(f, "{text:?}"),
            Value::Closure { .. } => f.write_str("<function>"),
            Value::Opaque { head, args } => {
                if args.is_empty() {
                    write!(f, "{head}")
                } else {
                    write!(f, "{head} ..{}", args.len())
                }
            }
            Value::Ctor { name, args } => {
                if *depth == 0 {
                    return write!(f, "{name} ..");
                }
                write!(f, "{name}")?;
                for arg in args {
                    match &*arg.0.borrow() {
                        ThunkState::Done(value) => write!(f, " ({})", Shown(value, depth - 1))?,
                        _ => f.write_str(" _")?,
                    }
                }
                Ok(())
            }
        }
    }
}
