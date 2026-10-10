//! The kernel terms.
//!
//! Lean has two tree types, and the difference is the heart of the design.
//!
//! - `rean_syntax::Syntax` is what the user wrote. It keeps every bracket, it
//!   has one node kind for every notation, and a user can add new kinds.
//! - [`Expr`] is what the type checker reads. It has ten variants and no more.
//!   A user cannot add a variant.
//!
//! The elaborator turns the first into the second. It resolves names, it fills
//! implicit arguments, and it expands macros. Every rule about the meaning of a
//! program lives there, not in the kernel.
//!
//! The kernel stays small for one reason: you must trust it. The kernel is the
//! part that decides whether a proof is correct. A smaller kernel is a smaller
//! thing to trust.

pub mod environment;
pub mod expr;
pub mod level;
pub mod local;
pub mod nat_lit;
pub mod positivity;
pub mod typeck;

pub use environment::{
    AxiomVal, ConstructorVal, Declaration, DefinitionSafety, DefinitionVal, Environment,
    InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    TheoremVal,
};
pub use expr::{BinderInfo, Expr, FVarId, Literal, MVarId, Proj};
pub use level::Level;
pub use local::{LocalContext, LocalDecl};
pub use typeck::{TypeChecker, TypeError, TypeResult};
