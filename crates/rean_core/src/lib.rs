//! Shared vocabulary for the whole compiler.
//!
//! Every later stage speaks these four types:
//!
//! - [`Name`]: a hierarchical identifier, such as `Nat.succ`.
//! - [`Span`]: a byte range in one source file.
//! - [`SourceFile`] and [`SourceMap`]: the text that the compiler reads.
//! - [`Diagnostic`]: one error or warning that points at a [`Span`].

pub mod diag;
pub mod name;
pub mod source;

pub use diag::{Diagnostic, DiagnosticBag, Severity};
pub use name::Name;
pub use source::{FileId, LineCol, SourceFile, SourceMap, Span};
