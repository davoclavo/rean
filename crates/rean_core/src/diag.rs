//! Diagnostics.
//!
//! A compiler must not stop at the first error. Each stage puts a
//! [`Diagnostic`] into a [`DiagnosticBag`] and then continues with a repair.
//! The driver prints the bag at the end.
//!
//! This design is the reason that the syntax tree needs a `Missing` node. The
//! parser reports an error, puts `Missing` in the hole, and keeps going.

use crate::source::{SourceFile, Span};
use std::fmt::Write as _;

/// How serious a diagnostic is.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Severity {
    /// The compiler prints information, such as the output of `#eval`.
    Info,
    /// The code is suspect, but the compiler can continue.
    Warning,
    /// The code is wrong. The compiler must not emit a result.
    Error,
}

impl Severity {
    /// Returns the word that the compiler prints for this severity.
    pub fn label(&self) -> &'static str {
        match self {
            Severity::Info => "info",
            Severity::Warning => "warning",
            Severity::Error => "error",
        }
    }
}

/// One message that points at a range of source text.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    pub span: Span,
    pub message: String,
    /// Extra lines that help the reader. Each line is one hint.
    pub notes: Vec<String>,
}

impl Diagnostic {
    /// Builds an error.
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Diagnostic {
            severity: Severity::Error,
            span,
            message: message.into(),
            notes: Vec::new(),
        }
    }

    /// Builds a warning.
    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Diagnostic {
            severity: Severity::Warning,
            span,
            message: message.into(),
            notes: Vec::new(),
        }
    }

    /// Adds a hint to the diagnostic.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Renders the diagnostic as text, with the source line and a caret bar.
    pub fn render(&self, file: &SourceFile) -> String {
        let start = file.line_col(self.span.start);
        let mut out = String::new();
        let _ = writeln!(
            out,
            "{}: {}\n  --> {}:{}",
            self.severity.label(),
            self.message,
            file.path(),
            start
        );

        if let Some(text) = file.line_text(start.line) {
            let gutter = start.line.to_string();
            let pad = " ".repeat(gutter.len());
            let end = file.line_col(self.span.end);
            // A span that crosses a line break gets a caret bar to the line end.
            let width = if end.line == start.line {
                (end.col - start.col).max(1)
            } else {
                (text.chars().count() as u32 + 1 - start.col).max(1)
            };
            let _ = writeln!(out, "{pad} |");
            let _ = writeln!(out, "{gutter} | {text}");
            let _ = writeln!(
                out,
                "{pad} | {}{}",
                " ".repeat(start.col as usize - 1),
                "^".repeat(width as usize)
            );
        }

        for note in &self.notes {
            let _ = writeln!(out, "  note: {note}");
        }
        out
    }
}

/// Every diagnostic from one run, in the order that the stages reported them.
#[derive(Default, Debug)]
pub struct DiagnosticBag {
    items: Vec<Diagnostic>,
}

impl DiagnosticBag {
    /// Builds an empty bag.
    pub fn new() -> Self {
        DiagnosticBag::default()
    }

    /// Adds a diagnostic to the bag.
    pub fn push(&mut self, diag: Diagnostic) {
        self.items.push(diag);
    }

    /// Returns every diagnostic in the bag.
    pub fn items(&self) -> &[Diagnostic] {
        &self.items
    }

    /// Returns `true` if the bag holds no diagnostic.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Returns the number of diagnostics in the bag.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Returns `true` if the bag holds at least one error.
    pub fn has_errors(&self) -> bool {
        self.items.iter().any(|d| d.severity == Severity::Error)
    }

    /// Returns the number of errors in the bag.
    pub fn error_count(&self) -> usize {
        self.items
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count()
    }

    /// Renders every diagnostic in the bag.
    pub fn render(&self, file: &SourceFile) -> String {
        self.items.iter().map(|d| d.render(file)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{Diagnostic, DiagnosticBag};
    use crate::source::{SourceMap, Span};

    #[test]
    fn render_shows_the_line_and_the_caret() {
        let mut map = SourceMap::new();
        let id = map.add("a.lean", "def f := bogus\n");
        let diag = Diagnostic::error(Span::new(9, 14), "unknown identifier 'bogus'")
            .with_note("did you mean 'bogon'?");
        let text = diag.render(map.file(id));
        assert!(text.contains("error: unknown identifier 'bogus'"), "{text}");
        assert!(text.contains("--> a.lean:1:10"), "{text}");
        assert!(text.contains("1 | def f := bogus"), "{text}");
        assert!(text.contains("^^^^^"), "{text}");
        assert!(text.contains("note: did you mean 'bogon'?"), "{text}");
    }

    #[test]
    fn empty_span_still_gets_one_caret() {
        let mut map = SourceMap::new();
        let id = map.add("a.lean", "def f :=\n");
        let diag = Diagnostic::error(Span::empty(8), "expected a term");
        let text = diag.render(map.file(id));
        assert!(text.contains(" | "));
        assert!(text.contains('^'), "{text}");
    }

    #[test]
    fn bag_counts_only_errors() {
        let mut bag = DiagnosticBag::new();
        bag.push(Diagnostic::warning(Span::empty(0), "unused variable"));
        assert!(!bag.has_errors());
        bag.push(Diagnostic::error(Span::empty(0), "type mismatch"));
        assert!(bag.has_errors());
        assert_eq!(bag.len(), 2);
        assert_eq!(bag.error_count(), 1);
    }
}
