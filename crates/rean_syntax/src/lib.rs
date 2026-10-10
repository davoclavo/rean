//! The syntax tree.
//!
//! Most compilers give each construct its own struct. Lean does not. Lean has
//! one tree type for every construct, and the node kind is a [`Name`] such as
//! `Lean.Parser.Term.app`.
//!
//! The reason is the macro system. A `macro_rules` command writes a tree, and a
//! `syntax` command declares a new node kind. A fixed set of Rust enum variants
//! could not hold a kind that a user invents at run time. A [`Name`] can.
//!
//! The tree keeps every token, including the keywords and the brackets. The
//! tree is therefore lossless. A pretty printer and a language server both
//! need that.
//!
//! The price is that a later stage cannot trust the shape of a node. Stage 2,
//! the elaborator, checks the shape and turns the tree into a
//! `rean_kernel::Expr`, which does have one variant per construct.

pub mod kind;

use rean_core::{Name, Span};
use rean_lexer::{Token, TokenKind};
use std::fmt;
use std::fmt::Write as _;
use std::sync::Arc;

/// One node of the syntax tree.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Syntax {
    /// A hole where the parser found an error.
    ///
    /// The parser reports a diagnostic and puts this node in place of the part
    /// that it could not read. The rest of the file still gets a tree, so the
    /// compiler reports many errors in one run.
    Missing,
    /// A keyword, a symbol, or a literal. The tree keeps the source text.
    Atom { span: Span, value: Arc<str> },
    /// A name.
    Ident {
        span: Span,
        /// The text as the file holds it, such as `«has space»`.
        raw: Arc<str>,
        /// The name after the lexer removes the quotes.
        name: Name,
    },
    /// A construct with children.
    Node {
        /// The kind of the node, such as `Lean.Parser.Term.app`.
        kind: Name,
        span: Span,
        args: Vec<Syntax>,
    },
}

impl Syntax {
    /// Builds a node and computes its span from its children.
    pub fn node(kind: impl Into<Name>, args: Vec<Syntax>) -> Syntax {
        let span = args
            .iter()
            .filter_map(Syntax::span)
            .reduce(|a, b| a.to(b))
            .unwrap_or(Span::empty(0));
        Syntax::Node {
            kind: kind.into(),
            span,
            args,
        }
    }

    /// Builds an atom.
    pub fn atom(span: Span, value: impl Into<Arc<str>>) -> Syntax {
        Syntax::Atom {
            span,
            value: value.into(),
        }
    }

    /// Builds a leaf from one token.
    ///
    /// A literal becomes an atom that holds the source text, because the tree
    /// must stay lossless. The elaborator reads the value again later.
    pub fn from_token(token: &Token, source: &str) -> Syntax {
        let span = token.span;
        let raw = || Arc::<str>::from(&source[span.range()]);
        match &token.kind {
            TokenKind::Ident { name, raw } => Syntax::Ident {
                span,
                raw: raw.clone(),
                name: name.clone(),
            },
            TokenKind::Keyword(text) | TokenKind::Symbol(text) => Syntax::Atom {
                span,
                value: text.clone(),
            },
            TokenKind::Nat { .. }
            | TokenKind::Scientific(_)
            | TokenKind::Str(_)
            | TokenKind::Char(_)
            | TokenKind::DocComment(_)
            | TokenKind::Unknown(_) => Syntax::Atom { span, value: raw() },
            TokenKind::Eof => Syntax::Missing,
        }
    }

    /// Returns the span of the node. A `Missing` node has no span.
    pub fn span(&self) -> Option<Span> {
        match self {
            Syntax::Missing => None,
            Syntax::Atom { span, .. } | Syntax::Ident { span, .. } | Syntax::Node { span, .. } => {
                Some(*span)
            }
        }
    }

    /// Returns the kind of the node, if the node is a [`Syntax::Node`].
    pub fn kind(&self) -> Option<&Name> {
        match self {
            Syntax::Node { kind, .. } => Some(kind),
            _ => None,
        }
    }

    /// Returns `true` if the node is a node of this kind.
    pub fn is_of_kind(&self, kind: &Name) -> bool {
        self.kind() == Some(kind)
    }

    /// Returns the children of the node. A leaf has no child.
    pub fn args(&self) -> &[Syntax] {
        match self {
            Syntax::Node { args, .. } => args,
            _ => &[],
        }
    }

    /// Returns the child at `index`.
    pub fn arg(&self, index: usize) -> Option<&Syntax> {
        self.args().get(index)
    }

    /// Returns `true` if the node or any child below it is `Missing`.
    ///
    /// The elaborator uses this test. It must not report a type error for a
    /// tree that the parser already failed to read.
    pub fn has_missing(&self) -> bool {
        match self {
            Syntax::Missing => true,
            Syntax::Node { args, .. } => args.iter().any(Syntax::has_missing),
            _ => false,
        }
    }

    /// Returns the name of the node, if the node is an identifier.
    pub fn as_ident(&self) -> Option<&Name> {
        match self {
            Syntax::Ident { name, .. } => Some(name),
            _ => None,
        }
    }

    /// Returns the text of the node, if the node is an atom.
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            Syntax::Atom { value, .. } => Some(value),
            _ => None,
        }
    }

    /// Renders the tree over several lines, in the style of the Lean output.
    pub fn dump(&self) -> String {
        let mut out = String::new();
        self.write_dump(&mut out, 0);
        out
    }

    fn write_dump(&self, out: &mut String, depth: usize) {
        let pad = "  ".repeat(depth);
        match self {
            Syntax::Missing => {
                let _ = writeln!(out, "{pad}<missing>");
            }
            Syntax::Atom { value, .. } => {
                let _ = writeln!(out, "{pad}{value:?}");
            }
            Syntax::Ident { name, .. } => {
                let _ = writeln!(out, "{pad}(ident {name})");
            }
            Syntax::Node { kind, args, .. } => {
                let _ = writeln!(out, "{pad}({kind}");
                for arg in args {
                    arg.write_dump(out, depth + 1);
                }
                let _ = writeln!(out, "{pad})");
            }
        }
    }
}

impl fmt::Display for Syntax {
    /// Prints the tree on one line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Syntax::Missing => f.write_str("<missing>"),
            Syntax::Atom { value, .. } => write!(f, "{value}"),
            Syntax::Ident { name, .. } => write!(f, "{name}"),
            Syntax::Node { kind, args, .. } => {
                write!(f, "({kind}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                f.write_str(")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Syntax, kind};
    use rean_core::{Name, Span};

    fn ident(start: u32, text: &str) -> Syntax {
        Syntax::Ident {
            span: Span::new(start, start + text.len() as u32),
            raw: text.into(),
            name: Name::from_dotted(text),
        }
    }

    #[test]
    fn a_node_span_covers_its_children() {
        let app = Syntax::node(kind::term_app(), vec![ident(0, "f"), ident(2, "x")]);
        assert_eq!(app.span(), Some(Span::new(0, 3)));
    }

    #[test]
    fn a_missing_child_does_not_break_the_span() {
        let app = Syntax::node(kind::term_app(), vec![ident(0, "f"), Syntax::Missing]);
        assert_eq!(app.span(), Some(Span::new(0, 1)));
        assert!(app.has_missing());
    }

    #[test]
    fn a_tree_with_no_error_reports_no_missing() {
        let app = Syntax::node(kind::term_app(), vec![ident(0, "f"), ident(2, "x")]);
        assert!(!app.has_missing());
    }

    #[test]
    fn one_line_display_shows_the_kind() {
        let app = Syntax::node("Term.app", vec![ident(0, "f"), ident(2, "x")]);
        assert_eq!(app.to_string(), "(Term.app f x)");
    }

    #[test]
    fn dump_indents_each_level() {
        let inner = Syntax::node("Term.app", vec![ident(0, "f"), ident(2, "x")]);
        let outer = Syntax::node("Term.paren", vec![inner]);
        assert_eq!(
            outer.dump(),
            "(Term.paren\n  (Term.app\n    (ident f)\n    (ident x)\n  )\n)\n"
        );
    }

    #[test]
    fn accessors_read_the_leaves() {
        let app = Syntax::node(kind::term_app(), vec![ident(0, "f"), ident(2, "x")]);
        assert!(app.is_of_kind(&kind::term_app()));
        assert_eq!(
            app.arg(0).and_then(Syntax::as_ident),
            Some(&Name::from_dotted("f"))
        );
        assert!(app.arg(2).is_none());
        assert!(app.as_atom().is_none());
    }
}
