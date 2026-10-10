//! The token type.

use rean_core::{Name, Span};
use std::fmt;
use std::sync::Arc;

/// What a token is.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TokenKind {
    /// A name, such as `x` or `Nat.succ`.
    Ident { name: Name, raw: Arc<str> },
    /// A word from the token table, such as `def` or `fun`.
    Keyword(Arc<str>),
    /// A symbol from the token table, such as `:=` or `→`.
    Symbol(Arc<str>),
    /// A whole number. The lexer keeps the digits, not a machine integer,
    /// because a Lean `Nat` has no upper bound.
    Nat { radix: u32, digits: Arc<str> },
    /// A number with a point or an exponent, such as `1.5` or `2e-3`.
    Scientific(Arc<str>),
    /// A string, after the lexer decodes the escapes.
    Str(Arc<str>),
    /// One character, after the lexer decodes the escape.
    Char(char),
    /// A `/-- ... -/` comment. Lean keeps it, because it is documentation.
    DocComment(Arc<str>),
    /// A character that fits no rule. The lexer also reports a diagnostic.
    Unknown(char),
    /// The end of the file. The list of tokens always ends with this token.
    Eof,
}

impl TokenKind {
    /// Returns the text of the token, if the token has fixed text.
    pub fn atom_text(&self) -> Option<&str> {
        match self {
            TokenKind::Keyword(text) | TokenKind::Symbol(text) => Some(text),
            _ => None,
        }
    }

    /// Returns `true` if the token is the keyword or the symbol `text`.
    pub fn is_atom(&self, text: &str) -> bool {
        self.atom_text() == Some(text)
    }

    /// Returns the short name of the kind, for a dump or a message.
    pub fn label(&self) -> &'static str {
        match self {
            TokenKind::Ident { .. } => "ident",
            TokenKind::Keyword(_) => "keyword",
            TokenKind::Symbol(_) => "symbol",
            TokenKind::Nat { .. } => "nat",
            TokenKind::Scientific(_) => "scientific",
            TokenKind::Str(_) => "str",
            TokenKind::Char(_) => "char",
            TokenKind::DocComment(_) => "doc",
            TokenKind::Unknown(_) => "unknown",
            TokenKind::Eof => "eof",
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Ident { name, .. } => write!(f, "{name}"),
            TokenKind::Keyword(text) | TokenKind::Symbol(text) => write!(f, "{text}"),
            TokenKind::Nat { radix, digits } if *radix == 10 => write!(f, "{digits}"),
            TokenKind::Nat { radix, digits } => write!(f, "{digits} (base {radix})"),
            TokenKind::Scientific(raw) => write!(f, "{raw}"),
            TokenKind::Str(value) => write!(f, "{value:?}"),
            TokenKind::Char(c) => write!(f, "{c:?}"),
            TokenKind::DocComment(text) => write!(f, "{:?}", text.trim()),
            TokenKind::Unknown(c) => write!(f, "{c:?}"),
            TokenKind::Eof => f.write_str("<eof>"),
        }
    }
}

/// One token and the source range that it covers.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    /// Builds a token.
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Token { kind, span }
    }

    /// Returns `true` if the token is the end of the file.
    pub fn is_eof(&self) -> bool {
        matches!(self.kind, TokenKind::Eof)
    }
}
