//! The lexer turns source text into a flat list of tokens.
//!
//! One thing makes a Lean lexer different from a C lexer or a Rust lexer: the
//! set of keywords and symbols is not fixed. A `notation` command or a `syntax`
//! command adds a new token while the compiler reads the file. The lexer
//! therefore asks a [`TokenTable`] on every token, and the table can grow.
//!
//! ```
//! use rean_core::{DiagnosticBag, SourceMap};
//! use rean_lexer::{TokenKind, TokenTable, tokenize};
//!
//! let mut map = SourceMap::new();
//! let id = map.add("a.lean", "def two := 2");
//! let mut table = TokenTable::builtin();
//! let mut diags = DiagnosticBag::new();
//! let tokens = tokenize(map.file(id), &table, &mut diags);
//! assert!(matches!(tokens[0].kind, TokenKind::Keyword(_)));
//!
//! // A later `notation` command teaches the lexer a new symbol.
//! table.insert("⊹");
//! ```

mod chars;
mod lexer;
mod table;
mod token;

pub use chars::{is_id_first, is_id_rest};
pub use lexer::{Lexer, tokenize};
pub use table::TokenTable;
pub use token::{Token, TokenKind};
