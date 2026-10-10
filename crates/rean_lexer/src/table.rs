//! The token table.
//!
//! In C the keyword list lives in the lexer. In Lean the list lives in the
//! environment, because a user command can extend it:
//!
//! ```lean
//! infixl:65 " ⊹ " => HAdd.hAdd
//! ```
//!
//! After that line, `⊹` is a token. Before that line, it is not. The lexer
//! therefore holds no keyword list of its own. It reads this table.
//!
//! The table answers one question: what is the longest token in the table that
//! is a prefix of this text? The longest match matters. Without it, `:=` would
//! lex as `:` and then `=`.

use std::collections::HashSet;
use std::sync::Arc;

/// The set of keywords and symbols that the lexer knows right now.
#[derive(Clone, Debug, Default)]
pub struct TokenTable {
    tokens: HashSet<Arc<str>>,
    /// The length in bytes of the longest token. It bounds the match loop.
    max_len: usize,
}

impl TokenTable {
    /// Builds an empty table.
    pub fn new() -> Self {
        TokenTable::default()
    }

    /// Adds a token to the table. A second insert of the same text does nothing.
    pub fn insert(&mut self, text: &str) {
        let text = text.trim();
        if text.is_empty() {
            return;
        }
        self.max_len = self.max_len.max(text.len());
        self.tokens.insert(Arc::from(text));
    }

    /// Adds every token of `texts` to the table.
    pub fn extend<'a>(&mut self, texts: impl IntoIterator<Item = &'a str>) {
        for text in texts {
            self.insert(text);
        }
    }

    /// Returns `true` if the table holds exactly this text.
    pub fn contains(&self, text: &str) -> bool {
        self.tokens.contains(text)
    }

    /// Returns the shared text of a token, if the table holds it.
    pub fn get(&self, text: &str) -> Option<Arc<str>> {
        self.tokens.get(text).cloned()
    }

    /// Returns the number of tokens in the table.
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    /// Returns `true` if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Returns the longest token in the table that starts `text`.
    ///
    /// The method tries the longest candidate first, so `":=x"` gives `":="`
    /// and not `":"`.
    pub fn longest_match(&self, text: &str) -> Option<Arc<str>> {
        let limit = self.max_len.min(text.len());
        // Walk the candidate ends from the longest to the shortest. A slice is
        // only valid at a character boundary.
        for end in (1..=limit).rev() {
            if !text.is_char_boundary(end) {
                continue;
            }
            if let Some(found) = self.tokens.get(&text[..end]) {
                return Some(found.clone());
            }
        }
        None
    }

    /// Builds a table with the tokens of the core language.
    ///
    /// Real Lean loads this set from the prelude. The list below is a start.
    pub fn builtin() -> Self {
        let mut table = TokenTable::new();
        table.extend(BUILTIN_KEYWORDS.iter().copied());
        table.extend(BUILTIN_SYMBOLS.iter().copied());
        table
    }
}

/// Words that look like identifiers but that the core language reserves.
pub const BUILTIN_KEYWORDS: &[&str] = &[
    // Commands.
    "import",
    "open",
    "namespace",
    "section",
    "end",
    "universe",
    "variable",
    "def",
    "abbrev",
    "theorem",
    "lemma",
    "example",
    "axiom",
    "inductive",
    "structure",
    "class",
    "instance",
    "mutual",
    "deriving",
    "attribute",
    "set_option",
    "macro",
    "macro_rules",
    "notation",
    "syntax",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    // Modifiers.
    "partial",
    "unsafe",
    "private",
    "protected",
    "noncomputable",
    // Terms.
    "fun",
    "let",
    "have",
    "show",
    "suffices",
    "from",
    "match",
    "with",
    "where",
    "do",
    "if",
    "then",
    "else",
    "by",
    "calc",
    "sorry",
    "this",
    "at",
    "in",
    "using",
    // Sorts.
    "Type",
    "Prop",
    "Sort",
];

/// Symbols that the core language reserves.
pub const BUILTIN_SYMBOLS: &[&str] = &[
    // Brackets.
    "(", ")", "{", "}", "[", "]", "⟨", "⟩", "⦃", "⦄", "⟦", "⟧", // Structure.
    ",", ":", ";", "|", "@", "_", "$", ".", "..", "...", ":=", "=>", "->", "→", "↦", "<-", "←",
    // Arithmetic and comparison.
    "+", "-", "*", "/", "%", "^", "=", "==", "!=", "≠", "<", ">", "<=", ">=", "≤", "≥",
    // Logic.
    "&&", "||", "!", "¬", "∧", "∨", "↔", "∀", "∃", "λ", "Π", "Σ", // Sets and types.
    "×", "⊕", "∘", "∈", "∉", "⊆", "∪", "∩", "∅", "⊢",
    // Commands that start with a hash.
    "#eval", "#check", "#print", "#reduce", "#exit", // Pipes.
    "++", "<|", "|>", "<;>", "<|>",
];

#[cfg(test)]
mod tests {
    use super::TokenTable;

    #[test]
    fn longest_match_wins() {
        let table = TokenTable::builtin();
        assert_eq!(table.longest_match(":=x").as_deref(), Some(":="));
        assert_eq!(table.longest_match(": x").as_deref(), Some(":"));
        assert_eq!(table.longest_match("...a").as_deref(), Some("..."));
        assert_eq!(table.longest_match("..a").as_deref(), Some(".."));
    }

    #[test]
    fn a_match_respects_character_boundaries() {
        let table = TokenTable::builtin();
        // `→` is three bytes long. A one byte slice of it is not valid.
        assert_eq!(table.longest_match("→ β").as_deref(), Some("→"));
    }

    #[test]
    fn no_match_returns_none() {
        let table = TokenTable::builtin();
        assert!(table.longest_match("abc").is_none());
        assert!(table.longest_match("").is_none());
    }

    #[test]
    fn the_table_grows() {
        let mut table = TokenTable::new();
        assert!(table.is_empty());
        table.insert(" ⊹ ");
        assert_eq!(table.len(), 1);
        assert!(table.contains("⊹"));
        assert_eq!(table.longest_match("⊹ y").as_deref(), Some("⊹"));
    }

    #[test]
    fn an_empty_insert_does_nothing() {
        let mut table = TokenTable::new();
        table.insert("   ");
        assert!(table.is_empty());
    }
}
