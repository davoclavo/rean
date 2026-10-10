//! The scanner.

use crate::chars::{is_id_first, is_id_rest};
use crate::table::TokenTable;
use crate::token::{Token, TokenKind};
use rean_core::{Diagnostic, DiagnosticBag, Name, SourceFile, Span};
use std::sync::Arc;

/// Reads one file and returns every token, including the final `Eof`.
pub fn tokenize(file: &SourceFile, table: &TokenTable, diags: &mut DiagnosticBag) -> Vec<Token> {
    let mut lexer = Lexer::new(file.text(), table, diags);
    let mut tokens = Vec::new();
    loop {
        let token = lexer.next_token();
        let eof = token.is_eof();
        tokens.push(token);
        if eof {
            return tokens;
        }
    }
}

/// A scanner over one string of source text.
pub struct Lexer<'a> {
    text: &'a str,
    pos: u32,
    table: &'a TokenTable,
    diags: &'a mut DiagnosticBag,
}

impl<'a> Lexer<'a> {
    /// Builds a lexer at the start of `text`.
    pub fn new(text: &'a str, table: &'a TokenTable, diags: &'a mut DiagnosticBag) -> Self {
        Lexer {
            text,
            pos: 0,
            table,
            diags,
        }
    }

    /// Returns the next token and moves past it.
    pub fn next_token(&mut self) -> Token {
        // A doc comment is a token, so the skip loop can stop on one.
        if let Some(token) = self.skip_trivia() {
            return token;
        }
        let start = self.pos;
        let Some(c) = self.peek() else {
            return Token::new(TokenKind::Eof, Span::empty(start));
        };

        if is_id_first(c) || c == '«' {
            return self.ident(start);
        }
        if c.is_ascii_digit() {
            return self.number(start);
        }
        if c == '"' {
            return self.string(start);
        }
        if c == '\'' {
            return self.char_literal(start);
        }
        if let Some(text) = self.table.longest_match(&self.text[start as usize..]) {
            self.pos += text.len() as u32;
            return Token::new(TokenKind::Symbol(text), self.span_from(start));
        }

        self.bump();
        let span = self.span_from(start);
        self.diags.push(Diagnostic::error(
            span,
            format!("unexpected character {c:?}"),
        ));
        Token::new(TokenKind::Unknown(c), span)
    }

    // --- trivia ---------------------------------------------------------

    /// Moves past whitespace and comments.
    ///
    /// Returns a token if the scanner met a doc comment, because Lean keeps a
    /// doc comment as part of the program.
    fn skip_trivia(&mut self) -> Option<Token> {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => {
                    self.bump();
                }
                Some('-') if self.starts_with("--") => {
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                // `/--` opens a doc comment, but `/--/` is an empty block comment.
                Some('/') if self.starts_with("/--") && !self.starts_with("/--/") => {
                    return Some(self.doc_comment());
                }
                Some('/') if self.starts_with("/-") => {
                    self.block_comment();
                }
                _ => return None,
            }
        }
    }

    /// Reads a `/- ... -/` comment. The comment can hold another comment.
    fn block_comment(&mut self) {
        let start = self.pos;
        self.pos += 2;
        let mut depth = 1usize;
        while depth > 0 {
            if self.starts_with("/-") {
                self.pos += 2;
                depth += 1;
            } else if self.starts_with("-/") {
                self.pos += 2;
                depth -= 1;
            } else if self.bump().is_none() {
                self.diags.push(
                    Diagnostic::error(self.span_from(start), "unterminated block comment")
                        .with_note("add `-/` to close the comment"),
                );
                return;
            }
        }
    }

    /// Reads a `/-- ... -/` comment and returns it as a token.
    fn doc_comment(&mut self) -> Token {
        let start = self.pos;
        self.pos += 3;
        let body_start = self.pos as usize;
        let mut depth = 1usize;
        loop {
            if self.starts_with("/-") {
                self.pos += 2;
                depth += 1;
            } else if self.starts_with("-/") {
                let body_end = self.pos as usize;
                self.pos += 2;
                depth -= 1;
                if depth == 0 {
                    let body = &self.text[body_start..body_end];
                    return Token::new(
                        TokenKind::DocComment(Arc::from(body)),
                        self.span_from(start),
                    );
                }
            } else if self.bump().is_none() {
                let span = self.span_from(start);
                self.diags.push(
                    Diagnostic::error(span, "unterminated doc comment")
                        .with_note("add `-/` to close the comment"),
                );
                let body = &self.text[body_start..];
                return Token::new(TokenKind::DocComment(Arc::from(body)), span);
            }
        }
    }

    // --- identifiers ----------------------------------------------------

    /// Reads a name. A name can hold a dot, so `Nat.succ` is one token.
    fn ident(&mut self, start: u32) -> Token {
        let mut name = Name::anonymous();
        while let Some(part) = self.ident_part() {
            name = name.str(part);
            // Only continue the name if a part follows the dot. `x.1` keeps
            // the `.` as a separate token, and the parser reads a projection.
            if self.peek() == Some('.') && self.next_part_follows_dot() {
                self.bump();
            } else {
                break;
            }
        }

        let span = self.span_from(start);
        let raw = &self.text[span.range()];
        // A single plain part can be a reserved word, such as `def`.
        if name.len() == 1
            && let Some(text) = self.table.get(raw)
        {
            return Token::new(TokenKind::Keyword(text), span);
        }
        Token::new(
            TokenKind::Ident {
                name,
                raw: Arc::from(raw),
            },
            span,
        )
    }

    /// Reads one part of a name, either plain or inside french quotes.
    fn ident_part(&mut self) -> Option<Arc<str>> {
        if self.peek() == Some('«') {
            let open = self.pos;
            self.bump();
            let body_start = self.pos as usize;
            while let Some(c) = self.peek() {
                if c == '»' {
                    let body = Arc::from(&self.text[body_start..self.pos as usize]);
                    self.bump();
                    return Some(body);
                }
                self.bump();
            }
            self.diags.push(
                Diagnostic::error(self.span_from(open), "unterminated escaped identifier")
                    .with_note("add `»` to close the identifier"),
            );
            return Some(Arc::from(&self.text[body_start..]));
        }

        let part_start = self.pos as usize;
        if !self.peek().is_some_and(is_id_first) {
            return None;
        }
        self.bump();
        while self.peek().is_some_and(is_id_rest) {
            self.bump();
        }
        Some(Arc::from(&self.text[part_start..self.pos as usize]))
    }

    /// Returns `true` if a name part follows the dot at the scanner position.
    fn next_part_follows_dot(&self) -> bool {
        let rest = &self.text[self.pos as usize + 1..];
        rest.chars()
            .next()
            .is_some_and(|c| is_id_first(c) || c == '«')
    }

    // --- numbers --------------------------------------------------------

    /// Reads a whole number or a number with a point or an exponent.
    fn number(&mut self, start: u32) -> Token {
        if self.peek() == Some('0')
            && let Some(radix) = self.peek_at(1).and_then(radix_of)
        {
            return self.radix_number(start, radix);
        }

        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.bump();
        }

        let mut scientific = false;
        // A point only belongs to the number if a digit follows it. `1..2` and
        // `x.1` must keep the dot as its own token.
        if self.peek() == Some('.') && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
            scientific = true;
            self.bump();
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.bump();
            }
        }
        if matches!(self.peek(), Some('e' | 'E')) {
            let save = self.pos;
            self.bump();
            if matches!(self.peek(), Some('+' | '-')) {
                self.bump();
            }
            if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                scientific = true;
                while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.bump();
                }
            } else {
                // No digit after `e`, so the `e` starts an identifier instead.
                self.pos = save;
            }
        }

        let span = self.span_from(start);
        let raw = &self.text[span.range()];
        let kind = if scientific {
            TokenKind::Scientific(Arc::from(raw))
        } else {
            TokenKind::Nat {
                radix: 10,
                digits: Arc::from(raw),
            }
        };
        Token::new(kind, span)
    }

    /// Reads a number with a `0x`, `0b`, or `0o` prefix.
    fn radix_number(&mut self, start: u32, radix: u32) -> Token {
        self.pos += 2;
        let digits_start = self.pos as usize;
        while self.peek().is_some_and(|c| c.is_digit(radix) || c == '_') {
            self.bump();
        }
        let digits: String = self.text[digits_start..self.pos as usize]
            .chars()
            .filter(|c| *c != '_')
            .collect();
        let span = self.span_from(start);
        if digits.is_empty() {
            self.diags.push(Diagnostic::error(
                span,
                format!("a base {radix} number needs at least one digit"),
            ));
        }
        Token::new(
            TokenKind::Nat {
                radix,
                digits: Arc::from(digits.as_str()),
            },
            span,
        )
    }

    // --- strings and characters -----------------------------------------

    /// Reads a `"..."` literal and decodes the escapes.
    fn string(&mut self, start: u32) -> Token {
        self.bump();
        let mut value = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    let span = self.span_from(start);
                    self.diags.push(
                        Diagnostic::error(span, "unterminated string literal")
                            .with_note("add `\"` to close the string"),
                    );
                    return Token::new(TokenKind::Str(Arc::from(value.as_str())), span);
                }
                Some('"') => {
                    self.bump();
                    let span = self.span_from(start);
                    return Token::new(TokenKind::Str(Arc::from(value.as_str())), span);
                }
                Some('\\') => {
                    if let Some(c) = self.escape() {
                        value.push(c);
                    }
                }
                Some(c) => {
                    self.bump();
                    value.push(c);
                }
            }
        }
    }

    /// Reads a `'c'` literal.
    fn char_literal(&mut self, start: u32) -> Token {
        self.bump();
        let value = match self.peek() {
            Some('\\') => self.escape(),
            Some(c) => {
                self.bump();
                Some(c)
            }
            None => None,
        };
        if self.peek() == Some('\'') {
            self.bump();
        } else {
            self.diags.push(
                Diagnostic::error(self.span_from(start), "unterminated character literal")
                    .with_note("a character literal holds exactly one character"),
            );
        }
        Token::new(
            TokenKind::Char(value.unwrap_or('\u{fffd}')),
            self.span_from(start),
        )
    }

    /// Reads one escape and returns the character that it means.
    fn escape(&mut self) -> Option<char> {
        let start = self.pos;
        self.bump();
        let c = self.bump()?;
        match c {
            'n' => Some('\n'),
            't' => Some('\t'),
            'r' => Some('\r'),
            '\\' => Some('\\'),
            '"' => Some('"'),
            '\'' => Some('\''),
            'x' => self.hex_escape(start, 2),
            'u' => self.hex_escape(start, 4),
            other => {
                self.diags.push(Diagnostic::error(
                    self.span_from(start),
                    format!("unknown escape `\\{other}`"),
                ));
                None
            }
        }
    }

    /// Reads `count` hex digits and returns the character with that value.
    fn hex_escape(&mut self, start: u32, count: usize) -> Option<char> {
        let digits_start = self.pos as usize;
        for _ in 0..count {
            if !self.peek().is_some_and(|c| c.is_ascii_hexdigit()) {
                break;
            }
            self.bump();
        }
        let digits = &self.text[digits_start..self.pos as usize];
        let span = self.span_from(start);
        if digits.len() != count {
            self.diags.push(Diagnostic::error(
                span,
                format!("this escape needs {count} hex digits"),
            ));
            return None;
        }
        let value = u32::from_str_radix(digits, 16).ok()?;
        match char::from_u32(value) {
            Some(c) => Some(c),
            None => {
                self.diags.push(Diagnostic::error(
                    span,
                    format!("{value:#x} is not a character"),
                ));
                None
            }
        }
    }

    // --- cursor ---------------------------------------------------------

    fn rest(&self) -> &'a str {
        &self.text[self.pos as usize..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn peek_at(&self, index: usize) -> Option<char> {
        self.rest().chars().nth(index)
    }

    fn starts_with(&self, prefix: &str) -> bool {
        self.rest().starts_with(prefix)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8() as u32;
        Some(c)
    }

    fn span_from(&self, start: u32) -> Span {
        Span::new(start, self.pos)
    }
}

fn radix_of(c: char) -> Option<u32> {
    match c {
        'x' | 'X' => Some(16),
        'b' | 'B' => Some(2),
        'o' | 'O' => Some(8),
        _ => None,
    }
}
