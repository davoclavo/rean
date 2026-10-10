//! Source text, byte positions, and spans.
//!
//! The compiler stores a position as one `u32` byte offset, not as a line and a
//! column pair. A [`Span`] is therefore 8 bytes, and it fits in every syntax
//! node without cost.
//!
//! The compiler computes the line and the column only when it prints a
//! message. [`SourceFile`] keeps a table of line start offsets for that job.

use std::fmt;
use std::ops::Range;
use std::sync::Arc;

/// An index into the [`SourceMap`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FileId(pub u32);

/// A byte range in one file.
///
/// The compiler does not store the [`FileId`] in the span. One command reads
/// one file, so the file is clear from the context.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// The byte offset of the first byte.
    pub start: u32,
    /// The byte offset after the last byte.
    pub end: u32,
}

impl Span {
    /// Builds a span from two byte offsets.
    pub fn new(start: u32, end: u32) -> Self {
        debug_assert!(start <= end, "a span must not run backwards");
        Span { start, end }
    }

    /// Builds an empty span at one offset.
    pub fn empty(at: u32) -> Self {
        Span { start: at, end: at }
    }

    /// Returns the length of the span in bytes.
    pub fn len(&self) -> u32 {
        self.end - self.start
    }

    /// Returns `true` if the span covers no bytes.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Returns the smallest span that covers both `self` and `other`.
    pub fn to(&self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Returns the span as a range, for a slice of the source text.
    pub fn range(&self) -> Range<usize> {
        self.start as usize..self.end as usize
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// A line number and a column number, both counted from 1.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

impl fmt::Display for LineCol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

/// One file of source text and its table of line starts.
pub struct SourceFile {
    id: FileId,
    path: String,
    text: Arc<str>,
    /// The byte offset of the first byte of each line.
    line_starts: Vec<u32>,
}

impl SourceFile {
    fn new(id: FileId, path: String, text: Arc<str>) -> Self {
        let mut line_starts = vec![0];
        line_starts.extend(
            text.bytes()
                .enumerate()
                .filter(|(_, b)| *b == b'\n')
                .map(|(i, _)| i as u32 + 1),
        );
        SourceFile {
            id,
            path,
            text,
            line_starts,
        }
    }

    /// Returns the identifier of the file.
    pub fn id(&self) -> FileId {
        self.id
    }

    /// Returns the path that the compiler reports in a message.
    pub fn path(&self) -> &str {
        &self.path
    }

    /// Returns the whole text of the file.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Returns the text that the span covers.
    pub fn slice(&self, span: Span) -> &str {
        &self.text[span.range()]
    }

    /// Returns the number of lines in the file.
    pub fn line_count(&self) -> u32 {
        self.line_starts.len() as u32
    }

    /// Converts a byte offset into a line and a column.
    ///
    /// The column counts characters, not bytes. A multi-byte character
    /// therefore adds 1 to the column.
    pub fn line_col(&self, offset: u32) -> LineCol {
        let offset = offset.min(self.text.len() as u32);
        // `partition_point` finds the first line that starts after `offset`.
        let line_index = self.line_starts.partition_point(|start| *start <= offset) - 1;
        let line_start = self.line_starts[line_index] as usize;
        let col = self.text[line_start..offset as usize].chars().count() as u32 + 1;
        LineCol {
            line: line_index as u32 + 1,
            col,
        }
    }

    /// Returns the text of one line, with no line break. Lines count from 1.
    pub fn line_text(&self, line: u32) -> Option<&str> {
        let index = line.checked_sub(1)? as usize;
        let start = *self.line_starts.get(index)? as usize;
        let end = match self.line_starts.get(index + 1) {
            Some(next) => *next as usize,
            None => self.text.len(),
        };
        Some(self.text[start..end].trim_end_matches(['\n', '\r']))
    }
}

/// Every file that the compiler read in this run.
#[derive(Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    /// Builds an empty map.
    pub fn new() -> Self {
        SourceMap::default()
    }

    /// Adds a file to the map and returns its identifier.
    pub fn add(&mut self, path: impl Into<String>, text: impl Into<Arc<str>>) -> FileId {
        let id = FileId(self.files.len() as u32);
        self.files
            .push(SourceFile::new(id, path.into(), text.into()));
        id
    }

    /// Returns the file with this identifier.
    ///
    /// # Panics
    ///
    /// This method panics if the map does not hold the identifier.
    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }

    /// Returns every file in the map.
    pub fn files(&self) -> &[SourceFile] {
        &self.files
    }
}

#[cfg(test)]
mod tests {
    use super::{SourceMap, Span};

    #[test]
    fn span_joins_cover_both_ends() {
        let joined = Span::new(3, 5).to(Span::new(10, 12));
        assert_eq!(joined, Span::new(3, 12));
    }

    #[test]
    fn line_col_counts_from_one() {
        let mut map = SourceMap::new();
        let id = map.add("a.lean", "def f :=\n  1\n");
        let file = map.file(id);
        assert_eq!(file.line_col(0).to_string(), "1:1");
        assert_eq!(file.line_col(4).to_string(), "1:5");
        assert_eq!(file.line_col(9).to_string(), "2:1");
        assert_eq!(file.line_col(11).to_string(), "2:3");
    }

    #[test]
    fn column_counts_characters() {
        let mut map = SourceMap::new();
        // The arrow is three bytes long, but it is one character.
        let id = map.add("a.lean", "α → β");
        let file = map.file(id);
        let offset = "α → ".len() as u32;
        assert_eq!(file.line_col(offset).to_string(), "1:5");
    }

    #[test]
    fn line_text_drops_the_line_break() {
        let mut map = SourceMap::new();
        let id = map.add("a.lean", "one\r\ntwo\n");
        let file = map.file(id);
        assert_eq!(file.line_text(1), Some("one"));
        assert_eq!(file.line_text(2), Some("two"));
        assert_eq!(file.line_text(4), None);
    }

    #[test]
    fn slice_returns_the_covered_text() {
        let mut map = SourceMap::new();
        let id = map.add("a.lean", "def f := 1");
        assert_eq!(map.file(id).slice(Span::new(4, 5)), "f");
    }
}
