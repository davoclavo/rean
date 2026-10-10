//! Hierarchical names.
//!
//! Lean does not use a plain string for an identifier. It uses a linked list of
//! parts that grows at the front. The name `Nat.succ` is
//! `Str(Str(Anonymous, "Nat"), "succ")`.
//!
//! Two reasons explain this design:
//!
//! - A `namespace` command only adds a prefix. A list makes that cheap.
//! - The elaborator invents fresh names, such as `_uniq.17`. The `Num` case
//!   holds the number without a string allocation.
//!
//! [`std::sync::Arc`] makes a clone cheap, because the prefix is shared.

use std::fmt;
use std::sync::Arc;

/// A hierarchical name.
#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub enum Name {
    /// The empty name. It is the root of every other name.
    #[default]
    Anonymous,
    /// A string part, such as the `succ` of `Nat.succ`.
    Str { prefix: Arc<Name>, part: Arc<str> },
    /// A numeric part, such as the `17` of `_uniq.17`.
    Num { prefix: Arc<Name>, part: u64 },
}

impl Name {
    /// Returns the anonymous name.
    pub fn anonymous() -> Self {
        Name::Anonymous
    }

    /// Adds a string part to the end of `self`.
    pub fn str(&self, part: impl Into<Arc<str>>) -> Self {
        Name::Str {
            prefix: Arc::new(self.clone()),
            part: part.into(),
        }
    }

    /// Adds a numeric part to the end of `self`.
    pub fn num(&self, part: u64) -> Self {
        Name::Num {
            prefix: Arc::new(self.clone()),
            part,
        }
    }

    /// Builds a name from a dotted string. `"Nat.succ"` gives two parts.
    ///
    /// An empty string gives [`Name::Anonymous`].
    pub fn from_dotted(text: &str) -> Self {
        let mut name = Name::Anonymous;
        if text.is_empty() {
            return name;
        }
        for part in text.split('.') {
            name = name.str(part);
        }
        name
    }

    /// Returns `true` if `self` is the anonymous name.
    pub fn is_anonymous(&self) -> bool {
        matches!(self, Name::Anonymous)
    }

    /// Returns the prefix of `self`. The anonymous name has no prefix.
    pub fn prefix(&self) -> Option<&Name> {
        match self {
            Name::Anonymous => None,
            Name::Str { prefix, .. } | Name::Num { prefix, .. } => Some(prefix),
        }
    }

    /// Returns the number of parts in `self`.
    pub fn len(&self) -> usize {
        match self {
            Name::Anonymous => 0,
            Name::Str { prefix, .. } | Name::Num { prefix, .. } => 1 + prefix.len(),
        }
    }

    /// Returns `true` if `self` has no parts.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the last part of `self` as a string, if that part is a string.
    pub fn last_str(&self) -> Option<&str> {
        match self {
            Name::Str { part, .. } => Some(part),
            _ => None,
        }
    }

    /// Appends every part of `other` to `self`.
    pub fn append(&self, other: &Name) -> Name {
        match other {
            Name::Anonymous => self.clone(),
            Name::Str { prefix, part } => self.append(prefix).str(part.clone()),
            Name::Num { prefix, part } => self.append(prefix).num(*part),
        }
    }

    /// Returns `true` if `prefix` is a prefix of `self`.
    pub fn is_prefix_of(&self, other: &Name) -> bool {
        if self == other {
            return true;
        }
        match other.prefix() {
            Some(p) => self.is_prefix_of(p),
            None => false,
        }
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Anonymous => f.write_str("[anonymous]"),
            Name::Str { prefix, part } => write_part(f, prefix, part),
            Name::Num { prefix, part } => write_part(f, prefix, part),
        }
    }
}

fn write_part(f: &mut fmt::Formatter<'_>, prefix: &Name, part: &dyn fmt::Display) -> fmt::Result {
    if prefix.is_anonymous() {
        write!(f, "{part}")
    } else {
        write!(f, "{prefix}.{part}")
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{self}")
    }
}

impl From<&str> for Name {
    fn from(text: &str) -> Self {
        Name::from_dotted(text)
    }
}

#[cfg(test)]
mod tests {
    use super::Name;

    #[test]
    fn dotted_round_trip() {
        let name = Name::from_dotted("Nat.succ");
        assert_eq!(name.to_string(), "Nat.succ");
        assert_eq!(name.len(), 2);
        assert_eq!(name.last_str(), Some("succ"));
    }

    #[test]
    fn anonymous_has_no_prefix() {
        let name = Name::anonymous();
        assert!(name.is_anonymous());
        assert!(name.prefix().is_none());
        assert_eq!(name.to_string(), "[anonymous]");
    }

    #[test]
    fn numeric_part_prints_with_a_dot() {
        let name = Name::from_dotted("_uniq").num(17);
        assert_eq!(name.to_string(), "_uniq.17");
    }

    #[test]
    fn append_joins_two_names() {
        let joined = Name::from_dotted("List").append(&Name::from_dotted("map.go"));
        assert_eq!(joined.to_string(), "List.map.go");
    }

    #[test]
    fn prefix_test_walks_the_list() {
        let nat = Name::from_dotted("Nat");
        let succ = Name::from_dotted("Nat.succ");
        assert!(nat.is_prefix_of(&succ));
        assert!(!succ.is_prefix_of(&nat));
    }
}
