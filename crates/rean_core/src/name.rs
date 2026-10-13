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
///
/// # The two numbers each part carries
///
/// `hash` and `parts` are computed once, where the part is added, and they are
/// the reason this type is cheap to use as a key.
///
/// The kernel asks for both on paths that run on **every reduction step**.
/// `Environment::lookup` hashes a name to find a declaration, and
/// `nat_lit::is_binop` asks `two_parts`, which asked `len`, which walked the
/// whole chain. The hash of a term's `Const` node mixes the name's hash in, so
/// building any constant asked for it too.
///
/// `Eq` and `Hash` are written by hand rather than derived, so that both can
/// use the number. See the two `impl` blocks below.
#[derive(Clone, Default)]
pub enum Name {
    /// The empty name. It is the root of every other name.
    #[default]
    Anonymous,
    /// A string part, such as the `succ` of `Nat.succ`.
    Str {
        prefix: Arc<Name>,
        part: Arc<str>,
        hash: u64,
        parts: u32,
    },
    /// A numeric part, such as the `17` of `_uniq.17`.
    Num {
        prefix: Arc<Name>,
        part: u64,
        hash: u64,
        parts: u32,
    },
}

/// The seed and the multiplier of FNV-1a, which `rean_kernel` also uses.
const SEED: u64 = 0xcbf2_9ce4_8422_2325;
const PRIME: u64 = 0x0000_0100_0000_01b3;

/// Mixes one value into a hash.
fn mix(state: u64, value: u64) -> u64 {
    (state ^ value).wrapping_mul(PRIME)
}

impl Name {
    /// Returns the anonymous name.
    pub fn anonymous() -> Self {
        Name::Anonymous
    }

    /// Returns the hash of the whole name, computed when it was built.
    ///
    /// Two equal names have equal hashes, which is what lets [`Hash`] write
    /// this one number and lets [`PartialEq`] refuse a pair in O(1).
    pub fn hash_value(&self) -> u64 {
        match self {
            Name::Anonymous => SEED,
            Name::Str { hash, .. } | Name::Num { hash, .. } => *hash,
        }
    }

    /// Adds a string part to the end of `self`.
    pub fn str(&self, part: impl Into<Arc<str>>) -> Self {
        let part: Arc<str> = part.into();
        let mut hash = mix(self.hash_value(), part.len() as u64);
        for byte in part.as_bytes() {
            hash = mix(hash, u64::from(*byte));
        }
        Name::Str {
            parts: self.len() as u32 + 1,
            hash,
            prefix: Arc::new(self.clone()),
            part,
        }
    }

    /// Adds a numeric part to the end of `self`.
    pub fn num(&self, part: u64) -> Self {
        Name::Num {
            parts: self.len() as u32 + 1,
            // The marker keeps `Foo.1` apart from `Foo.«1»`, which are two
            // different names that `from_dotted` can no longer confuse.
            hash: mix(mix(self.hash_value(), 1), part),
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
            // A part that is all digits is a **numeric** part, because that is
            // what [`fmt::Display`] wrote. Lean's own private names carry one:
            // `_private.Init.Data.SInt.Lemmas.0.ISize.le_toInt` holds `Num(0)`
            // in the middle, and reading it back as the string "0" gives a
            // different name that no environment holds.
            //
            // That cost two real faults before `rean show` made it visible.
            // The trust report looks a declaration up by this route, so for
            // every private declaration of the prelude it found nothing and
            // reported no axioms; and `rean show` could not find one at all.
            //
            // A string part that is all digits cannot be written in a dotted
            // name, in Lean or here. Lean spells that one `«0»`.
            name = match part.parse::<u64>() {
                Ok(number) => name.num(number),
                Err(_) => name.str(part),
            };
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
            Name::Str { parts, .. } | Name::Num { parts, .. } => *parts as usize,
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

    /// Returns the two parts of a two part name, and allocates nothing.
    ///
    /// `Nat.add` gives `Some(("Nat", "add"))`. Any other shape gives `None`.
    ///
    /// The kernel asks "is this name `Nat.add`" on nearly every reduction step,
    /// and the readable way to ask was `name.to_string() == "Nat.add"`. That
    /// built a `String` every time, and `Name` then showed up in a profile of
    /// the Lean prelude. This method answers the same question by comparing two
    /// string slices that already exist.
    pub fn two_parts(&self) -> Option<(&str, &str)> {
        let last = self.last_str()?;
        let prefix = self.prefix()?;
        if prefix.len() != 1 {
            return None;
        }
        Some((prefix.last_str()?, last))
    }

    /// Appends every part of `other` to `self`.
    pub fn append(&self, other: &Name) -> Name {
        match other {
            Name::Anonymous => self.clone(),
            Name::Str { prefix, part, .. } => self.append(prefix).str(part.clone()),
            Name::Num { prefix, part, .. } => self.append(prefix).num(*part),
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

impl PartialEq for Name {
    /// Two names are equal when they hold the same parts.
    ///
    /// Three tests, cheapest first.
    ///
    /// 1. **The hashes.** Two different hashes cannot be the same name, so one
    ///    comparison of two numbers refuses most pairs. A hash may not confirm
    ///    an answer, which is why the rest of the function exists.
    /// 2. **The pointers.** A name grows at the front and the parts are
    ///    shared, so two names that end the same way very often hold the
    ///    **same** prefix object. The export reader builds every name of a
    ///    module that way.
    /// 3. The parts themselves.
    fn eq(&self, other: &Name) -> bool {
        if self.hash_value() != other.hash_value() {
            return false;
        }
        match (self, other) {
            (Name::Anonymous, Name::Anonymous) => true,
            (
                Name::Str {
                    prefix: p1,
                    part: s1,
                    ..
                },
                Name::Str {
                    prefix: p2,
                    part: s2,
                    ..
                },
            ) => (Arc::ptr_eq(s1, s2) || s1 == s2) && (Arc::ptr_eq(p1, p2) || p1 == p2),
            (
                Name::Num {
                    prefix: p1,
                    part: n1,
                    ..
                },
                Name::Num {
                    prefix: p2,
                    part: n2,
                    ..
                },
            ) => n1 == n2 && (Arc::ptr_eq(p1, p2) || p1 == p2),
            _ => false,
        }
    }
}

impl Eq for Name {}

impl std::hash::Hash for Name {
    /// Writes the one number that the name carries.
    ///
    /// The derived version walked the chain and fed every byte of every part to
    /// the hasher, on every lookup. Equal names have equal hashes, which is the
    /// only thing `Hash` has to promise beside `Eq`.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash_value());
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Anonymous => f.write_str("[anonymous]"),
            Name::Str { prefix, part, .. } => write_part(f, prefix, part),
            Name::Num { prefix, part, .. } => write_part(f, prefix, part),
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
