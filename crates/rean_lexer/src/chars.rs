//! Which characters can start an identifier and which can continue one.
//!
//! Lean lets you write `α`, `Γ₀`, and `𝒞` as ordinary identifiers. The lexer
//! needs explicit Unicode ranges for that. The ranges below follow the
//! `isLetterLike` and `isSubScriptAlnum` functions of the Lean source.
//!
//! The ranges leave out `λ`, `Π`, and `Σ`, because Lean reserves those three
//! characters for notation.

/// Returns `true` if `c` can start an identifier.
pub fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

/// Returns `true` if `c` can continue an identifier.
///
/// The set is wider than [`is_id_first`]. It adds the digits, the prime, and
/// the subscripts, so that `x'`, `h₂`, and `f1` are single identifiers.
pub fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || c == '_'
        || c == '\''
        || c == '!'
        || c == '?'
        || c == '\u{271d}'
        || is_letter_like(c)
        || is_sub_script_alnum(c)
}

/// Returns `true` if `c` is a letter outside ASCII that Lean treats as a letter.
pub fn is_letter_like(c: char) -> bool {
    let v = c as u32;
    // Lower case Greek, but not lambda.
    (0x3b1..=0x3c9).contains(&v) && v != 0x3bb
        // Upper case Greek, but not Pi and not Sigma.
        || (0x391..=0x3a9).contains(&v) && v != 0x3a0 && v != 0x3a3
        // Greek with accents.
        || (0x3ca..=0x3fb).contains(&v)
        // Polytonic Greek.
        || (0x1f00..=0x1ffe).contains(&v)
        // Letter like symbols, such as `ℕ` and `ℝ`.
        || (0x2100..=0x214f).contains(&v)
        // Script, double struck, and Fraktur Latin letters, such as `𝒞`.
        || (0x1d49c..=0x1d59f).contains(&v)
        // Ligatures.
        || (0xfb00..=0xfb4f).contains(&v)
        // CJK.
        || (0x4e00..=0x9fff).contains(&v)
        // Hangul Jamo.
        || (0x1100..=0x11ff).contains(&v)
        || (0xd7cb..=0xd7fb).contains(&v)
}

/// Returns `true` if `c` is a subscript digit or a subscript letter.
pub fn is_sub_script_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
}

#[cfg(test)]
mod tests {
    use super::{is_id_first, is_id_rest};

    #[test]
    fn greek_letters_are_identifiers() {
        assert!(is_id_first('α'));
        assert!(is_id_first('Γ'));
    }

    #[test]
    fn lean_reserves_lambda_pi_and_sigma() {
        assert!(!is_id_first('λ'));
        assert!(!is_id_first('Π'));
        assert!(!is_id_first('Σ'));
    }

    #[test]
    fn subscripts_and_primes_only_continue_a_name() {
        assert!(is_id_rest('₂'));
        assert!(is_id_rest('\''));
        assert!(!is_id_first('₂'));
        assert!(!is_id_first('\''));
    }

    #[test]
    fn digits_only_continue_a_name() {
        assert!(is_id_rest('1'));
        assert!(!is_id_first('1'));
    }
}
