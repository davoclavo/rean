//! Natural number literals.
//!
//! `Expr::Lit(Literal::Nat(..))` exists for speed. In the theory, `3` is
//! `Nat.succ (Nat.succ (Nat.succ Nat.zero))`. In practice nobody wants a
//! million nested constructors, so the kernel stores the digits.
//!
//! That choice buys speed and costs two obligations, and a kernel that skips
//! either one is wrong:
//!
//! 1. A literal must behave like a constructor application wherever the rules
//!    expect one. [`to_ctor`] does that conversion.
//! 2. A literal must be definitionally equal to the matching constructor
//!    chain, so that `1` and `Nat.succ Nat.zero` are the same term.
//!
//! The kernel also computes on literals directly. Without that, `2 + 3` would
//! unfold through `Nat.rec` three times, and a real program would exhaust the
//! reduction budget on the first large number.
//!
//! # The limit
//!
//! A Lean `Nat` has no upper bound. This module uses `u128`, so it refuses to
//! compute past that. The real Lean kernel links a big number library. A term
//! that is too large stays stuck rather than give a wrong answer.

use crate::expr::{Expr, Literal};
use crate::level::Level;
use rean_core::Name;

/// Returns the value of `e`, if `e` is a natural number literal that fits.
pub fn value(e: &Expr) -> Option<u128> {
    match e {
        Expr::Lit(Literal::Nat(digits)) => digits.parse().ok(),
        _ => None,
    }
}

/// Builds a literal.
pub fn lit(n: u128) -> Expr {
    Expr::nat(n.to_string().as_str())
}

/// Turns a literal into a constructor application, one level deep.
///
/// `0` becomes `Nat.zero`, and `n+1` becomes `Nat.succ <n>`. The ι rule needs
/// this, because its major premise must be a constructor application.
pub fn to_ctor(n: u128) -> Expr {
    if n == 0 {
        Expr::const_("Nat.zero", vec![])
    } else {
        Expr::const_("Nat.succ", vec![]).app(lit(n - 1))
    }
}

/// Returns the constructor form of `e`, if `e` is a natural number literal.
pub fn to_ctor_if_lit(e: &Expr) -> Option<Expr> {
    value(e).map(to_ctor)
}

/// Returns the bytes of a string literal, as the term Lean means by them.
///
/// A `String` is a structure with two fields:
///
/// ```text
/// String.ofByteArray (toByteArray : ByteArray) (isValidUTF8 : ...) : String
/// ```
///
/// The kernel stores `"ab"` as a literal and never writes that pair out, so a
/// projection of a literal has to produce the field itself:
///
/// ```text
/// "ab".toByteArray  ~>  ByteArray.mk (Array.mk [UInt8.ofNat 97, UInt8.ofNat 98])
/// ```
///
/// The numbers are **UTF-8 bytes** and not code points. A Rust `str` is UTF-8
/// already, so its bytes are exactly the ones Lean means.
///
/// The second field is a proof, so no rule has to produce it. Proof irrelevance
/// makes any two proofs of it equal.
pub fn str_bytes(text: &str) -> Expr {
    let byte_type = Expr::const_("UInt8", vec![]);
    let mut list = Expr::const_("List.nil", vec![Level::Zero]).app(byte_type.clone());
    for byte in text.bytes().rev() {
        list = Expr::const_("List.cons", vec![Level::Zero])
            .app(byte_type.clone())
            .app(Expr::const_("UInt8.ofNat", vec![]).app(lit(byte as u128)))
            .app(list);
    }
    let array = Expr::const_("Array.mk", vec![Level::Zero])
        .app(byte_type)
        .app(list);
    Expr::const_("ByteArray.mk", vec![]).app(array)
}

/// Splits a constructor application of `Nat` into its shape.
pub enum NatShape<'e> {
    /// `Nat.zero`
    Zero,
    /// `Nat.succ x`
    Succ(&'e Expr),
}

/// Reads `Nat.zero` or `Nat.succ x` out of `e`.
pub fn shape<'e>(e: &'e Expr) -> Option<NatShape<'e>> {
    let (head, args) = e.unfold_apps();
    let Expr::Const { name, .. } = head else {
        return None;
    };
    match (name.two_parts()?, args.as_slice()) {
        (("Nat", "zero"), []) => Some(NatShape::Zero),
        (("Nat", "succ"), [inner]) => Some(NatShape::Succ(inner)),
        _ => None,
    }
}

/// A function on natural numbers that the kernel computes directly.
///
/// Each entry takes two literals and gives a term. The `Bool` results need
/// `Bool.true` and `Bool.false` in the environment, so the caller checks that.
pub fn binop(name: &Name, a: u128, b: u128) -> Option<Expr> {
    let number = |n: u128| Some(lit(n));
    let boolean = |yes: bool| {
        Some(Expr::const_(
            if yes { "Bool.true" } else { "Bool.false" },
            vec![],
        ))
    };
    let ("Nat", op) = name.two_parts()? else {
        return None;
    };
    match op {
        "add" => number(a.checked_add(b)?),
        "sub" => number(a.saturating_sub(b)),
        "mul" => number(a.checked_mul(b)?),
        // Lean defines division and modulo by zero to give zero.
        "div" => number(a.checked_div(b).unwrap_or(0)),
        "mod" => number(a.checked_rem(b).unwrap_or(a)),
        "pow" => number(a.checked_pow(u32::try_from(b).ok()?)?),
        "gcd" => number(gcd(a, b)),
        "land" => number(a & b),
        "lor" => number(a | b),
        "xor" => number(a ^ b),
        "shiftLeft" => number(a.checked_shl(u32::try_from(b).ok()?)?),
        "shiftRight" => number(a.checked_shr(u32::try_from(b).ok()?)?),
        "beq" => boolean(a == b),
        "ble" => boolean(a <= b),
        _ => None,
    }
}

/// Returns `true` if `name` is a function that [`binop`] computes.
pub fn is_binop(name: &Name) -> bool {
    binop(name, 0, 0).is_some()
}

/// Returns `true` if the result of [`binop`] is a `Bool` and not a `Nat`.
pub fn returns_bool(name: &Name) -> bool {
    matches!(name.two_parts(), Some(("Nat", "beq" | "ble")))
}

/// Returns the value of `e`, if `e` is a string literal.
pub fn str_value(e: &Expr) -> Option<&str> {
    match e {
        Expr::Lit(Literal::Str(text)) => Some(text),
        _ => None,
    }
}

/// A function on string literals that the kernel computes directly.
///
/// The general rule would be the one `Nat` gets: a literal behaves like the
/// constructor form, here `String.mk` of a list of characters. Building that
/// list needs `Char`, which needs `UInt32`, which is another layer again. So
/// these three are computed directly instead, and the limit is named rather
/// than hidden.
pub fn string_op(name: &Name, text: &str) -> Option<Expr> {
    match name.two_parts()? {
        // The number of characters, not bytes.
        ("String", "length") => Some(lit(text.chars().count() as u128)),
        // The number of bytes in the UTF-8 encoding. A Rust `str` is already
        // UTF-8, so this is its length.
        ("String", "utf8ByteSize") => Some(lit(text.len() as u128)),
        _ => None,
    }
}

/// Returns `true` if `name` is a function that [`string_op`] computes.
pub fn is_string_op(name: &Name) -> bool {
    string_op(name, "").is_some()
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let next = a % b;
        a = b;
        b = next;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::{NatShape, binop, shape, to_ctor, value};
    use crate::expr::Expr;
    use rean_core::Name;

    #[test]
    fn a_literal_reads_back_as_a_number() {
        assert_eq!(value(&Expr::nat("17")), Some(17));
        assert_eq!(value(&Expr::prop()), None);
    }

    #[test]
    fn a_number_too_large_for_u128_does_not_read() {
        let huge = "1".repeat(50);
        assert_eq!(value(&Expr::nat(huge.as_str())), None);
    }

    #[test]
    fn to_ctor_peels_one_successor() {
        assert_eq!(to_ctor(0).pretty(), "Nat.zero");
        assert_eq!(to_ctor(3).pretty(), "Nat.succ 2");
    }

    #[test]
    fn shape_reads_a_constructor_application() {
        assert!(matches!(
            shape(&Expr::const_("Nat.zero", vec![])),
            Some(NatShape::Zero)
        ));
        assert!(matches!(
            shape(&Expr::const_("Nat.succ", vec![]).app(Expr::nat("4"))),
            Some(NatShape::Succ(_))
        ));
        assert!(shape(&Expr::nat("4")).is_none());
    }

    #[test]
    fn arithmetic_computes() {
        let at = |name: &str, a, b| binop(&Name::from_dotted(name), a, b).map(|e| e.pretty());
        assert_eq!(at("Nat.add", 2, 3).as_deref(), Some("5"));
        assert_eq!(at("Nat.mul", 6, 7).as_deref(), Some("42"));
        assert_eq!(at("Nat.pow", 2, 10).as_deref(), Some("1024"));
        assert_eq!(at("Nat.gcd", 12, 18).as_deref(), Some("6"));
        assert_eq!(at("Nat.beq", 3, 3).as_deref(), Some("Bool.true"));
        assert_eq!(at("Nat.ble", 4, 3).as_deref(), Some("Bool.false"));
        assert_eq!(at("Nat.wat", 1, 1), None);
    }

    #[test]
    fn subtraction_stops_at_zero() {
        // A Lean `Nat` has no negative value. `2 - 5` is `0`.
        let at = |a, b| binop(&Name::from_dotted("Nat.sub"), a, b).map(|e| e.pretty());
        assert_eq!(at(5, 2).as_deref(), Some("3"));
        assert_eq!(at(2, 5).as_deref(), Some("0"));
    }

    #[test]
    fn division_by_zero_gives_zero() {
        // Lean defines it that way, so that the function stays total.
        let at = |name: &str, a, b| binop(&Name::from_dotted(name), a, b).map(|e| e.pretty());
        assert_eq!(at("Nat.div", 7, 0).as_deref(), Some("0"));
        assert_eq!(at("Nat.mod", 7, 0).as_deref(), Some("7"));
    }

    #[test]
    fn an_overflow_refuses_to_answer() {
        // A wrong answer is worse than no answer.
        assert_eq!(binop(&Name::from_dotted("Nat.mul"), u128::MAX, 2), None);
        assert_eq!(binop(&Name::from_dotted("Nat.pow"), 2, 1000), None);
    }
}
