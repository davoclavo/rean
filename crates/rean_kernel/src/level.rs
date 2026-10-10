//! Universe levels.
//!
//! Lean needs levels because `Type` cannot hold itself. `Type 0` lives in
//! `Type 1`, and `Type 1` lives in `Type 2`. A level is the argument of `Sort`.
//!
//! A level is not only a number. A polymorphic definition needs a level
//! variable, so `Level::Param` holds a name. `Max` and `IMax` then combine
//! levels that the compiler does not know yet.
//!
//! `IMax u v` is `0` when `v` is `0`, and `Max u v` otherwise. The case exists
//! because of `Prop`. A function into `Prop` is a proposition, whatever the
//! level of its argument is.

use rean_core::Name;
use std::fmt;
use std::sync::Arc;

/// A universe level.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Level {
    /// Level `0`. `Sort 0` is `Prop`.
    Zero,
    /// One more than another level.
    Succ(Arc<Level>),
    /// The larger of two levels.
    Max(Arc<Level>, Arc<Level>),
    /// `Zero` if the second level is `Zero`, else the larger of the two.
    IMax(Arc<Level>, Arc<Level>),
    /// A level variable of a polymorphic definition, such as the `u` of
    /// `List.{u}`.
    Param(Name),
}

impl Level {
    /// Returns the level `n`.
    pub fn of_nat(n: u32) -> Level {
        let mut level = Level::Zero;
        for _ in 0..n {
            level = level.succ();
        }
        level
    }

    /// Returns one more than `self`.
    pub fn succ(&self) -> Level {
        Level::Succ(Arc::new(self.clone()))
    }

    /// Returns the larger of `self` and `other`.
    pub fn max(&self, other: &Level) -> Level {
        Level::Max(Arc::new(self.clone()), Arc::new(other.clone()))
    }

    /// Returns the impredicative maximum of `self` and `other`.
    pub fn imax(&self, other: &Level) -> Level {
        Level::IMax(Arc::new(self.clone()), Arc::new(other.clone()))
    }

    /// Builds a level variable.
    pub fn param(name: impl Into<Name>) -> Level {
        Level::Param(name.into())
    }

    /// Returns `true` if `self` is exactly `Zero`.
    pub fn is_zero(&self) -> bool {
        matches!(self, Level::Zero)
    }

    /// Returns the value of `self` as a number, if `self` holds no variable.
    pub fn to_nat(&self) -> Option<u32> {
        match self {
            Level::Zero => Some(0),
            Level::Succ(inner) => inner.to_nat().map(|n| n + 1),
            Level::Max(a, b) => Some(a.to_nat()?.max(b.to_nat()?)),
            Level::IMax(a, b) => {
                let b = b.to_nat()?;
                if b == 0 {
                    Some(0)
                } else {
                    Some(a.to_nat()?.max(b))
                }
            }
            Level::Param(_) => None,
        }
    }

    /// Returns `true` if `self` holds no level variable.
    pub fn is_closed(&self) -> bool {
        self.to_nat().is_some()
    }

    /// Replaces each parameter in `params` with the level at the same position
    /// in `args`.
    ///
    /// The δ rule needs this method. A polymorphic definition such as
    /// `List.{u}` stores its value with `u` as a parameter. The call site
    /// supplies the real level, so the value must take it before it is used.
    pub fn substitute(&self, params: &[Name], args: &[Level]) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(inner) => Level::Succ(Arc::new(inner.substitute(params, args))),
            Level::Max(a, b) => Level::Max(
                Arc::new(a.substitute(params, args)),
                Arc::new(b.substitute(params, args)),
            ),
            Level::IMax(a, b) => Level::IMax(
                Arc::new(a.substitute(params, args)),
                Arc::new(b.substitute(params, args)),
            ),
            Level::Param(name) => match params.iter().position(|p| p == name) {
                Some(index) => args.get(index).cloned().unwrap_or(Level::Zero),
                None => self.clone(),
            },
        }
    }

    /// Rewrites `self` into a shape that compares well.
    ///
    /// Three rules do the work:
    ///
    /// - `max u u` becomes `u`, and so does `max u 0` and `max 0 u`.
    /// - `imax u 0` becomes `0`, and `imax u v` becomes `max u v` when `v` is a
    ///   successor, because a successor is never `0`.
    /// - A closed level becomes a plain chain of `succ`.
    ///
    /// This is weaker than the normal form of the real Lean kernel. It is
    /// enough for the fixture, and the limit is honest rather than hidden.
    pub fn normalize(&self) -> Level {
        if let Some(n) = self.to_nat() {
            return Level::of_nat(n);
        }
        match self {
            Level::Zero | Level::Param(_) => self.clone(),
            Level::Succ(inner) => Level::Succ(Arc::new(inner.normalize())),
            Level::Max(a, b) => {
                let a = a.normalize();
                let b = b.normalize();
                if a == b || b.is_zero() {
                    return a;
                }
                if a.is_zero() {
                    return b;
                }
                a.max(&b)
            }
            Level::IMax(a, b) => {
                let a = a.normalize();
                let b = b.normalize();
                // `imax u 0` is `0`.
                if b.is_zero() {
                    return Level::Zero;
                }
                // A successor is never zero, so `imax` acts like `max` here.
                if matches!(b, Level::Succ(_)) {
                    return Level::Max(Arc::new(a), Arc::new(b)).normalize();
                }
                if a == b {
                    return a;
                }
                a.imax(&b)
            }
        }
    }

    /// Returns `true` if `self` and `other` mean the same level.
    ///
    /// Two closed levels compare by value, so `max 1 4` equals `4`.
    ///
    /// Two open levels compare after [`Level::normalize`], so `max u 0` and `u`
    /// do match. The normal form is weaker than the one in the real Lean
    /// kernel, so a harder pair can still fail.
    pub fn is_equiv(&self, other: &Level) -> bool {
        match (self.to_nat(), other.to_nat()) {
            (Some(a), Some(b)) => a == b,
            _ => self == other || self.normalize() == other.normalize(),
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // A closed level prints as a plain number, which reads better.
        if let Some(n) = self.to_nat() {
            return write!(f, "{n}");
        }
        match self {
            Level::Zero => f.write_str("0"),
            Level::Succ(inner) => write!(f, "{inner}+1"),
            Level::Max(a, b) => write!(f, "max {a} {b}"),
            Level::IMax(a, b) => write!(f, "imax {a} {b}"),
            Level::Param(name) => write!(f, "{name}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Level;

    #[test]
    fn a_closed_level_has_a_value() {
        assert_eq!(Level::of_nat(3).to_nat(), Some(3));
        assert_eq!(Level::of_nat(3).to_string(), "3");
    }

    #[test]
    fn a_parameter_has_no_value() {
        let u = Level::param("u");
        assert_eq!(u.to_nat(), None);
        assert!(!u.is_closed());
        assert_eq!(u.succ().to_string(), "u+1");
    }

    #[test]
    fn max_takes_the_larger_level() {
        let level = Level::of_nat(1).max(&Level::of_nat(4));
        assert_eq!(level.to_nat(), Some(4));
    }

    #[test]
    fn imax_collapses_to_zero_for_prop() {
        let u = Level::param("u");
        // A function into `Prop` is a `Prop`, whatever the argument level is.
        let level = u.imax(&Level::Zero);
        assert_eq!(level.to_nat(), Some(0));
        // With a non zero right side, `imax` acts like `max`.
        assert_eq!(Level::of_nat(2).imax(&Level::of_nat(5)).to_nat(), Some(5));
    }

    #[test]
    fn an_open_imax_prints_its_shape() {
        let level = Level::param("u").imax(&Level::param("v"));
        assert_eq!(level.to_string(), "imax u v");
    }
}
