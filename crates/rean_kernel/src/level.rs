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

    /// Returns `true` when no instantiation of `self` can be `Zero`.
    ///
    /// # Why a checker needs this and not [`Self::is_zero`]
    ///
    /// `Sort u` is not `Prop`, and it **becomes** `Prop` when somebody writes
    /// `u := 0`. A rule that asks "is this level zero?" of a universe parameter
    /// gets `false` and lets through everything the rule exists to stop.
    ///
    /// That is a soundness hole, and the Lean Kernel Arena has it as a test
    /// called `large-elim-param`. `MyBool.{u} : Sort u` has two constructors,
    /// so at `u := 0` it is a `Prop` with two elements and its recursor must
    /// not eliminate into a `Type`. We accepted `MyBool.rec.{1, 0}`, and eight
    /// lines later the file proves `False`. See chapter 28.
    ///
    /// The cases:
    ///
    /// - `Zero` is zero.
    /// - `Succ _` is never zero, whatever is inside it.
    /// - `Max a b` is never zero when **either** side is never zero.
    /// - `IMax a b` is `0` exactly when `b` is `0`, and otherwise it is
    ///   `Max a b`, so it is never zero exactly when `b` is never zero.
    /// - `Param _` **can** be zero, and that is the whole point of this
    ///   function.
    pub fn is_never_zero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false,
            Level::Succ(_) => true,
            Level::Max(a, b) => a.is_never_zero() || b.is_never_zero(),
            Level::IMax(_, b) => b.is_never_zero(),
        }
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

    /// Adds every parameter name in `self` to `out`, with no repeats.
    pub fn collect_params(&self, out: &mut Vec<Name>) {
        match self {
            Level::Zero => {}
            Level::Succ(inner) => inner.collect_params(out),
            Level::Max(a, b) | Level::IMax(a, b) => {
                a.collect_params(out);
                b.collect_params(out);
            }
            Level::Param(name) => {
                if !out.contains(name) {
                    out.push(name.clone());
                }
            }
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
        self.substitute_opt(params, args)
            .unwrap_or_else(|| self.clone())
    }

    /// Like [`Self::substitute`], and returns `None` when nothing changed.
    ///
    /// Chapter 17 taught this to [`Expr::instantiate_at`] and the profile moved:
    /// an unchanged subterm keeps its existing [`Arc`] and costs one reference
    /// count bump instead of a fresh allocation.
    ///
    /// The δ rule asks for this on **every** unfold, and the value of a
    /// definition is mostly levels that no parameter touches. `Nat.casesOn`
    /// unfolds 283,803 times in one declaration of the prelude, and the old
    /// version rebuilt every `Level` node of it each time.
    ///
    /// [`Expr::instantiate_at`]: crate::expr::Expr::instantiate_at
    pub fn substitute_opt(&self, params: &[Name], args: &[Level]) -> Option<Level> {
        match self {
            Level::Zero => None,
            Level::Succ(inner) => Some(Level::Succ(Arc::new(inner.substitute_opt(params, args)?))),
            Level::Max(a, b) => {
                let (x, y) = (
                    a.substitute_opt(params, args),
                    b.substitute_opt(params, args),
                );
                if x.is_none() && y.is_none() {
                    return None;
                }
                Some(Level::Max(
                    x.map(Arc::new).unwrap_or_else(|| Arc::clone(a)),
                    y.map(Arc::new).unwrap_or_else(|| Arc::clone(b)),
                ))
            }
            Level::IMax(a, b) => {
                let (x, y) = (
                    a.substitute_opt(params, args),
                    b.substitute_opt(params, args),
                );
                if x.is_none() && y.is_none() {
                    return None;
                }
                Some(Level::IMax(
                    x.map(Arc::new).unwrap_or_else(|| Arc::clone(a)),
                    y.map(Arc::new).unwrap_or_else(|| Arc::clone(b)),
                ))
            }
            Level::Param(name) => params
                .iter()
                .position(|p| p == name)
                .map(|index| args.get(index).cloned().unwrap_or(Level::Zero)),
        }
    }

    /// Rewrites `self` into a canonical shape.
    ///
    /// Two levels that mean the same thing must reach the same shape, or
    /// `is_def_eq` reports a mismatch on a correct program. Running the checker
    /// over the Lean prelude showed how much this matters: a weak normal form
    /// caused 809 of 895 failures, and every one of them was a `Sort` compared
    /// with the same `Sort` written differently.
    ///
    /// The form is a `max` over atoms, each with a count of successors on top.
    /// Four rules get there:
    ///
    /// 1. `imax u 0` becomes `0`, and `imax u (v+1)` becomes `max u (v+1)`,
    ///    because a successor is never zero.
    /// 2. `succ (max a b)` becomes `max (a+1) (b+1)`, so a successor never
    ///    hides a `max`.
    /// 3. A nested `max` flattens into one list.
    /// 4. In that list, a dominated entry goes away, and what is left is
    ///    sorted. So `max u (max u v)` becomes `max u v`, and `max (u+1) 1`
    ///    becomes `u+1`.
    ///
    /// An `imax` whose right side is a bare parameter cannot be resolved, so it
    /// stays as an atom of the list.
    pub fn normalize(&self) -> Level {
        match self {
            Level::Zero | Level::Param(_) => self.clone(),
            Level::Succ(inner) => {
                let inner = inner.normalize();
                match &inner {
                    // A successor must never hide a `max`, so distribute it
                    // over the branches.
                    Level::Max(_, _) => {
                        let mut parts = Vec::new();
                        flatten(&inner, &mut parts);
                        for (_, offset) in parts.iter_mut() {
                            *offset += 1;
                        }
                        rebuild_max(parts)
                    }
                    _ => Level::Succ(Arc::new(inner)),
                }
            }
            Level::IMax(a, b) => {
                let right = b.normalize();
                // `imax u 0` is `0`. That is what makes `Prop` impredicative.
                if right.is_zero() {
                    return Level::Zero;
                }
                let left = a.normalize();
                // The right side is never zero, so `imax` acts like `max`.
                if right.is_never_zero() {
                    let mut parts = Vec::new();
                    flatten(&left, &mut parts);
                    flatten(&right, &mut parts);
                    return rebuild_max(parts);
                }
                // `imax a b` is `b` whenever `a` is at most one.
                //
                // Read the definition. If `b` is zero the answer is zero,
                // which is `b`. If `b` is not zero then `b` is at least one,
                // so `max a b` is `b`. Either way the left side drops out.
                //
                // Leaving this rule out cost 48 declarations of the Lean
                // prelude on its own, all of them `imax 0 u` against `u`.
                if left.to_nat().is_some_and(|value| value <= 1) {
                    return right;
                }
                if left == right {
                    return left;
                }
                Level::IMax(Arc::new(left), Arc::new(right))
            }
            Level::Max(a, b) => {
                let left = a.normalize();
                let right = b.normalize();
                let mut parts = Vec::new();
                flatten(&left, &mut parts);
                flatten(&right, &mut parts);
                rebuild_max(parts)
            }
        }
    }

    /// Returns whether `self` is at most `other`, when that can be decided.
    ///
    /// `None` means **undecided**, and a caller must then accept. A check that
    /// refuses what it does not understand would refuse correct Lean.
    ///
    /// The question is "does `self ≤ other` hold for **every** value of every
    /// parameter", so one assignment that breaks it is a refusal. The cheap
    /// rules come first:
    ///
    /// - two closed levels compare by value
    /// - `u ≤ u`
    /// - `u+1 ≤ v+1` when `u ≤ v`
    /// - `u ≤ max a b` when `u ≤ a` or `u ≤ b`
    /// - `max a b ≤ v` when both `a ≤ v` and `b ≤ v`
    /// - `u ≤ v+1` when `u ≤ v`
    ///
    /// When those do not settle it, [`leq_without_imax`] decides, and `imax`
    /// is the only shape that is left undecided.
    pub fn is_leq(&self, other: &Level) -> Option<bool> {
        leq_normal(&self.normalize(), &other.normalize())
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
            // Unreachable, for the same reason: a closed level took the fast
            // path above. The arm exists because the `match` must be complete.
            Level::Zero => f.write_str("0"),
            Level::Succ(inner) => write!(f, "{inner}+1"),
            Level::Max(a, b) => write!(f, "max {a} {b}"),
            Level::IMax(a, b) => write!(f, "imax {a} {b}"),
            Level::Param(name) => write!(f, "{name}"),
        }
    }
}

/// Flattens an **already normal** `max` into `(atom, successor count)` pairs.
///
/// The input must be normal. Normalizing here instead would re-normalize every
/// sub level once per level of nesting, and that cost is not theoretical: it
/// took the Lean prelude run from 81 seconds to over 10 minutes.
fn flatten(level: &Level, out: &mut Vec<(Level, u32)>) {
    match level {
        Level::Max(a, b) => {
            flatten(a, out);
            flatten(b, out);
        }
        other => out.push(strip_succ(other)),
    }
}

/// Compares two **already normal** levels. See [`Level::is_leq`].
fn leq_normal(left: &Level, right: &Level) -> Option<bool> {
    if left == right {
        return Some(true);
    }
    if let (Some(a), Some(b)) = (left.to_nat(), right.to_nat()) {
        return Some(a <= b);
    }
    // `u+1 ≤ v+1` reduces to `u ≤ v`. Try it before the looser rules.
    if let (Level::Succ(a), Level::Succ(b)) = (left, right)
        && leq_normal(a, b) == Some(true)
    {
        return Some(true);
    }
    // Every branch of a `max` on the left must fit.
    if let Level::Max(a, b) = left
        && leq_normal(a, right) == Some(true)
        && leq_normal(b, right) == Some(true)
    {
        return Some(true);
    }
    // One branch of a `max` on the right is enough.
    if let Level::Max(a, b) = right
        && (leq_normal(left, a) == Some(true) || leq_normal(left, b) == Some(true))
    {
        return Some(true);
    }
    // Room to spare on the right.
    if let Level::Succ(b) = right
        && leq_normal(left, b) == Some(true)
    {
        return Some(true);
    }
    // Nothing above said yes, and that is not the same as no.
    leq_without_imax(left, right)
}

/// Decides `left ≤ right` when no `imax` is left in either **normal** level.
///
/// # Why this can answer `false`
///
/// A normal level is a `max` of parts, and each part is an atom with a count
/// of successors on top. Without `imax`, every atom is either `0` or a
/// parameter, and a parameter can take any value. So one assignment is enough
/// to refuse the whole question, and two of them decide it:
///
/// - give **every** parameter the value `0`. A part `0+k` on the left then
///   needs a part on the right whose count is at least `k`.
/// - give **one** parameter `p` a huge value and the rest `0`. Only a part
///   based on `p` grows with it, so a part `p+k` on the left needs a part
///   `p+m` on the right with `m` at least `k`.
///
/// Both conditions are the same sentence, and that sentence is also enough for
/// `true`, because an atom is never negative.
///
/// # Why `imax` is left out
///
/// `imax u v` is `0` when `v` is `0` and `max u v` otherwise, so an atom of
/// that shape is two levels at once and the argument above does not hold for
/// it. The real Lean kernel decides this case by splitting on `v`, once for
/// `0` and once for `v+1`. We do not, so the answer stays `None` and the
/// caller accepts. That is the last gap in this order.
///
/// # Why a `false` here is worth having
///
/// `TypeChecker::check_field_universes` is the caller, and it accepts whatever
/// this cannot decide. A constructor field in `Sort u` inside a type that
/// promises `Sort v` is the shape of Russell's paradox, and the old answer of
/// `None` accepted it.
fn leq_without_imax(left: &Level, right: &Level) -> Option<bool> {
    let mut left_parts = Vec::new();
    flatten(left, &mut left_parts);
    let mut right_parts = Vec::new();
    flatten(right, &mut right_parts);
    let an_imax = |(atom, _): &(Level, u32)| !matches!(atom, Level::Zero | Level::Param(_));
    if left_parts.iter().any(an_imax) || right_parts.iter().any(an_imax) {
        return None;
    }
    Some(left_parts.iter().all(|(atom, count)| {
        right_parts
            .iter()
            .any(|(base, room)| room >= count && (atom.is_zero() || base == atom))
    }))
}

/// Splits a level into its atom and the number of successors on top.
fn strip_succ(level: &Level) -> (Level, u32) {
    let mut current = level;
    let mut count = 0;
    while let Level::Succ(inner) = current {
        count += 1;
        current = inner;
    }
    (current.clone(), count)
}

/// Rebuilds a canonical `max` from a flattened list.
fn rebuild_max(parts: Vec<(Level, u32)>) -> Level {
    // The largest plain number in the list.
    let constant = parts
        .iter()
        .filter(|(base, _)| base.is_zero())
        .map(|(_, offset)| *offset)
        .max()
        .unwrap_or(0);

    // For each atom, keep only its largest offset.
    let mut atoms: Vec<(Level, u32)> = Vec::new();
    for (base, offset) in parts {
        if base.is_zero() {
            continue;
        }
        match atoms.iter_mut().find(|(seen, _)| *seen == base) {
            Some((_, best)) => *best = (*best).max(offset),
            None => atoms.push((base, offset)),
        }
    }

    // An atom is at least zero, so `atom + k` is at least `k`. A plain number
    // no larger than some atom's offset is therefore dominated.
    let dominated = atoms.iter().any(|(_, offset)| *offset >= constant);
    // One order, so that two equal levels reach one shape. The comparison
    // walks the structure rather than render a string, because `normalize`
    // runs on every level comparison and a string per comparison is too much.
    atoms.sort_by(|(a, ka), (b, kb)| compare(a, b).then(ka.cmp(kb)));

    let mut pieces: Vec<Level> = Vec::new();
    if !dominated || atoms.is_empty() {
        pieces.push(Level::of_nat(constant));
    }
    for (base, offset) in atoms {
        let mut piece = base;
        for _ in 0..offset {
            piece = piece.succ();
        }
        pieces.push(piece);
    }
    let mut result = pieces.remove(0);
    for piece in pieces {
        result = Level::Max(Arc::new(result), Arc::new(piece));
    }
    result
}

/// A total order on levels, for a canonical `max`.
///
/// The order has no meaning of its own. It only has to be the same every time,
/// so that two equal levels reach one shape.
fn compare(a: &Level, b: &Level) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    fn tag(level: &Level) -> u8 {
        match level {
            Level::Zero => 0,
            Level::Param(_) => 1,
            Level::Succ(_) => 2,
            Level::Max(_, _) => 3,
            Level::IMax(_, _) => 4,
        }
    }
    match tag(a).cmp(&tag(b)) {
        Ordering::Equal => {}
        other => return other,
    }
    match (a, b) {
        (Level::Zero, Level::Zero) => Ordering::Equal,
        (Level::Param(x), Level::Param(y)) => x.to_string().cmp(&y.to_string()),
        (Level::Succ(x), Level::Succ(y)) => compare(x, y),
        (Level::Max(x1, y1), Level::Max(x2, y2)) | (Level::IMax(x1, y1), Level::IMax(x2, y2)) => {
            compare(x1, x2).then_with(|| compare(y1, y2))
        }
        _ => Ordering::Equal,
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
