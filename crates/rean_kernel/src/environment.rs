//! The environment: a map from [`Name`] to a declaration.
//!
//! Chapter 1 could check a term but it could not name one. Nothing had a type
//! unless the local context held it. The environment fixes that, and it unlocks
//! two reduction rules at once:
//!
//! - **δ**, because a [`Declaration::Definition`] carries a value.
//! - **ι**, because a [`Declaration::Recursor`] carries its rules.
//!
//! The shape of these types follows the `lean4export` NDJSON format, so that
//! `rean_export` can read a real Lean file into them with no translation layer.
//! See `docs/ROADMAP.md`.

use crate::expr::Expr;
use rean_core::Name;
use std::collections::{HashMap, HashSet};

/// How eager the elaborator should be to unfold a definition.
///
/// The kernel ignores this field. It belongs to the elaborator, and the format
/// carries it, so we keep it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

/// Whether a definition is safe to trust.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefinitionSafety {
    Safe,
    Unsafe,
    Partial,
}

/// Which of the four quotient constants this is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum QuotKind {
    /// `Quot`
    Type,
    /// `Quot.mk`
    Ctor,
    /// `Quot.lift`
    Lift,
    /// `Quot.ind`
    Ind,
}

/// A name with a type and no value. The kernel trusts it blindly.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AxiomVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    pub is_unsafe: bool,
}

/// A name with a type and a value.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DefinitionVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    pub value: Expr,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
    /// Every name of the mutual group that this definition belongs to.
    pub all: Vec<Name>,
}

/// Like a definition, but the value is a proof.
///
/// The kernel treats the two the same way. The split exists so that a tool can
/// tell a proof from a program.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TheoremVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    pub value: Expr,
    pub all: Vec<Name>,
}

/// A definition whose value the δ rule must not unfold.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OpaqueVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    pub value: Expr,
    pub is_unsafe: bool,
    pub all: Vec<Name>,
}

/// One of the four quotient constants.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct QuotVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    pub kind: QuotKind,
}

/// An inductive type.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct InductiveVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    /// The arguments that stay fixed across every constructor.
    pub num_params: u32,
    /// The arguments that vary, such as the `b` of `a = b`.
    pub num_indices: u32,
    pub all: Vec<Name>,
    pub ctors: Vec<Name>,
    pub num_nested: u32,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// One constructor of an inductive type.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConstructorVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    /// The inductive type that owns this constructor.
    pub induct: Name,
    /// The position of this constructor in the list, counted from 0.
    pub cidx: u32,
    pub num_params: u32,
    /// The arguments after the parameters. These are the fields.
    pub num_fields: u32,
    pub is_unsafe: bool,
}

/// One ι rule: what the recursor becomes for one constructor.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RecursorRule {
    pub ctor: Name,
    pub num_fields: u32,
    /// The right hand side. The ι rule rewrites to this term.
    pub rhs: Expr,
}

/// The recursor of an inductive type.
///
/// The argument order is fixed, and the ι rule depends on it:
///
/// ```text
/// rec  <params>  <motives>  <minors>  <indices>  <major>
/// ```
///
/// So the major premise, the term that the recursor takes apart, sits at
/// position `num_params + num_motives + num_minors + num_indices`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RecursorVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
    pub all: Vec<Name>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Vec<RecursorRule>,
    /// `true` for a K-like recursor, such as `Eq.rec`.
    pub k: bool,
    pub is_unsafe: bool,
}

impl RecursorVal {
    /// Returns the position of the major premise in the argument list.
    pub fn major_index(&self) -> usize {
        (self.num_params + self.num_motives + self.num_minors + self.num_indices) as usize
    }

    /// Returns the number of arguments before the indices and the major premise.
    ///
    /// The ι rule passes exactly these to the right hand side of the rule.
    pub fn num_prefix(&self) -> usize {
        (self.num_params + self.num_motives + self.num_minors) as usize
    }

    /// Returns the rule for `ctor`, if this recursor has one.
    pub fn rule_for(&self, ctor: &Name) -> Option<&RecursorRule> {
        self.rules.iter().find(|rule| rule.ctor == *ctor)
    }
}

/// One entry of the environment.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Declaration {
    Axiom(AxiomVal),
    Definition(DefinitionVal),
    Theorem(TheoremVal),
    Opaque(OpaqueVal),
    Quot(QuotVal),
    Inductive(InductiveVal),
    Constructor(ConstructorVal),
    Recursor(RecursorVal),
}

impl Declaration {
    /// Returns the name of the declaration.
    pub fn name(&self) -> &Name {
        match self {
            Declaration::Axiom(d) => &d.name,
            Declaration::Definition(d) => &d.name,
            Declaration::Theorem(d) => &d.name,
            Declaration::Opaque(d) => &d.name,
            Declaration::Quot(d) => &d.name,
            Declaration::Inductive(d) => &d.name,
            Declaration::Constructor(d) => &d.name,
            Declaration::Recursor(d) => &d.name,
        }
    }

    /// Returns the universe parameters of the declaration.
    pub fn level_params(&self) -> &[Name] {
        match self {
            Declaration::Axiom(d) => &d.level_params,
            Declaration::Definition(d) => &d.level_params,
            Declaration::Theorem(d) => &d.level_params,
            Declaration::Opaque(d) => &d.level_params,
            Declaration::Quot(d) => &d.level_params,
            Declaration::Inductive(d) => &d.level_params,
            Declaration::Constructor(d) => &d.level_params,
            Declaration::Recursor(d) => &d.level_params,
        }
    }

    /// Returns the type of the declaration.
    pub fn ty(&self) -> &Expr {
        match self {
            Declaration::Axiom(d) => &d.ty,
            Declaration::Definition(d) => &d.ty,
            Declaration::Theorem(d) => &d.ty,
            Declaration::Opaque(d) => &d.ty,
            Declaration::Quot(d) => &d.ty,
            Declaration::Inductive(d) => &d.ty,
            Declaration::Constructor(d) => &d.ty,
            Declaration::Recursor(d) => &d.ty,
        }
    }

    /// Returns the value that the δ rule may unfold.
    ///
    /// An `Opaque` declaration has a value and returns `None`, because the δ
    /// rule must not unfold it. That is the whole point of `opaque`.
    pub fn unfoldable_value(&self) -> Option<&Expr> {
        match self {
            Declaration::Definition(d) => Some(&d.value),
            Declaration::Theorem(d) => Some(&d.value),
            _ => None,
        }
    }

    /// Returns the value that the declaration stores, if it stores one.
    ///
    /// Unlike [`Declaration::unfoldable_value`], this includes an `Opaque`
    /// value. Use it to ask what a declaration depends on, not to reduce.
    pub fn value(&self) -> Option<&Expr> {
        match self {
            Declaration::Definition(d) => Some(&d.value),
            Declaration::Theorem(d) => Some(&d.value),
            Declaration::Opaque(d) => Some(&d.value),
            _ => None,
        }
    }

    /// Returns `true` if the declaration is not safe to trust in a proof.
    pub fn is_unsafe(&self) -> bool {
        match self {
            Declaration::Axiom(d) => d.is_unsafe,
            Declaration::Definition(d) => d.safety != DefinitionSafety::Safe,
            Declaration::Opaque(d) => d.is_unsafe,
            Declaration::Inductive(d) => d.is_unsafe,
            Declaration::Constructor(d) => d.is_unsafe,
            Declaration::Recursor(d) => d.is_unsafe,
            Declaration::Theorem(_) | Declaration::Quot(_) => false,
        }
    }

    /// Adds every name that this declaration mentions to `out`.
    ///
    /// The type, the value, and the right hand side of every ι rule all count.
    /// A recursor that calls itself names itself, and that is correct.
    pub fn collect_dependencies(&self, out: &mut Vec<Name>) {
        self.ty().collect_constants(out);
        if let Some(value) = self.value() {
            value.collect_constants(out);
        }
        if let Declaration::Recursor(rec) = self {
            for rule in &rec.rules {
                rule.rhs.collect_constants(out);
                if !out.contains(&rule.ctor) {
                    out.push(rule.ctor.clone());
                }
            }
        }
        if let Declaration::Inductive(ind) = self {
            for ctor in &ind.ctors {
                if !out.contains(ctor) {
                    out.push(ctor.clone());
                }
            }
        }
    }

    /// Returns the word that a report prints for this kind.
    pub fn kind_label(&self) -> &'static str {
        match self {
            Declaration::Axiom(_) => "axiom",
            Declaration::Definition(_) => "def",
            Declaration::Theorem(_) => "theorem",
            Declaration::Opaque(_) => "opaque",
            Declaration::Quot(_) => "quot",
            Declaration::Inductive(_) => "inductive",
            Declaration::Constructor(_) => "ctor",
            Declaration::Recursor(_) => "rec",
        }
    }
}

/// Every declaration that the checker knows.
#[derive(Clone, Default, Debug)]
pub struct Environment {
    decls: HashMap<Name, Declaration>,
}

impl Environment {
    /// Builds an empty environment.
    pub fn new() -> Self {
        Environment::default()
    }

    /// Adds a declaration. Returns the old one if the name was taken.
    pub fn add(&mut self, decl: Declaration) -> Option<Declaration> {
        self.decls.insert(decl.name().clone(), decl)
    }

    /// Returns the declaration for `name`.
    pub fn get(&self, name: &Name) -> Option<&Declaration> {
        self.decls.get(name)
    }

    /// Returns every name in the environment, in no particular order.
    ///
    /// A driver uses this to answer "did you mean?" when a reader asks for a
    /// declaration by a name that is nearly right.
    pub fn names(&self) -> impl Iterator<Item = &Name> {
        self.decls.keys()
    }

    /// Returns `true` if the environment holds `name`.
    pub fn contains(&self, name: &Name) -> bool {
        self.decls.contains_key(name)
    }

    /// Returns the number of declarations.
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    /// Returns `true` if the environment holds nothing.
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// Returns every axiom that `name` rests on, in order of name.
    ///
    /// This is the trust report. The De Bruijn criterion of chapter 0, section
    /// 0.16, says the kernel re-checks everything, so a tactic cannot lie. An
    /// **axiom** is the one thing the kernel does not check: it asks to be
    /// trusted. So the only honest answer to "do you believe this theorem" is
    /// "yes, and here is what it rests on".
    ///
    /// Lean spells the same question `#print axioms`.
    pub fn axioms_of(&self, name: &Name) -> Vec<Name> {
        let mut seen: HashSet<Name> = HashSet::new();
        let mut axioms: Vec<Name> = Vec::new();
        let mut todo = vec![name.clone()];
        while let Some(current) = todo.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            let Some(decl) = self.get(&current) else {
                continue;
            };
            if matches!(decl, Declaration::Axiom(_)) {
                axioms.push(current.clone());
            }
            decl.collect_dependencies(&mut todo);
        }
        axioms.sort_by_key(Name::to_string);
        axioms
    }

    /// Returns how **tall** a definition is, if it unfolds at all.
    ///
    /// Lean records this in [`ReducibilityHints`], and the kernel uses it to
    /// choose which of two sides to unfold. See
    /// [`TypeChecker::lazy_delta`][crate::TypeChecker::lazy_delta].
    ///
    /// An `Abbrev` is meant to disappear on sight, so it counts as taller than
    /// any `Regular`. An `Opaque` definition does not unfold, and neither does
    /// anything that is not a definition, so both give `None`.
    pub fn height(&self, name: &Name) -> Option<u32> {
        let Declaration::Definition(def) = self.get(name)? else {
            // A theorem unfolds, and has no height of its own. Treat it as the
            // shortest, so a definition beside it unfolds first.
            return match self.get(name)? {
                Declaration::Theorem(_) => Some(0),
                _ => None,
            };
        };
        match def.hints {
            ReducibilityHints::Opaque => None,
            ReducibilityHints::Abbrev => Some(u32::MAX),
            ReducibilityHints::Regular(h) => Some(h),
        }
    }

    /// Returns the inductive type that owns `ctor`.    /// Returns the inductive type that owns `ctor`.
    pub fn inductive_of_ctor(&self, ctor: &Name) -> Option<&InductiveVal> {
        let Declaration::Constructor(c) = self.get(ctor)? else {
            return None;
        };
        match self.get(&c.induct)? {
            Declaration::Inductive(i) => Some(i),
            _ => None,
        }
    }

    /// Returns the single constructor of a structure, if it has exactly one.
    ///
    /// A projection only makes sense for a one constructor inductive type.
    pub fn sole_ctor(&self, inductive: &Name) -> Option<&ConstructorVal> {
        let Declaration::Inductive(i) = self.get(inductive)? else {
            return None;
        };
        let [only] = i.ctors.as_slice() else {
            return None;
        };
        match self.get(only)? {
            Declaration::Constructor(c) => Some(c),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{AxiomVal, Declaration, Environment, RecursorVal};
    use crate::expr::Expr;
    use rean_core::Name;

    fn an_axiom(name: &str) -> Declaration {
        Declaration::Axiom(AxiomVal {
            name: Name::from_dotted(name),
            level_params: Vec::new(),
            ty: Expr::prop(),
            is_unsafe: false,
        })
    }

    #[test]
    fn a_declaration_goes_in_and_comes_out() {
        let mut env = Environment::new();
        assert!(env.is_empty());
        assert!(env.add(an_axiom("Foo")).is_none());
        assert_eq!(env.len(), 1);
        let got = env.get(&Name::from_dotted("Foo")).expect("it is there");
        assert_eq!(got.kind_label(), "axiom");
        assert_eq!(got.ty(), &Expr::prop());
    }

    #[test]
    fn an_axiom_has_no_value_for_delta() {
        assert!(an_axiom("Foo").unfoldable_value().is_none());
    }

    #[test]
    fn the_major_premise_sits_after_the_indices() {
        // `Nat.rec` has 0 params, 1 motive, 2 minors, and 0 indices.
        let rec = RecursorVal {
            name: Name::from_dotted("Nat.rec"),
            level_params: Vec::new(),
            ty: Expr::prop(),
            all: Vec::new(),
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: Vec::new(),
            k: false,
            is_unsafe: false,
        };
        assert_eq!(rec.major_index(), 3);
        assert_eq!(rec.num_prefix(), 3);

        // `Eq.rec` has 2 params, 1 motive, 1 minor, and 1 index.
        let eq_rec = RecursorVal {
            num_params: 2,
            num_indices: 1,
            num_motives: 1,
            num_minors: 1,
            ..rec
        };
        assert_eq!(eq_rec.major_index(), 5);
        assert_eq!(eq_rec.num_prefix(), 4);
    }
}
