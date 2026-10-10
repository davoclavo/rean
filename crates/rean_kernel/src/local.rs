//! The local context.
//!
//! A type rule reads `Γ ⊢ e : A`, and `Γ` is this type. It is the list of what
//! the checker already knows:
//!
//! ```text
//! Γ  =  x₁ : A₁,  x₂ : A₂,  ...,  xₙ : Aₙ
//! ```
//!
//! # Why a free variable and not a de Bruijn index
//!
//! The checker must look inside the body of a binder. It has two ways:
//!
//! 1. Walk the body with a depth counter and renumber on every step.
//! 2. Replace the bound variable with a fresh [`FVarId`], which never changes
//!    number, and put its type into this context.
//!
//! Lean uses the second way, and so does this code. The elaborator and the
//! checker both walk a term many times, and a renumber on every walk costs too
//! much. [`Expr::instantiate`] opens the binder once, and
//! [`Expr::abstract_fvar`] closes it once at the end.
//!
//! [`Expr::instantiate`]: crate::Expr::instantiate
//! [`Expr::abstract_fvar`]: crate::Expr::abstract_fvar

use crate::expr::{Expr, FVarId};
use rean_core::Name;

/// One entry of the local context.
#[derive(Clone, Debug)]
pub struct LocalDecl {
    /// The identifier that [`Expr::FVar`] holds.
    pub id: FVarId,
    /// The name that the source used. It serves the printer only.
    pub name: Name,
    /// The type of the variable.
    pub ty: Expr,
}

/// The list of free variables that are in scope, with their types.
#[derive(Clone, Debug, Default)]
pub struct LocalContext {
    decls: Vec<LocalDecl>,
    next_id: u64,
}

impl LocalContext {
    /// Builds an empty context.
    pub fn new() -> Self {
        LocalContext::default()
    }

    /// Adds a variable to the end of the context and returns its identifier.
    ///
    /// The identifier is fresh for the life of this context. It never repeats,
    /// even after a [`LocalContext::pop`].
    pub fn push(&mut self, name: Name, ty: Expr) -> FVarId {
        let id = FVarId(self.next_id);
        self.next_id += 1;
        self.decls.push(LocalDecl { id, name, ty });
        id
    }

    /// Removes the last variable. Returns it, or `None` if the context is empty.
    pub fn pop(&mut self) -> Option<LocalDecl> {
        self.decls.pop()
    }

    /// Adds a variable, runs `f`, and then removes the variable again.
    ///
    /// Use this method instead of a manual push and pop. It cannot leak an
    /// entry, not even when `f` returns an error.
    pub fn with_binder<R>(
        &mut self,
        name: Name,
        ty: Expr,
        f: impl FnOnce(&mut Self, FVarId) -> R,
    ) -> R {
        let id = self.push(name, ty);
        let out = f(self, id);
        self.pop();
        out
    }

    /// Returns the type of a variable, or `None` if it is not in scope.
    pub fn type_of(&self, id: FVarId) -> Option<&Expr> {
        self.decls
            .iter()
            .rev()
            .find(|decl| decl.id == id)
            .map(|decl| &decl.ty)
    }

    /// Returns the name of a variable, or `None` if it is not in scope.
    pub fn name_of(&self, id: FVarId) -> Option<&Name> {
        self.decls
            .iter()
            .rev()
            .find(|decl| decl.id == id)
            .map(|decl| &decl.name)
    }

    /// Renders `e` and names every free variable that this context holds.
    ///
    /// Use this method for an error message. `Expr::pretty` cannot reach the
    /// names, so it prints `_f0` instead of `a`.
    pub fn pretty(&self, e: &Expr) -> String {
        e.pretty_with(&|id| self.name_of(id).map(Name::to_string))
    }

    /// Returns every entry, from the outermost to the innermost.
    pub fn decls(&self) -> &[LocalDecl] {
        &self.decls
    }

    /// Returns the number of variables in scope.
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    /// Returns `true` if no variable is in scope.
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::LocalContext;
    use crate::expr::Expr;
    use rean_core::Name;

    #[test]
    fn a_pushed_variable_has_a_type() {
        let mut ctx = LocalContext::new();
        let id = ctx.push(Name::from_dotted("x"), Expr::prop());
        assert_eq!(ctx.type_of(id), Some(&Expr::prop()));
        assert_eq!(ctx.name_of(id), Some(&Name::from_dotted("x")));
        assert_eq!(ctx.len(), 1);
    }

    #[test]
    fn an_identifier_never_repeats() {
        let mut ctx = LocalContext::new();
        let first = ctx.push(Name::from_dotted("x"), Expr::prop());
        ctx.pop();
        let second = ctx.push(Name::from_dotted("x"), Expr::prop());
        assert_ne!(first, second, "a fresh push must not reuse an identifier");
        // The first identifier is out of scope now.
        assert!(ctx.type_of(first).is_none());
    }

    #[test]
    fn with_binder_removes_the_entry_again() {
        let mut ctx = LocalContext::new();
        let id = ctx.with_binder(Name::from_dotted("x"), Expr::prop(), |ctx, id| {
            assert_eq!(ctx.len(), 1);
            id
        });
        assert!(ctx.is_empty());
        assert!(ctx.type_of(id).is_none());
    }

    #[test]
    fn pretty_uses_the_names_of_the_context() {
        let mut ctx = LocalContext::new();
        let id = ctx.push(Name::from_dotted("α"), Expr::prop());
        let term = Expr::arrow(Expr::FVar(id), Expr::FVar(id));
        assert_eq!(term.pretty(), "_f0 → _f0");
        assert_eq!(ctx.pretty(&term), "α → α");
    }

    #[test]
    fn a_variable_that_is_not_in_scope_has_no_type() {
        let ctx = LocalContext::new();
        assert!(ctx.type_of(crate::expr::FVarId(99)).is_none());
    }
}
