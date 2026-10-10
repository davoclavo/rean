//! The node kinds that the core language uses.
//!
//! A kind is only a [`Name`]. Nothing here is special to the compiler. A
//! `syntax` command in a Lean file can add a kind at run time, and that kind
//! works the same way. The functions below are a convenience, so that the
//! parser does not spell the same string twice.

use rean_core::Name;

/// Builds a kind name under the `Rean.Parser` prefix.
fn kind(path: &str) -> Name {
    Name::from_dotted("Rean.Parser").append(&Name::from_dotted(path))
}

/// A whole file: a list of commands.
pub fn module() -> Name {
    kind("Module")
}

/// A `def` command.
pub fn command_def() -> Name {
    kind("Command.def")
}

/// A function application, such as `f x`.
pub fn term_app() -> Name {
    kind("Term.app")
}

/// A lambda, such as `fun x => x`.
pub fn term_fun() -> Name {
    kind("Term.fun")
}

/// A function type, such as `Nat → Nat`.
pub fn term_arrow() -> Name {
    kind("Term.arrow")
}

/// A term inside brackets, such as `(x)`.
pub fn term_paren() -> Name {
    kind("Term.paren")
}

/// A `Type` or a `Prop` or a `Sort u`.
pub fn term_sort() -> Name {
    kind("Term.sort")
}

/// A binder group, such as `(x : Nat)`.
pub fn binder() -> Name {
    kind("Binder")
}

#[cfg(test)]
mod tests {
    use super::{command_def, module};

    #[test]
    fn a_kind_is_a_hierarchical_name() {
        assert_eq!(module().to_string(), "Rean.Parser.Module");
        assert_eq!(command_def().to_string(), "Rean.Parser.Command.def");
    }
}
