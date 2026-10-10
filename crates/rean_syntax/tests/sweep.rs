//! Every `Syntax` shape, and every token that becomes one.

use rean_core::{DiagnosticBag, Name, SourceMap, Span};
use rean_lexer::{TokenTable, tokenize};
use rean_syntax::{Syntax, kind};

/// Lexes `text` and turns each token into a leaf.
fn leaves(text: &str) -> Vec<Syntax> {
    let mut map = SourceMap::new();
    let id = map.add("t.lean", text);
    let file = map.file(id);
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(file, &TokenTable::builtin(), &mut diags);
    tokens
        .iter()
        .map(|token| Syntax::from_token(token, text))
        .collect()
}

#[test]
fn every_token_kind_becomes_a_leaf() {
    // A keyword, an identifier, a symbol, a number, a string, a character, a
    // doc comment, and the end of the file.
    let text = "/-- doc -/ def x.y := 0xFF \"s\" 'c' 1.5";
    let built = leaves(text);
    // The doc comment keeps its source text as an atom.
    assert!(built[0].as_atom().unwrap().contains("doc"));
    // A keyword is an atom with the table text.
    assert_eq!(built[1].as_atom(), Some("def"));
    // An identifier keeps a hierarchical name.
    assert_eq!(built[2].as_ident(), Some(&Name::from_dotted("x.y")));
    assert_eq!(built[3].as_atom(), Some(":="));
    // A literal becomes an atom that holds the source text, so the tree stays
    // lossless.
    assert_eq!(built[4].as_atom(), Some("0xFF"));
    assert_eq!(built[5].as_atom(), Some("\"s\""));
    assert_eq!(built[6].as_atom(), Some("'c'"));
    assert_eq!(built[7].as_atom(), Some("1.5"));
    // The end of the file has no tree, so it becomes `Missing`.
    assert!(built.last().unwrap().has_missing());
    assert!(built.last().unwrap().span().is_none());
}

#[test]
fn an_unknown_character_becomes_an_atom() {
    let mut map = SourceMap::new();
    let text = "a ∰ b";
    let id = map.add("t.lean", text);
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(map.file(id), &TokenTable::builtin(), &mut diags);
    assert_eq!(diags.error_count(), 1);
    let leaf = Syntax::from_token(&tokens[1], text);
    assert_eq!(leaf.as_atom(), Some("∰"));
}

#[test]
fn every_accessor_answers_for_every_shape() {
    let atom = Syntax::atom(Span::new(0, 1), "(");
    let missing = Syntax::Missing;
    let ident = leaves("x")[0].clone();
    let node = Syntax::node(kind::term_app(), vec![ident.clone(), atom.clone()]);

    // `kind` only answers for a node.
    assert!(atom.kind().is_none());
    assert!(missing.kind().is_none());
    assert!(ident.kind().is_none());
    assert_eq!(node.kind(), Some(&kind::term_app()));
    assert!(node.is_of_kind(&kind::term_app()));
    assert!(!node.is_of_kind(&kind::term_fun()));
    assert!(!atom.is_of_kind(&kind::term_app()));

    // `args` only answers for a node.
    assert!(atom.args().is_empty());
    assert!(missing.args().is_empty());
    assert_eq!(node.args().len(), 2);
    assert!(node.arg(0).is_some());
    assert!(node.arg(9).is_none());

    // `as_atom` and `as_ident` each answer for one shape.
    assert_eq!(atom.as_atom(), Some("("));
    assert!(ident.as_atom().is_none());
    assert!(node.as_atom().is_none());
    assert!(missing.as_atom().is_none());
    assert!(atom.as_ident().is_none());
    assert!(ident.as_ident().is_some());
    assert!(node.as_ident().is_none());

    // `span` answers for all but `Missing`.
    assert!(atom.span().is_some());
    assert!(ident.span().is_some());
    assert!(node.span().is_some());
    assert!(missing.span().is_none());

    // `has_missing` walks the whole tree.
    assert!(!node.has_missing());
    assert!(Syntax::node(kind::term_app(), vec![node, missing]).has_missing());
}

#[test]
fn a_node_with_no_child_gets_an_empty_span() {
    let empty = Syntax::node(kind::module(), Vec::new());
    assert_eq!(empty.span(), Some(Span::empty(0)));
    assert_eq!(empty.to_string(), "(Rean.Parser.Module)");
}

#[test]
fn display_and_dump_cover_every_shape() {
    let tree = Syntax::node(
        kind::term_sort(),
        vec![
            Syntax::atom(Span::new(0, 4), "Type"),
            leaves("x")[0].clone(),
            Syntax::Missing,
        ],
    );
    let one_line = tree.to_string();
    assert!(one_line.contains("Type"));
    assert!(one_line.contains("<missing>"));
    let many_lines = tree.dump();
    assert!(many_lines.contains("\"Type\""));
    assert!(many_lines.contains("(ident x)"));
    assert!(many_lines.contains("<missing>"));
}

#[test]
fn every_kind_name_is_distinct() {
    let kinds = [
        kind::module(),
        kind::command_def(),
        kind::term_app(),
        kind::term_fun(),
        kind::term_arrow(),
        kind::term_paren(),
        kind::term_sort(),
        kind::binder(),
    ];
    for (i, left) in kinds.iter().enumerate() {
        assert!(left.to_string().starts_with("Rean.Parser."));
        for (j, right) in kinds.iter().enumerate() {
            if i != j {
                assert_ne!(left, right);
            }
        }
    }
}
