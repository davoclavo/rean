//! The driver.
//!
//! The driver owns the stages and the order of the stages. Each library crate
//! stays free of input and output, so a test can call it directly.

use rean_core::{DiagnosticBag, SourceMap};
use rean_kernel::{Environment, Expr, Level, TypeChecker};
use rean_lexer::{TokenKind, TokenTable, tokenize};
use rean_syntax::{Syntax, kind};
use std::process::ExitCode;

const USAGE: &str = "\
rean - a Lean compiler in Rust

usage:
  rean lex <file.lean>   print every token with its position
  rean demo              walk the stages over a small example
  rean prove             check a proof with the kernel
  rean check <f.ndjson>  check a lean4export file with our kernel
  rean help              print this text
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("lex") => match args.get(1) {
            Some(path) => lex_file(path),
            None => fail("lex needs a path"),
        },
        Some("demo") => {
            demo();
            ExitCode::SUCCESS
        }
        Some("prove") => prove(),
        Some("check") => match args.get(1) {
            Some(path) => check_export(path),
            None => fail("check needs a path to an .ndjson file"),
        },
        Some("help") | Some("--help") | Some("-h") | None => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Some(other) => fail(&format!("unknown command `{other}`")),
    }
}

fn fail(message: &str) -> ExitCode {
    eprintln!("error: {message}\n\n{USAGE}");
    ExitCode::FAILURE
}

/// Reads one file and prints its tokens.
fn lex_file(path: &str) -> ExitCode {
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => return fail(&format!("cannot read {path}: {err}")),
    };

    let mut map = SourceMap::new();
    let id = map.add(path, text);
    let file = map.file(id);
    let table = TokenTable::builtin();
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(file, &table, &mut diags);

    for token in &tokens {
        if matches!(token.kind, TokenKind::Eof) {
            continue;
        }
        println!(
            "{:>9}  {:<10}  {}",
            file.line_col(token.span.start).to_string(),
            token.kind.label(),
            token.kind
        );
    }

    if diags.is_empty() {
        println!("\n{} tokens, no error", tokens.len() - 1);
        return ExitCode::SUCCESS;
    }
    print!("\n{}", diags.render(file));
    println!("{} error(s)", diags.error_count());
    ExitCode::FAILURE
}

/// Shows the three data structures of the frontend over one small input.
fn demo() {
    let source = "def twice (f : Nat → Nat) : Nat → Nat := fun x => f (f x)";

    println!("== source ==\n{source}\n");

    // Stage 1. The lexer turns text into tokens. The token table decides
    // which words are keywords.
    let mut map = SourceMap::new();
    let id = map.add("demo.lean", source);
    let file = map.file(id);
    let table = TokenTable::builtin();
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(file, &table, &mut diags);

    println!("== stage 1: tokens ==");
    let line: Vec<String> = tokens
        .iter()
        .filter(|t| !t.is_eof())
        .map(|t| format!("{}:{}", t.kind.label(), t.kind))
        .collect();
    println!("{}\n", line.join("  "));

    // Stage 2. The parser builds a `Syntax` tree. This project has no parser
    // yet, so the tree below is hand built. It shows the shape that a parser
    // must produce: one node kind for every notation, and every token kept.
    println!("== stage 2: syntax tree (hand built) ==");
    let leaves: Vec<Syntax> = tokens
        .iter()
        .filter(|token| !token.is_eof())
        .map(|token| Syntax::from_token(token, source))
        .collect();
    // `at` names one token of the source, so the tree below reads like the text.
    let at = |index: usize| leaves[index].clone();
    let nat_to_nat_syntax = |first: usize| {
        Syntax::node(
            kind::term_arrow(),
            vec![at(first), at(first + 1), at(first + 2)],
        )
    };
    let tree = Syntax::node(
        kind::command_def(),
        vec![
            at(0), // `def`
            at(1), // `twice`
            Syntax::node(
                kind::binder(),
                vec![
                    at(2), // `(`
                    at(3), // `f`
                    at(4), // `:`
                    nat_to_nat_syntax(5),
                    at(8), // `)`
                ],
            ),
            at(9), // `:`
            nat_to_nat_syntax(10),
            at(13), // `:=`
            Syntax::node(
                kind::term_fun(),
                vec![
                    at(14), // `fun`
                    at(15), // `x`
                    at(16), // `=>`
                    Syntax::node(
                        kind::term_app(),
                        vec![
                            at(17), // `f`
                            Syntax::node(
                                kind::term_paren(),
                                vec![
                                    at(18), // `(`
                                    Syntax::node(kind::term_app(), vec![at(19), at(20)]),
                                    at(21), // `)`
                                ],
                            ),
                        ],
                    ),
                ],
            ),
        ],
    );
    print!("{}", tree.dump());
    println!("has a parse error: {}\n", tree.has_missing());

    // Stage 3. The elaborator turns the tree into an `Expr`. The names are
    // gone and a bound variable is a number.
    println!("== stage 3: kernel term ==");
    let nat = Expr::const_("Nat", vec![]);
    let nat_to_nat = Expr::arrow(nat.clone(), nat.clone());
    // `fun (f : Nat → Nat) => fun (x : Nat) => f (f x)`
    let twice = Expr::lam(
        "f",
        nat_to_nat.clone(),
        Expr::lam(
            "x",
            nat.clone(),
            // `f` is one binder away, so it is index 1. `x` is index 0.
            Expr::bvar(1).app(Expr::bvar(1).app(Expr::bvar(0))),
        ),
    );
    println!("raw      : {twice:?}");
    println!("pretty   : {}", twice.pretty());
    println!(
        "type     : {}",
        Expr::arrow(nat_to_nat, Expr::arrow(nat.clone(), nat))
    );
    println!("closed   : {}\n", !twice.has_loose_bvars());

    // Stage 4. The kernel reduces. One beta step removes one binder.
    println!("== stage 4: one beta step ==");
    let succ = Expr::const_("Nat.succ", vec![]);
    let applied = twice.app(succ);
    println!("before   : {}", applied.pretty());
    println!("after    : {}\n", applied.beta().pretty());

    // Universe levels are the other half of the kernel.
    println!("== universe levels ==");
    println!("Sort 0      : {}", Expr::prop().pretty());
    println!("Sort 1      : {}", Expr::type_(0).pretty());
    println!(
        "Sort (u+1)  : {}",
        Expr::sort(Level::param("u").succ()).pretty()
    );
    println!(
        "polymorphic : {}",
        Expr::const_("List", vec![Level::param("u")])
            .app(Expr::const_("Nat", vec![]))
            .pretty()
    );
}

/// Checks one proof, then shows what a failed proof looks like.
///
/// This command is chapter 1. See `docs/01-the-type-checker.md`.
fn prove() -> ExitCode {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);

    // `fun (α : Prop) (h : α) => h`
    let proof = Expr::lam(
        "α",
        Expr::prop(),
        Expr::lam("h", Expr::bvar(0), Expr::bvar(0)),
    );
    // `(α : Prop) → α → α`
    let proposition = Expr::forall("α", Expr::prop(), Expr::arrow(Expr::bvar(0), Expr::bvar(0)));

    println!("== the proof ==");
    println!("de Bruijn : {proof:?}");
    println!("readable  : {}", proof.pretty());

    println!("\n== the proposition ==");
    println!("readable  : {}", proposition.pretty());

    println!("\n== infer_type ==");
    match tc.infer_type(&proof) {
        Ok(ty) => println!("the proof has type : {}", tc.lctx().pretty(&ty)),
        Err(err) => {
            eprintln!("error: {}", err.render(tc.lctx()));
            return ExitCode::FAILURE;
        }
    }

    println!("\n== check ==");
    match tc.check(&proof, &proposition) {
        Ok(()) => println!("accepted. The proposition holds."),
        Err(err) => {
            eprintln!("error: {}", err.render(tc.lctx()));
            return ExitCode::FAILURE;
        }
    }

    // The level of the proposition. `imax 1 0 = 0`, so it is a `Prop`.
    match tc.infer_type(&proposition) {
        Ok(ty) => println!("the proposition lives in : {}", tc.lctx().pretty(&ty)),
        Err(err) => eprintln!("error: {}", err.render(tc.lctx())),
    }

    println!("\n== a proof that does not check ==");
    // The term proves `α → α`, and the proposition asks for `α → β`.
    let bad_proof = Expr::lam(
        "α",
        Expr::prop(),
        Expr::lam(
            "β",
            Expr::prop(),
            Expr::lam("h", Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let wanted = Expr::forall(
        "α",
        Expr::prop(),
        Expr::forall("β", Expr::prop(), Expr::arrow(Expr::bvar(1), Expr::bvar(0))),
    );
    println!("the proof  : {}", bad_proof.pretty());
    println!("the claim  : {}", wanted.pretty());
    match tc.check(&bad_proof, &wanted) {
        Ok(()) => println!("accepted, and that is a bug"),
        Err(err) => println!(
            "rejected:\n  {}",
            err.render(tc.lctx()).replace('\n', "\n  ")
        ),
    }

    println!("\n== what still needs chapter 2 ==");
    for term in [Expr::const_("Nat", vec![]), Expr::nat("3")] {
        match tc.infer_type(&term) {
            Ok(ty) => println!("{} : {}", term.pretty(), tc.lctx().pretty(&ty)),
            Err(err) => println!("{} -> {}", term.pretty(), err.render(tc.lctx())),
        }
    }
    let _ = Level::Zero;
    ExitCode::SUCCESS
}

/// Reads a `lean4export` file and checks every declaration with our kernel.
///
/// This is the level 1 checkpoint of `docs/ROADMAP.md`.
fn check_export(path: &str) -> ExitCode {
    let module = match rean_export::read_module(path) {
        Ok(module) => module,
        Err(err) => return fail(&format!("cannot read {path}: {err}")),
    };

    println!("{path}");
    println!("  {}", module.meta);
    println!("  {} declarations\n", module.order.len());

    // Build the environment one declaration at a time. A declaration may only
    // use the ones before it, so a circular definition cannot slip through.
    let mut known = Environment::new();
    let mut passed = 0usize;
    let mut failed = 0usize;

    for name in &module.order {
        let Some(decl) = module.env.get(name) else {
            println!("  MISSING  {name}");
            failed += 1;
            continue;
        };
        let outcome = {
            let mut tc = TypeChecker::new(&known);
            tc.check_declaration(decl)
                .map_err(|err| err.render(tc.lctx()))
        };
        match outcome {
            Ok(()) => {
                println!("  ok    {:10} {name}", decl.kind_label());
                passed += 1;
            }
            Err(message) => {
                println!("  FAIL  {:10} {name}", decl.kind_label());
                for line in message.lines() {
                    println!("          {line}");
                }
                failed += 1;
            }
        }
        // Add it either way, so one failure does not cascade.
        known.add(decl.clone());
    }

    println!(
        "\nlevel 1: checked {passed} of {} declarations",
        passed + failed
    );
    if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
