//! The driver, as a library.
//!
//! Every command returns a value instead of printing one. `main.rs` does the
//! printing. That split is what makes the driver testable, and a binary that
//! holds its own logic cannot be tested at all.

use rean_core::{DiagnosticBag, SourceMap};
use rean_kernel::{Declaration, Environment, Expr, Level, TypeChecker};
use rean_lexer::{TokenKind, TokenTable, tokenize};
use rean_syntax::{Syntax, kind};

pub const USAGE: &str = "\
rean - a Lean compiler in Rust

usage:
  rean lex <file.lean>   print every token with its position
  rean check <f.ndjson>  check a lean4export file with our kernel
  rean prove             check a proof with the kernel
  rean demo              walk the stages over a small example
  rean help              print this text
";

/// What `lex` found.
#[derive(Debug)]
pub struct LexReport {
    /// One line per token: the position, the kind, and the text.
    pub lines: Vec<String>,
    pub token_count: usize,
    pub error_count: usize,
    /// The rendered diagnostics, empty when the file is clean.
    pub diagnostics: String,
}

/// Reads one file and returns its tokens.
pub fn lex_file(path: &str) -> Result<LexReport, String> {
    let text = std::fs::read_to_string(path).map_err(|err| format!("cannot read {path}: {err}"))?;
    let mut map = SourceMap::new();
    let id = map.add(path, text);
    let file = map.file(id);
    let table = TokenTable::builtin();
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(file, &table, &mut diags);

    let lines = tokens
        .iter()
        .filter(|token| !matches!(token.kind, TokenKind::Eof))
        .map(|token| {
            format!(
                "{:>9}  {:<10}  {}",
                file.line_col(token.span.start).to_string(),
                token.kind.label(),
                token.kind
            )
        })
        .collect();

    Ok(LexReport {
        lines,
        token_count: tokens.len() - 1,
        error_count: diags.error_count(),
        diagnostics: diags.render(file),
    })
}

/// What our kernel said about one declaration.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// The kernel accepted it.
    Ok,
    /// The kernel refused it.
    Failed(String),
    /// It was not checked, because it rests on a declaration that failed.
    ///
    /// A failed declaration must **not** go into the environment. A bogus
    /// declaration in the environment proves anything that uses it. So one
    /// failure makes every later declaration that names it unproven, and
    /// calling that "blocked" rather than "failed" keeps the report readable
    /// without softening the verdict.
    Blocked(String),
}

/// One declaration of a `lean4export` file, and what our kernel said about it.
#[derive(Debug)]
pub struct DeclOutcome {
    pub name: String,
    pub kind: &'static str,
    pub verdict: Verdict,
}

/// What `check` found.
#[derive(Debug)]
pub struct CheckReport {
    pub meta: String,
    pub outcomes: Vec<DeclOutcome>,
}

impl CheckReport {
    /// Returns the number of declarations that the kernel accepted.
    pub fn passed(&self) -> usize {
        self.count(|v| matches!(v, Verdict::Ok))
    }

    /// Returns the number that the kernel refused.
    pub fn failed(&self) -> usize {
        self.count(|v| matches!(v, Verdict::Failed(_)))
    }

    /// Returns the number that rest on a failure and were not checked.
    pub fn blocked(&self) -> usize {
        self.count(|v| matches!(v, Verdict::Blocked(_)))
    }

    fn count(&self, pick: impl Fn(&Verdict) -> bool) -> usize {
        self.outcomes.iter().filter(|o| pick(&o.verdict)).count()
    }

    /// Returns the score line of the level 1 checkpoint.
    pub fn score(&self) -> String {
        let mut line = format!(
            "level 1: checked {} of {} declarations",
            self.passed(),
            self.outcomes.len()
        );
        if self.failed() > 0 || self.blocked() > 0 {
            line.push_str(&format!(
                " ({} failed, {} blocked)",
                self.failed(),
                self.blocked()
            ));
        }
        line
    }
}

/// Reads a `lean4export` file and checks every declaration with our kernel.
///
/// The environment grows one declaration at a time, so a declaration can only
/// use the ones before it. A circular definition cannot slip through.
pub fn check_export(path: &str) -> Result<CheckReport, String> {
    let module =
        rean_export::read_module(path).map_err(|err| format!("cannot read {path}: {err}"))?;

    let mut known = Environment::new();
    let mut rejected: Vec<rean_core::Name> = Vec::new();
    let mut outcomes = Vec::new();

    for name in &module.order {
        let Some(decl) = module.env.get(name) else {
            outcomes.push(DeclOutcome {
                name: name.to_string(),
                kind: "missing",
                verdict: Verdict::Failed("the reader lost this declaration".to_string()),
            });
            continue;
        };

        // Does it rest on something that already failed?
        let mut uses = Vec::new();
        decl.ty().collect_constants(&mut uses);
        if let Some(value) = declaration_value(decl) {
            value.collect_constants(&mut uses);
        }
        let blocker = uses.iter().find(|used| rejected.contains(used));

        let verdict = match blocker {
            Some(blocker) => Verdict::Blocked(format!("`{blocker}` did not check")),
            None => {
                let mut tc = TypeChecker::new(&known);
                match tc.check_declaration(decl) {
                    Ok(()) => {
                        // Only a declaration that checks goes into the
                        // environment. A bogus one would prove anything that
                        // uses it.
                        known.add(decl.clone());
                        Verdict::Ok
                    }
                    Err(err) => Verdict::Failed(err.render(tc.lctx())),
                }
            }
        };
        if !matches!(verdict, Verdict::Ok) {
            rejected.push(name.clone());
        }
        outcomes.push(DeclOutcome {
            name: name.to_string(),
            kind: decl.kind_label(),
            verdict,
        });
    }

    Ok(CheckReport {
        meta: module.meta.to_string(),
        outcomes,
    })
}

/// What `prove` found.
#[derive(Debug)]
pub struct ProveReport {
    /// The proof, printed with names.
    pub proof: String,
    /// The proposition, printed with names.
    pub proposition: String,
    /// The type that `infer_type` gave the proof.
    pub inferred: String,
    /// The universe that the proposition lives in.
    pub lives_in: String,
    /// `None` when the proof checks.
    pub rejected: Option<String>,
    /// The message for a proof that must not check.
    pub bad_proof_message: String,
    /// What still needs an environment.
    pub needs_environment: Vec<String>,
}

/// Checks one proof, then shows what a failed proof looks like.
pub fn prove() -> ProveReport {
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

    let inferred = match tc.infer_type(&proof) {
        Ok(ty) => tc.lctx().pretty(&ty),
        Err(err) => err.render(tc.lctx()),
    };
    let rejected = tc
        .check(&proof, &proposition)
        .err()
        .map(|err| err.render(tc.lctx()));
    let lives_in = match tc.infer_type(&proposition) {
        Ok(ty) => tc.lctx().pretty(&ty),
        Err(err) => err.render(tc.lctx()),
    };

    // A proof of `α → α` does not prove `α → β`.
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
    let bad_proof_message = match tc.check(&bad_proof, &wanted) {
        Ok(()) => "accepted, and that is a bug".to_string(),
        Err(err) => err.render(tc.lctx()),
    };

    let needs_environment = [Expr::const_("Nat", vec![]), Expr::nat("3")]
        .iter()
        .map(|term| match tc.infer_type(term) {
            Ok(ty) => format!("{} : {}", term.pretty(), tc.lctx().pretty(&ty)),
            Err(err) => format!("{} -> {}", term.pretty(), err.render(tc.lctx())),
        })
        .collect();

    ProveReport {
        proof: proof.pretty(),
        proposition: proposition.pretty(),
        inferred,
        lives_in,
        rejected,
        bad_proof_message,
        needs_environment,
    }
}

/// Shows the data structures of the frontend over one small input.
///
/// Returns the whole report as text, because this command is a tour and not a
/// computation.
pub fn demo() -> String {
    use std::fmt::Write as _;
    let source = "def twice (f : Nat → Nat) : Nat → Nat := fun x => f (f x)";
    let mut out = String::new();

    let _ = writeln!(out, "== source ==\n{source}\n");

    // Stage 1. The lexer turns text into tokens.
    let mut map = SourceMap::new();
    let id = map.add("demo.lean", source);
    let file = map.file(id);
    let table = TokenTable::builtin();
    let mut diags = DiagnosticBag::new();
    let tokens = tokenize(file, &table, &mut diags);

    let _ = writeln!(out, "== stage 1: tokens ==");
    let shapes: Vec<String> = tokens
        .iter()
        .filter(|t| !t.is_eof())
        .map(|t| format!("{}:{}", t.kind.label(), t.kind))
        .collect();
    let _ = writeln!(out, "{}\n", shapes.join("  "));

    // Stage 2. This project has no parser yet, so the tree is hand built.
    let _ = writeln!(out, "== stage 2: syntax tree (hand built) ==");
    let leaves: Vec<Syntax> = tokens
        .iter()
        .filter(|token| !token.is_eof())
        .map(|token| Syntax::from_token(token, source))
        .collect();
    let at = |index: usize| leaves[index].clone();
    let arrow = |first: usize| {
        Syntax::node(
            kind::term_arrow(),
            vec![at(first), at(first + 1), at(first + 2)],
        )
    };
    let tree = Syntax::node(
        kind::command_def(),
        vec![
            at(0),
            at(1),
            Syntax::node(kind::binder(), vec![at(2), at(3), at(4), arrow(5), at(8)]),
            at(9),
            arrow(10),
            at(13),
            Syntax::node(
                kind::term_fun(),
                vec![
                    at(14),
                    at(15),
                    at(16),
                    Syntax::node(
                        kind::term_app(),
                        vec![
                            at(17),
                            Syntax::node(
                                kind::term_paren(),
                                vec![
                                    at(18),
                                    Syntax::node(kind::term_app(), vec![at(19), at(20)]),
                                    at(21),
                                ],
                            ),
                        ],
                    ),
                ],
            ),
        ],
    );
    let _ = write!(out, "{}", tree.dump());
    let _ = writeln!(out, "has a parse error: {}\n", tree.has_missing());

    // Stage 3. The elaborator turns the tree into an `Expr`.
    let _ = writeln!(out, "== stage 3: kernel term ==");
    let nat = Expr::const_("Nat", vec![]);
    let nat_to_nat = Expr::arrow(nat.clone(), nat.clone());
    let twice = Expr::lam(
        "f",
        nat_to_nat.clone(),
        Expr::lam(
            "x",
            nat.clone(),
            Expr::bvar(1).app(Expr::bvar(1).app(Expr::bvar(0))),
        ),
    );
    let _ = writeln!(out, "pretty   : {}", twice.pretty());
    let _ = writeln!(
        out,
        "type     : {}",
        Expr::arrow(nat_to_nat, Expr::arrow(nat.clone(), nat)).pretty()
    );
    let _ = writeln!(out, "closed   : {}\n", !twice.has_loose_bvars());

    // Stage 4. One beta step.
    let _ = writeln!(out, "== stage 4: one beta step ==");
    let applied = twice.app(Expr::const_("Nat.succ", vec![]));
    let _ = writeln!(out, "before   : {}", applied.pretty());
    let _ = writeln!(out, "after    : {}\n", applied.beta().pretty());

    let _ = writeln!(out, "== universe levels ==");
    let _ = writeln!(out, "Sort 0      : {}", Expr::prop().pretty());
    let _ = writeln!(out, "Sort 1      : {}", Expr::type_(0).pretty());
    let _ = writeln!(
        out,
        "Sort (u+1)  : {}",
        Expr::sort(Level::param("u").succ()).pretty()
    );
    out
}

/// Returns the value that a declaration must be checked against, if it has one.
fn declaration_value(decl: &Declaration) -> Option<&Expr> {
    match decl {
        Declaration::Definition(d) => Some(&d.value),
        Declaration::Theorem(d) => Some(&d.value),
        Declaration::Opaque(d) => Some(&d.value),
        _ => None,
    }
}
