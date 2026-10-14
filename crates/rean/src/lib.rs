//! The driver, as a library.
//!
//! Every command returns a value instead of printing one. `main.rs` does the
//! printing. That split is what makes the driver testable, and a binary that
//! holds its own logic cannot be tested at all.

pub mod export;

use export::{ExportReport, Toolchain};
use rean_core::{DiagnosticBag, SourceMap};
use rean_kernel::{Declaration, Environment, Expr, Level, LocalContext, TypeChecker};
use rean_lexer::{TokenKind, TokenTable, tokenize};
use rean_syntax::{Syntax, kind};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;

pub const USAGE: &str = "\
rean - a Lean compiler in Rust

usage:
  rean lex <file.lean>   print every token with its position
  rean check <target>    check Lean declarations with our kernel
  rean export <target>   export a target and print the path, without checking
  rean show <target> <name>   print one declaration as the kernel sees it
  rean run <target> <name>    check a declaration, then **run** it
  rean prove             check a proof with the kernel
  rean demo              walk the stages over a small example
  rean help              print this text

a check target is one of three things:
  foo.ndjson             a lean4export file, read as it is
  Demo.lean              a Lean source file. The real Lean compiles it, then
                         lean4export writes the terms, then our kernel checks
                         them. Stages 2 and 3 are Lean's, stage 4 is ours.
  prelude                Lean's `Init`, the whole prelude
  Some.Module            any compiled module on REAN_LEAN_PATH

options for show:
  --full                 print the whole value, however large

options for run:
  --no-check             run it without checking it first. Say what you mean.
  --steps <n>            how many steps the evaluation may take
  --out <dir>            where the export file goes

options for check and export:
  --decl <name>          export only this declaration and what it rests on.
                         Repeatable. The whole module is the default.
  --out <dir>            where the export file goes, default a temporary dir
  --no-check             export only, as `rean export` does

two knobs, and they are coupled:
  REAN_FUEL=<units>      work budget per declaration. The default reads the
                         size of the file: 20000000000 for a file of up to
                         10000 declarations, and 40000000 above that
  REAN_STACK=<MiB>       stack for the checker, default 512

A larger budget lets a reduction run longer, a longer reduction builds a
deeper term, and a deeper term needs more stack to reduce. The kernel may
use four fifths of the stack and then reports, rather than crashing.

three more, for finding out why a declaration is expensive:
  REAN_TALLY=1           count every rule the kernel fires, by name
  REAN_KERNEL_STACK=<MiB>  the kernel's allowance, held apart from the stack
  REAN_NAT_DEPTH=<levels>  how deep the arithmetic reader forces, default 16

four more, for the front door:
  REAN_LEAN              the `lean` binary to use
  REAN_LEANEXPORT        the `lean4export` binary to use
  REAN_LEAN_PATH         extra directories of compiled `.olean` files
  REAN_EXPORT_DIR        where an export file goes, default a temporary dir
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
    /// A limit stopped the check, so there is **no verdict**.
    ///
    /// This is not a refusal. `OutOfFuel` and `OutOfStack` mean "we did not
    /// check it", and reporting that as a refusal claims a declaration is
    /// wrong when all we know is that we gave up. The arena's own interface
    /// has the same three answers and the same reason for them: exit 0 to
    /// accept, 1 to reject, **2 to decline**, where a decline says "you are
    /// not claiming that the proof is not valid". See the arena chapter of
    /// the guide, and `tools/arena.py`.
    Declined(String),
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
    /// The axioms that this declaration rests on, if any.
    ///
    /// The kernel re-checks everything else, so an axiom is the only thing it
    /// takes on trust. A report that does not name them is not a trust report.
    pub axioms: Vec<String>,
    /// What the kernel did, rule by rule, when `REAN_TALLY` is set.
    ///
    /// Empty otherwise, and empty for a declaration that passed. The tally is
    /// for finding out why one declaration is expensive, and printing it for
    /// all 59,349 would bury the answer.
    pub tally: Vec<(String, u64)>,
    /// The most stack that this declaration needed, in bytes.
    ///
    /// Always measured, because the guard that measures it runs anyway. The
    /// driver prints it beside a tally, where it answers the question the
    /// tally raises: was the limit close? See `REAN_STACK`.
    pub deepest: usize,
}

/// What `check` found.
#[derive(Debug)]
pub struct CheckReport {
    pub meta: String,
    pub outcomes: Vec<DeclOutcome>,
    /// What the kernel did over the **whole run**, when `REAN_TALLY` is set.
    ///
    /// The per-declaration tally in [`DeclOutcome`] is printed for a
    /// declaration that failed, which answers "why is this one expensive" and
    /// not "where does the run spend itself". Reading one as the other is a
    /// mistake chapter 26 made and recorded.
    pub totals: Vec<(String, u64)>,
}

impl CheckReport {
    /// Returns every axiom that any accepted declaration rests on.
    pub fn axioms(&self) -> Vec<String> {
        let mut all: Vec<String> = self
            .outcomes
            .iter()
            .filter(|o| o.verdict == Verdict::Ok)
            .flat_map(|o| o.axioms.iter().cloned())
            .collect();
        all.sort();
        all.dedup();
        all
    }

    /// Returns the trust line that follows the score.
    pub fn trust(&self) -> String {
        let axioms = self.axioms();
        if axioms.is_empty() {
            return "trust: no accepted declaration rests on an axiom".to_string();
        }
        format!("trust: {} axiom(s): {}", axioms.len(), axioms.join(", "))
    }
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

    /// Returns the number that a limit stopped. See [`Verdict::Declined`].
    pub fn declined(&self) -> usize {
        self.count(|v| matches!(v, Verdict::Declined(_)))
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
        let mut parts = Vec::new();
        if self.failed() > 0 {
            parts.push(format!("{} failed", self.failed()));
        }
        if self.declined() > 0 {
            parts.push(format!("{} declined", self.declined()));
        }
        if self.blocked() > 0 {
            parts.push(format!("{} blocked", self.blocked()));
        }
        if !parts.is_empty() {
            line.push_str(&format!(" ({})", parts.join(", ")));
        }
        line
    }
}

/// What `check` and `export` were pointed at.
///
/// The three cases are told apart by the shape of the name, and not by a flag.
/// A reader who types `rean check Demo.lean` means that file, and a reader who
/// types `rean check prelude` means the prelude. Making them say which is which
/// would be a question whose answer is already written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Target {
    /// An export file, read as it is. No Lean is needed.
    Export(PathBuf),
    /// Lean source. The real Lean compiles it, then the exporter reads it.
    Source(PathBuf),
    /// A module that is compiled already, such as `Init`.
    Module(String),
}

impl Target {
    /// Reads what the user typed.
    ///
    /// `prelude` is an alias, because `Init` is the name of the module and not
    /// a word that a reader would guess.
    pub fn parse(target: &str) -> Result<Target, String> {
        if export::is_export_file(target) {
            return Ok(Target::Export(PathBuf::from(target)));
        }
        if export::is_lean_source(target) {
            return Ok(Target::Source(PathBuf::from(target)));
        }
        if target.eq_ignore_ascii_case("prelude") {
            return Ok(Target::Module(export::PRELUDE.to_string()));
        }
        // Anything else is a module name, such as `Init.Data.Nat`.
        //
        // A **path** is not. `./notes.txt` would otherwise pass as a module
        // name, and the reader would get a message about an unknown module
        // prefix, which is true and unhelpful. A separator settles it, and so
        // does a file that is really there: see [`prepare`].
        let looks_like_a_module = !target.is_empty()
            && !target.contains('/')
            && !target.contains('\\')
            && target.split('.').all(|part| {
                !part.is_empty()
                    && part
                        .chars()
                        .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
            });
        if !looks_like_a_module {
            return Err(format!(
                "`{target}` is not a target. Use a `.ndjson` export, a `.lean` \
                 file, `prelude`, or a module name."
            ));
        }
        Ok(Target::Module(target.to_string()))
    }
}

/// What the command line asked `check` or `export` to do.
///
/// The parser lives here and not in `main.rs`, by the rule the driver follows
/// everywhere: every decision belongs where a test can reach it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckArgs {
    pub target: Target,
    /// The declarations to export, or empty for the whole module.
    pub decls: Vec<String>,
    /// Where the export file goes.
    pub out: Option<String>,
    /// Whether to run the kernel afterwards.
    pub check: bool,
}

impl CheckArgs {
    /// Reads the arguments that follow `check` or `export`.
    ///
    /// `checks` is what the command does when no flag says otherwise, so
    /// `export` passes `false` and `check` passes `true`.
    pub fn parse(args: &[String], checks: bool) -> Result<CheckArgs, String> {
        let mut target = None;
        let mut decls = Vec::new();
        let mut out = None;
        let mut check = checks;
        let mut rest = args.iter();
        while let Some(arg) = rest.next() {
            match arg.as_str() {
                "--decl" => {
                    let name = rest
                        .next()
                        .ok_or_else(|| "--decl needs a declaration name".to_string())?;
                    decls.push(name.clone());
                }
                "--out" => {
                    let dir = rest
                        .next()
                        .ok_or_else(|| "--out needs a directory".to_string())?;
                    out = Some(dir.clone());
                }
                "--no-check" => check = false,
                other if other.starts_with("--") => {
                    return Err(format!("unknown option `{other}`"));
                }
                other => {
                    if target.is_some() {
                        return Err(format!(
                            "two targets, `{}` and `{other}`. One at a time.",
                            target.unwrap_or_default()
                        ));
                    }
                    target = Some(other.to_string());
                }
            }
        }
        let target = target.ok_or_else(|| {
            "no target. Give an `.ndjson` export, a `.lean` file, `prelude`, \
             or a module name."
                .to_string()
        })?;
        Ok(CheckArgs {
            target: Target::parse(&target)?,
            decls,
            out,
            check,
        })
    }
}

/// What it took to get an export file for a target.
#[derive(Debug)]
pub struct Prepared {
    /// The export file to check.
    pub path: PathBuf,
    /// What the exporter did, or `None` when the target was a file already.
    pub export: Option<ExportReport>,
}

/// Turns a target into an export file, driving the real Lean when it must.
///
/// This is the front door of `docs/ROADMAP.md` level 1. The reader points
/// `rean` at ordinary Lean code, and our kernel checks the terms that Lean's
/// own elaborator produced. Our parser and our elaborator are **not** in this
/// path. See [`export`].
pub fn prepare(target: &Target, decls: &[String], out: Option<&str>) -> Result<Prepared, String> {
    let work = match out {
        Some(dir) => PathBuf::from(dir),
        None => export::default_work_dir(),
    };
    match target {
        Target::Export(path) => {
            if !path.is_file() {
                return Err(format!("{} is not a file", path.display()));
            }
            if !decls.is_empty() {
                // Slicing an export file is what `tools/slice.py` is for, and
                // saying so beats doing nothing and reporting success.
                return Err(
                    "--decl needs Lean, so it works on a `.lean` file or a module. \
                     To cut an export file down, use tools/slice.py."
                        .to_string(),
                );
            }
            Ok(Prepared {
                path: path.clone(),
                export: None,
            })
        }
        Target::Source(path) => {
            if !path.is_file() {
                return Err(format!("{} is not a file", path.display()));
            }
            let tools = Toolchain::find()?;
            let report = tools.export_source(path, decls, &work)?;
            Ok(Prepared {
                path: report.path.clone(),
                export: Some(report),
            })
        }
        Target::Module(module) => {
            // A name that is really a file on disk is a mistake worth naming.
            // `rean check notes.txt` reads as a module name, and a message
            // about an unknown module prefix would send the reader looking in
            // the wrong place.
            if std::path::Path::new(module).is_file() {
                return Err(format!(
                    "`{module}` is a file, and its name ends in neither \
                     `.ndjson` nor `.lean`. An export file must be `.ndjson`, \
                     and Lean source must be `.lean`."
                ));
            }
            let tools = Toolchain::find()?;
            let report = tools.export_module(module, decls, &[], &work)?;
            Ok(Prepared {
                path: report.path.clone(),
                export: Some(report),
            })
        }
    }
}

/// Reads a `lean4export` file and checks every declaration with our kernel.
///
/// The environment grows one declaration at a time, so a declaration can only
/// use the ones before it. A circular definition cannot slip through.
pub fn check_export(path: &str) -> Result<CheckReport, String> {
    check_export_streaming(path, &mut |_| {})
}

/// Like [`check_export`], and calls `report` as each declaration is decided.
///
/// A file of the whole Lean prelude holds 57,512 declarations. Building the
/// whole report before printing a line of it tells the reader nothing for
/// minutes, and it hid a measurement from us: zero output looked like "stuck on
/// the first declaration" when it only meant "nothing is printed yet".
pub fn check_export_streaming(
    path: &str,
    report: &mut dyn FnMut(&DeclOutcome),
) -> Result<CheckReport, String> {
    let module =
        rean_export::read_module(path).map_err(|err| format!("cannot read {path}: {err}"))?;

    let mut known = Environment::new();
    // A set and not a list. `rejected.contains` runs for every dependency of
    // every declaration, and a list made that a walk of every failure so far.
    let mut rejected: HashSet<rean_core::Name> = HashSet::new();
    let mut outcomes = Vec::new();
    // The axioms that each accepted declaration rests on, built as the file is
    // read. See `axioms_of_group` for why that order is enough.
    let mut rests_on: HashMap<rean_core::Name, Arc<[rean_core::Name]>> = HashMap::new();

    // Walk the file one line at a time. One line can declare a whole mutual
    // group, and the members of a group refer to each other, so the checker
    // must see all of them at once.
    for group in &module.groups {
        let decls: Vec<Declaration> = group
            .iter()
            .filter_map(|name| module.env.get(name).cloned())
            .collect();

        let mut accepted: Vec<Declaration> = Vec::new();
        for name in group {
            let Some(decl) = module.env.get(name) else {
                let lost = DeclOutcome {
                    name: name.to_string(),
                    kind: "missing",
                    verdict: Verdict::Failed("the reader lost this declaration".to_string()),
                    axioms: Vec::new(),
                    tally: Vec::new(),
                    deepest: 0,
                };
                report(&lost);
                outcomes.push(lost);
                rejected.insert(name.clone());
                continue;
            };

            let mut tally: Vec<(String, u64)> = Vec::new();
            let mut deepest = 0usize;

            // Does it rest on something that already failed?
            let mut uses = Vec::new();
            decl.collect_dependencies(&mut uses);
            let blocker = uses
                .iter()
                .find(|used| rejected.contains(used) && !group.contains(used));

            let verdict = match blocker {
                Some(blocker) => Verdict::Blocked(format!("`{blocker}` did not check")),
                None => {
                    let mut tc = TypeChecker::new(&known);
                    if let Some(fuel) = budget_for(module.order.len()) {
                        tc.set_fuel(fuel);
                    }
                    if let Some(depth) = nat_depth_from_env() {
                        tc.set_nat_depth_limit(depth);
                    }
                    tc.set_stack_budget(kernel_stack_budget(stack_bytes(
                        std::env::var("REAN_STACK").ok().as_deref(),
                    )));
                    // The rendered message, the name of the constant that was
                    // missing if that is what went wrong, and whether a limit
                    // stopped us. The name is kept because a constant can be
                    // missing for two very different reasons, and the next
                    // `match` tells them apart. The limit is kept because it is
                    // the difference between "this is wrong" and "we did not
                    // check it", and only the kernel knows which it was.
                    let outcome = tc.with_group(&decls, |tc| {
                        tc.check_declaration(decl).map_err(|err| {
                            let missing = match &err {
                                rean_kernel::TypeError::UnknownConstant(name) => Some(name.clone()),
                                _ => None,
                            };
                            (err.render(tc.lctx()), missing, err.is_a_limit())
                        })
                    });
                    deepest = tc.deepest();
                    match outcome {
                        Ok(()) => {
                            accepted.push(decl.clone());
                            Verdict::Ok
                        }
                        Err((message, missing, a_limit)) => {
                            // The tally is taken here and not at the end of the
                            // file, because the next declaration clears it.
                            if rean_kernel::tally::on() {
                                tally = rean_kernel::tally::take();
                            }
                            verdict_for_failure(message, missing, a_limit, &rejected)
                        }
                    }
                }
            };
            if !matches!(verdict, Verdict::Ok) {
                rejected.insert(name.clone());
            }
            let outcome = DeclOutcome {
                name: name.to_string(),
                kind: decl.kind_label(),
                verdict,
                axioms: Vec::new(),
                tally,
                deepest,
            };
            report(&outcome);
            outcomes.push(outcome);
        }

        // Only a declaration that checks goes into the environment. A bogus
        // one would prove anything that uses it.
        let group_axioms = axioms_of_group(&accepted, &rests_on);
        for decl in accepted {
            rests_on.insert(decl.name().clone(), Arc::clone(&group_axioms));
            known.add(decl);
        }
    }

    // The trust report asks the environment of accepted declarations only, so
    // a refused axiom is never named as something we rest on.
    for outcome in &mut outcomes {
        if outcome.verdict == Verdict::Ok
            && let Some(axioms) = rests_on.get(&rean_core::Name::from_dotted(&outcome.name))
        {
            outcome.axioms = axioms.iter().map(ToString::to_string).collect();
        }
    }

    Ok(CheckReport {
        meta: module.meta.to_string(),
        outcomes,
        totals: rean_kernel::tally::totals(),
    })
}

/// What one declaration looks like to the kernel.
///
/// This is the command that answers the question a reader of these chapters
/// asks most: **what does Lean actually hand us?** `demo` shows a term that was
/// built by hand. This shows a real one, out of a real export, with the names
/// and universes that Lean gave it.
///
/// It paid for itself the hour it was written. Chapter 24 was stuck on why one
/// signed integer proof costs a billion units of work, and `rean show` on three
/// of its dependencies answered it in a minute.
#[derive(Debug)]
pub struct ShowReport {
    pub name: String,
    pub kind: &'static str,
    /// The universe parameters, as `{u, v}`, or empty.
    pub levels: String,
    pub ty: String,
    /// `None` for an axiom, an inductive type, a constructor or a recursor,
    /// and for a value too large to print. See `nodes`.
    pub value: Option<String>,
    /// How many nodes the value holds, counted as a tree.
    ///
    /// This is the number that says why a value was not printed, and it is the
    /// most interesting number about a generated proof. A `bv_decide` lemma
    /// reaches hundreds of millions.
    pub nodes: u32,
    /// How many bytes of the value were left out, if any.
    pub value_cut: usize,
    /// Every constant that the type and the value name.
    pub uses: Vec<String>,
    /// The axioms that this declaration rests on.
    pub axioms: Vec<String>,
    /// What the kernel says about it, if it was asked.
    pub verdict: Option<String>,
}

/// How much of a value to print before cutting it.
///
/// A proof term of the prelude can be hundreds of kilobytes. A reader wants to
/// see the **shape** of one, so the default is a page of it and the report says
/// how much it cut.
const SHOW_LIMIT: usize = 2_000;

/// How many nodes a value may hold before `show` refuses to print it.
///
/// A term is a **graph** and printing it writes a **tree**, so the two sizes
/// are not the same number. One theorem of `Std` has 13 GB of tree, and asking
/// `pretty` for it asks the allocator for 13 GB.
///
/// `--full` prints it anyway, and that is now bounded too:
/// `Expr::PRETTY_LIMIT` stops every printer in the kernel at a megabyte, so the
/// 13 GB above comes out as a megabyte in half a second. Nobody reads a
/// megabyte of a term, and a message that reports a failure must not ask the
/// allocator for gigabytes while it does so.
const HUGE_TERM: u32 = 200_000;

/// Reads one declaration out of an export and describes it.
///
/// `full` prints the whole value, however large.
pub fn show(path: &str, name: &str, full: bool) -> Result<ShowReport, String> {
    let module =
        rean_export::read_module(path).map_err(|err| format!("cannot read {path}: {err}"))?;
    let wanted = rean_core::Name::from_dotted(name);
    let decl = module.env.get(&wanted).ok_or_else(|| {
        // A name that is nearly right is the common mistake, so name the
        // nearest few rather than only refusing.
        let near = nearest_names(&module.env, name);
        if near.is_empty() {
            format!("{path} holds no declaration called `{name}`")
        } else {
            format!(
                "{path} holds no declaration called `{name}`. Did you mean:\n  {}",
                near.join("\n  ")
            )
        }
    })?;

    let lctx = LocalContext::new();
    let levels = if decl.level_params().is_empty() {
        String::new()
    } else {
        format!(
            "{{{}}}",
            decl.level_params()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let (value, value_cut) = match decl.value() {
        None => (None, 0),
        // **Ask the size before printing.** A `bv_decide` lemma of `Std` has a
        // value whose tree is 13,064,816,779 bytes of text. `Arc` sharing
        // keeps it small in memory and `pretty` does not share anything, so
        // asking for the string is asking for 13 GB. The node count is O(1),
        // because every node caches it.
        Some(term) if !full && term.size_up_to(u32::MAX) > HUGE_TERM => (None, 0),
        Some(term) => {
            let text = lctx.pretty(term);
            if full || text.len() <= SHOW_LIMIT {
                (Some(text), 0)
            } else {
                let cut = text.len() - SHOW_LIMIT;
                // Cut on a character boundary, because a term holds names
                // such as `assemble₄` and half of a `₄` is not text.
                let mut end = SHOW_LIMIT;
                while end > 0 && !text.is_char_boundary(end) {
                    end -= 1;
                }
                (Some(text[..end].to_string()), cut)
            }
        }
    };
    let mut uses = Vec::new();
    decl.collect_dependencies(&mut uses);
    let mut uses: Vec<String> = uses.iter().map(ToString::to_string).collect();
    uses.sort();
    uses.dedup();

    Ok(ShowReport {
        name: decl.name().to_string(),
        kind: decl.kind_label(),
        levels,
        nodes: decl.value().map_or(0, |term| term.size_up_to(u32::MAX)),
        ty: lctx.pretty(decl.ty()),
        value,
        value_cut,
        uses,
        axioms: module
            .env
            .axioms_of(&wanted)
            .iter()
            .map(ToString::to_string)
            .collect(),
        verdict: None,
    })
}

/// Returns up to five names that look like `name`.
///
/// The test is a shared last part, which is what a reader usually remembers.
fn nearest_names(env: &Environment, name: &str) -> Vec<String> {
    let last = name.rsplit('.').next().unwrap_or(name).to_lowercase();
    if last.len() < 3 {
        return Vec::new();
    }
    let mut found: Vec<String> = env
        .names()
        .filter(|known| known.to_string().to_lowercase().contains(&last))
        .map(ToString::to_string)
        .collect();
    found.sort_by_key(String::len);
    found.truncate(5);
    found
}

/// What `run` found out about one declaration.
///
/// Stage 4 decides whether the term is correct and stage 5 decides what it
/// comes to. This holds both answers, in that order, because the order is the
/// point: **we checked it, then we ran it.**
#[derive(Debug)]
pub struct RunReport {
    pub name: String,
    /// The score of the check, or `None` when `--no-check` was given.
    pub checked: Option<String>,
    /// What the kernel refused, if it refused anything this declaration needs.
    pub refused: Vec<String>,
    /// The value, printed.
    pub value: String,
    /// How many steps the evaluation took.
    pub steps: u64,
    /// How deep it recursed.
    pub deepest: u32,
    /// `true` when the declaration was run as a **program**, with a world.
    pub as_program: bool,
    /// What a program came to, for the line that says it ran.
    ///
    /// Empty when the action gave back nothing, which is what `IO Unit` does.
    /// A program that returns a value has it named here, because "it ran" and
    /// "it ran and gave you this" are different reports.
    pub outcome: String,
}

/// Checks a declaration with our kernel, then runs it with our evaluator.
///
/// The check comes first and it is not optional by default. A value that came
/// out of an unchecked term is a value from a program nobody verified, and this
/// project exists to know the difference.
pub fn run_declaration(
    path: &str,
    name: &str,
    check_first: bool,
    steps: Option<u64>,
    report: &mut dyn FnMut(&str),
) -> Result<RunReport, String> {
    let module =
        rean_export::read_module(path).map_err(|err| format!("cannot read {path}: {err}"))?;
    let wanted = rean_core::Name::from_dotted(name);
    if !module.env.contains(&wanted) {
        return Err(format!("{path} holds no declaration called `{name}`"));
    }

    // Stage 4. Only the declarations that check go into the environment the
    // evaluator runs against, so a refused declaration cannot be run by
    // accident.
    let report_score = report;
    let (env, checked, refused) = if check_first {
        let report = check_export(path)?;
        let score = report.score();
        // **Say what the kernel found before running anything.** The program
        // writes to the same standard output, and a reader who sees its output
        // above the verdict cannot tell which came first.
        report_score(&score);
        let mut refused: Vec<String> = report
            .outcomes
            .iter()
            .filter(|outcome| outcome.verdict != Verdict::Ok)
            .map(|outcome| outcome.name.clone())
            .collect();
        refused.sort();
        let mut env = Environment::new();
        let ok: HashSet<String> = report
            .outcomes
            .iter()
            .filter(|outcome| outcome.verdict == Verdict::Ok)
            .map(|outcome| outcome.name.clone())
            .collect();
        for group in &module.groups {
            for member in group {
                if ok.contains(&member.to_string())
                    && let Some(decl) = module.env.get(member)
                {
                    env.add(decl.clone());
                }
            }
        }
        (env, Some(score), refused)
    } else {
        (module.env.clone(), None, Vec::new())
    };

    if !env.contains(&wanted) {
        return Err(format!(
            "`{name}` did not check, so there is nothing to run. \
             `--no-check` runs it anyway."
        ));
    }

    // Stage 5.
    let mut eval = rean_eval::Evaluator::new(&env);
    if let Some(steps) = steps {
        eval.set_steps(steps);
    }
    let before = eval.steps_left();
    // An `IO` action is a function of the state of the world, so running one
    // means handing it that state. Anything else is a value and is simply
    // evaluated. The type decides which, and the type is the one thing this
    // evaluator does not read, so the **name** of the head of the type does:
    // a declaration whose type starts with `IO` is a program.
    let is_program = module
        .env
        .get(&wanted)
        .map(|decl| {
            let (head, _) = decl.ty().unfold_apps();
            matches!(head, Expr::Const { name, .. } if name.to_string().starts_with("IO")
                || name.to_string().starts_with("EIO")
                || name.to_string().starts_with("BaseIO"))
        })
        .unwrap_or(false);
    let value = if is_program {
        eval.run_main(&wanted)
    } else {
        eval.run(&wanted)
    }
    .map_err(|err| format!("`{name}` did not run: {err}"))?;
    Ok(RunReport {
        name: wanted.to_string(),
        checked,
        refused,
        // The printer forces what it meets, because a result that reads
        // `List.cons _ _ _` is true and useless.
        value: eval
            .show_deep(&value, 6)
            .unwrap_or_else(|_| format!("{}", rean_eval::Shown(&value, 6))),
        steps: before - eval.steps_left(),
        deepest: eval.deepest(),
        as_program: is_program,
        outcome: outcome_of(&value, &mut eval),
    })
}

/// Describes what an `IO` action gave back, for the report.
///
/// An action that worked is `EStateM.Result.ok a world`, and for an `IO Unit`
/// the `a` is `Unit.unit`, which is worth no words. Anything else is worth
/// naming, and an `error` is worth naming loudly.
fn outcome_of(value: &rean_eval::Value, eval: &mut rean_eval::Evaluator<'_>) -> String {
    let rean_eval::Value::Ctor { name, args } = value else {
        return String::new();
    };
    let shape = name.to_string();
    if shape.ends_with("Result.error") {
        return ", and **failed**".to_string();
    }
    if !shape.ends_with("Result.ok") || args.len() < 2 {
        return String::new();
    }
    // The fields are the last two: the value, and the world.
    match eval.force_thunk(&args[args.len() - 2]) {
        Ok(rean_eval::Value::Ctor { name, .. }) if name.to_string() == "Unit.unit" => String::new(),
        Ok(inner) => format!(", and gave {}", rean_eval::Shown(&inner, 4)),
        Err(_) => String::new(),
    }
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

/// The stack the checker runs on by default, in bytes.
///
/// The kernel walks a term by recursion, so the depth of the Rust stack follows
/// the depth of the term. The 8 MB that a main thread gets is not enough for
/// the Lean prelude, and the checker aborted with a stack overflow before it
/// ran on a thread of its own. `rustc` solves the same problem the same way.
pub const DEFAULT_STACK_MIB: usize = 512;

/// Turns the value of `REAN_STACK` into a stack size in bytes.
///
/// The stack and the work budget are **coupled**, and that is worth knowing
/// before a sweep. A larger `REAN_FUEL` lets a reduction run longer, a longer
/// reduction builds a deeper term, and a deeper term needs more stack.
///
/// 512 MB carries the whole prelude at the default budget and at five times it.
/// At a **thousand** times it, the checker overflowed that stack after 4,034
/// declarations, which is why this is a knob and not a constant.
///
/// A value that does not parse gives the default. A sweep must not stop on a
/// typo in a variable, and it must not silently use a number nobody wrote.
pub fn stack_bytes(setting: Option<&str>) -> usize {
    let mib = match setting.map(str::trim).map(str::parse::<usize>) {
        Some(Ok(mib)) if mib > 0 => mib,
        _ => DEFAULT_STACK_MIB,
    };
    mib * 1024 * 1024
}

/// Returns the axioms that a whole mutual group rests on.
///
/// [`Environment::axioms_of`] answers the same question for one declaration by
/// walking its entire transitive closure. That is the right definition and the
/// wrong algorithm to call 48,804 times: it re-walks the term of every
/// declaration it meets, once per caller, and on the Lean prelude the **report**
/// then cost more than the check. A profile of the run that would not finish
/// showed `Expr::collect_constants` all the way down.
///
/// The export is **topologically ordered**, so every dependency outside this
/// group is already answered. The answer here is therefore the union of those
/// answers, plus any member of this group that is itself an axiom. That is one
/// pass over the file rather than one pass per declaration.
///
/// A whole group shares one answer, and that is correct rather than a
/// shortcut: the members of a mutual group refer to each other, so they rest on
/// exactly the same things.
///
/// A dependency that is absent contributes nothing, which matches
/// [`Environment::axioms_of`]: a declaration the kernel refused never entered
/// the environment, so nothing may be said to rest on it.
fn axioms_of_group(
    group: &[Declaration],
    rests_on: &HashMap<rean_core::Name, Arc<[rean_core::Name]>>,
) -> Arc<[rean_core::Name]> {
    let mut found: HashSet<rean_core::Name> = HashSet::new();
    let mut uses = Vec::new();
    for decl in group {
        if matches!(decl, Declaration::Axiom(_)) {
            found.insert(decl.name().clone());
        }
        uses.clear();
        decl.collect_dependencies(&mut uses);
        for used in &uses {
            if let Some(axioms) = rests_on.get(used) {
                found.extend(axioms.iter().cloned());
            }
        }
    }
    // Sorted by name, as [`Environment::axioms_of`] does, so the report reads
    // the same whichever way it was computed.
    let mut sorted: Vec<rean_core::Name> = found.into_iter().collect();
    sorted.sort_by_key(rean_core::Name::to_string);
    sorted.into()
}

/// Reads a work budget from `REAN_FUEL`, if it is set.
///
/// The default lives in `rean_kernel`. This override exists so that a budget
/// can be chosen by measurement over a real file rather than by taste, and so
/// that a reader can see for themselves what a smaller one gives up.
fn fuel_from_env() -> Option<u64> {
    std::env::var("REAN_FUEL").ok()?.parse().ok()
}

/// How many declarations make a file a **batch** rather than a question.
///
/// See [`budget_for`].
const A_BATCH: usize = 10_000;

/// The budget one declaration of a file of `count` declarations may spend.
///
/// A budget exists so that one declaration cannot stall the rest, and a file
/// with one declaration in it **has** no rest. So the two cases are not the
/// same question, and giving them one answer served neither.
///
/// | the file | the budget | why |
/// |---|---|---|
/// | up to [`A_BATCH`] declarations | 20,000,000,000 | nothing is waiting. The clock is the limit, and the reader is holding it. |
/// | more than that | the kernel's own default | a report that arrives is worth more than a declaration that might. |
///
/// The numbers are measured, on the arena's `perf/` set, which is built to be
/// expensive:
///
/// | test | nodes it needs | time |
/// |---|---|---|
/// | `beta-ladder` | under 20 G | 1 s |
/// | `fueled-chain` | under 20 G | 1 s |
/// | `grind-ring-5` | under 20 G | 2 s |
/// | `magma-list-pair-n21` | under 20 G | 14 s |
/// | `proj-lazy-struct` | under 20 G | 25 s |
/// | `magma-list-deep-n36` | **more** | declines at 26 s |
///
/// Seven of those nine are correct declarations that the default budget
/// refused, and every one of them answers in seconds. The same budget over the
/// prelude would spend half an hour on the 72 declarations that cannot be
/// checked at all, which is why the rule reads the size of the file first.
///
/// The threshold is measured too. The largest single-declaration test of the
/// arena carries its whole dependency tree with it, so `grind-ring-5` is 2,275
/// declarations and the arena's own `init-prelude` is 1,824, while the real
/// libraries start at 59,349. Ten thousand sits in that gap with room on both
/// sides.
///
/// `REAN_FUEL` still overrides both.
fn budget_for(count: usize) -> Option<u64> {
    if let Some(asked) = fuel_from_env() {
        return Some(asked);
    }
    (count <= A_BATCH).then_some(20_000_000_000)
}

/// Decides whether a failed check is a **failure** or a **block**.
///
/// A missing constant that we refused is a block, not a failure.
///
/// The dependency test in [`check_export_streaming`] catches a dependency that
/// the term names. It cannot catch one that the **kernel** names:
/// `ctor_when_struct` builds `S.mk` out of the declaration of `S`, to let the ι
/// rule fire on a variable, so a refused constructor is asked for by a term
/// that never mentions it.
///
/// Three declarations of the Lean prelude were reported as failures for that
/// reason, and `tools/roots.py` ranked them beside real ones. A phantom failure
/// sends a reader looking for a cause that is not there, which is the one thing
/// a report must never do.
///
/// A constant that is missing for any **other** reason stays a failure. An
/// export that names something it never declared is a broken export, and
/// calling that "blocked" would hide it.
fn verdict_for_failure(
    message: String,
    missing: Option<rean_core::Name>,
    a_limit: bool,
    rejected: &HashSet<rean_core::Name>,
) -> Verdict {
    match missing {
        Some(name) if rejected.contains(&name) => {
            Verdict::Blocked(format!("`{name}` did not check"))
        }
        // A limit is carried here as a **bit from the kernel** and not read
        // back out of the message. `TypeError::is_a_limit` is the one place
        // that knows which errors mean "we did not check it", and a driver
        // that matched on the words would go stale the first time one of
        // those messages was reworded.
        _ if a_limit => Verdict::Declined(message),
        _ => Verdict::Failed(message),
    }
}

/// Reads how deep the arithmetic reader may force, from `REAN_NAT_DEPTH`.
///
/// The third thing to sweep. See `TypeChecker::set_nat_depth_limit`: a shallow
/// limit costs work and a deep one costs stack, and chapter 25 measures both
/// sides of that trade.
fn nat_depth_from_env() -> Option<u32> {
    std::env::var("REAN_NAT_DEPTH").ok()?.parse().ok()
}

/// How much of a stack of `bytes` the kernel may use.
///
/// The kernel's own default is set for the 8 MB that a main thread gets,
/// because a library cannot know its stack. The driver **chooses** the stack,
/// so it can do better, and this is where the two knobs stop being
/// independent: raise `REAN_STACK` and the kernel is allowed to recurse
/// further, with no second knob to learn.
///
/// The margin left over is **absolute and small**, not a fraction, and that is
/// a measurement and not a preference. The guard only acts where it is asked,
/// which is on entry to one of three functions, so the margin has to cover the
/// work between two of those entries and nothing more.
///
/// A fraction was tried first and it refuses real work. The declaration of the
/// prelude that blocks 2,283 others needs between 3.6 and 4.2 GB of stack, and
/// it **passes** on the 4 GB that `REAN_STACK=4096` gives. A fifth held back
/// leaves 3,276 MB, which refuses it, and a reader who gives the checker a 4 GB
/// stack has said what they meant.
pub fn kernel_stack_budget(bytes: usize) -> usize {
    match std::env::var("REAN_KERNEL_STACK")
        .ok()
        .and_then(|value| value.trim().parse::<usize>().ok())
    {
        // A measurement must be able to hold one variable still. This one
        // separates the allowance from the stack, so a sweep can ask "how much
        // does this declaration really need?" without moving both at once.
        // Setting it above the real stack brings the crash back, which is the
        // reader's business and not ours.
        Some(mib) if mib > 0 => mib * 1024 * 1024,
        _ => {
            const MARGIN: usize = 64 * 1024 * 1024;
            bytes.saturating_sub(MARGIN.min(bytes / 8))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rean_core::Name;

    fn rejected_set(names: &[&str]) -> HashSet<Name> {
        names.iter().map(|name| Name::from_dotted(name)).collect()
    }

    #[test]
    fn a_constant_we_refused_is_a_block_and_not_a_failure() {
        let verdict = verdict_for_failure(
            "unknown constant `Splits.mk`".to_string(),
            Some(Name::from_dotted("Splits.mk")),
            false,
            &rejected_set(&["Splits.mk"]),
        );
        assert_eq!(
            verdict,
            Verdict::Blocked("`Splits.mk` did not check".to_string())
        );
    }

    #[test]
    fn a_constant_that_nobody_declared_stays_a_failure() {
        // An export that names something it never declared is broken, and
        // calling that "blocked" would hide it.
        let verdict = verdict_for_failure(
            "unknown constant `Nowhere.at_all`".to_string(),
            Some(Name::from_dotted("Nowhere.at_all")),
            false,
            &rejected_set(&["Splits.mk"]),
        );
        assert!(matches!(verdict, Verdict::Failed(_)), "{verdict:?}");
    }

    #[test]
    fn any_other_error_stays_a_failure() {
        let verdict = verdict_for_failure(
            "`Nat.le` is not a function".to_string(),
            None,
            false,
            &rejected_set(&["Splits.mk"]),
        );
        assert!(matches!(verdict, Verdict::Failed(_)), "{verdict:?}");
    }

    #[test]
    fn a_limit_is_a_decline_and_not_a_failure() {
        // The arena's own interface draws this line, and so does the kernel:
        // `OutOfFuel` means "we did not check it". Calling that a failure
        // claims a valid proof is invalid, and eleven tests of the arena's
        // `perf/` set are exactly that case.
        let verdict = verdict_for_failure(
            "this declaration needed more than 20000000 units of work".to_string(),
            None,
            true,
            &rejected_set(&["Splits.mk"]),
        );
        assert!(matches!(verdict, Verdict::Declined(_)), "{verdict:?}");
    }

    #[test]
    fn a_question_gets_a_bigger_budget_than_a_batch() {
        // See `budget_for`. The numbers are measured on the arena's `perf/`
        // set, and the threshold on the size of its largest test.
        if std::env::var_os("REAN_FUEL").is_some() {
            return;
        }
        assert_eq!(budget_for(1), Some(20_000_000_000));
        assert_eq!(budget_for(2_275), Some(20_000_000_000));
        // The prelude is a batch, and it keeps the kernel's own default.
        assert_eq!(budget_for(59_349), None);
    }

    #[test]
    fn the_kernel_gets_the_stack_less_a_margin() {
        // The override is not set in a test run, so this is the derived value.
        if std::env::var_os("REAN_KERNEL_STACK").is_some() {
            return;
        }
        let mib = 1024 * 1024;
        // A large stack keeps all but the 64 MiB margin.
        assert_eq!(kernel_stack_budget(4096 * mib), 4032 * mib);
        assert_eq!(kernel_stack_budget(512 * mib), 448 * mib);
        // A small one keeps seven eighths, because 64 MiB of margin out of 8
        // would be most of it.
        assert_eq!(kernel_stack_budget(8 * mib), 7 * mib);
        assert_eq!(kernel_stack_budget(8), 7);
    }

    #[test]
    fn a_target_is_read_from_its_name() {
        assert_eq!(
            Target::parse("full.ndjson").unwrap(),
            Target::Export(PathBuf::from("full.ndjson"))
        );
        assert_eq!(
            Target::parse("Demo.lean").unwrap(),
            Target::Source(PathBuf::from("Demo.lean"))
        );
        // `prelude` is an alias, because `Init` is the name of the module and
        // not a word a reader would guess.
        assert_eq!(
            Target::parse("prelude").unwrap(),
            Target::Module("Init".to_string())
        );
        assert_eq!(
            Target::parse("Init.Data.Nat").unwrap(),
            Target::Module("Init.Data.Nat".to_string())
        );
        // A path is not a module name. `prepare` catches the other half of
        // this: a bare name that is really a file on disk.
        let err = Target::parse("./notes.txt").unwrap_err();
        assert!(err.contains("is not a target"), "{err}");
        assert!(Target::parse("docs/README.md").is_err());
    }

    #[test]
    fn the_options_of_check_are_read_where_a_test_can_see_them() {
        let args: Vec<String> = [
            "Demo.lean",
            "--decl",
            "foo",
            "--decl",
            "bar",
            "--out",
            "/tmp",
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        let parsed = CheckArgs::parse(&args, true).unwrap();
        assert_eq!(parsed.decls, vec!["foo".to_string(), "bar".to_string()]);
        assert_eq!(parsed.out.as_deref(), Some("/tmp"));
        assert!(parsed.check);

        let no_check: Vec<String> = ["prelude".to_string(), "--no-check".to_string()].to_vec();
        assert!(!CheckArgs::parse(&no_check, true).unwrap().check);
        // `export` checks nothing by default.
        assert!(
            !CheckArgs::parse(&["prelude".to_string()], false)
                .unwrap()
                .check
        );
    }

    #[test]
    fn two_targets_are_refused_with_both_names() {
        let args: Vec<String> = ["a.ndjson".to_string(), "b.ndjson".to_string()].to_vec();
        let err = CheckArgs::parse(&args, true).unwrap_err();
        assert!(err.contains("a.ndjson"), "{err}");
        assert!(err.contains("b.ndjson"), "{err}");
    }

    #[test]
    fn an_option_that_wants_a_value_says_so() {
        let err = CheckArgs::parse(&["--decl".to_string()], true).unwrap_err();
        assert!(err.contains("needs a declaration name"), "{err}");
        let err = CheckArgs::parse(&["--out".to_string()], true).unwrap_err();
        assert!(err.contains("needs a directory"), "{err}");
    }
}
