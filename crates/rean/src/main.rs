//! The command line.
//!
//! This file does the printing and nothing else. Every decision lives in the
//! library, so a test can reach it.

/// The allocator.
///
/// Nearly **half** of a profile of this checker was `malloc` and `free`. The
/// kernel builds a term for every reduction step and drops it on the next one,
/// so the allocator is not a detail of the work: for a while it **was** the
/// work, and chapter 15 found `drop_slow` at the top of the list.
///
/// Measured on the slice that holds the declaration which blocks 2,283 others,
/// at `REAN_FUEL=1600000000 REAN_STACK=4096`, three runs of each. The numbers
/// are **CPU** time, because the machine was loaded and the wall clock said
/// anything between 21 and 50 seconds for the same work.
///
/// | allocator | CPU time |
/// |---|---|
/// | the system allocator | 24.57, 24.37, 24.42 s |
/// | **`mimalloc`** | **19.84, 19.96, 19.92 s** |
///
/// Nineteen per cent, for one line, and the verdicts do not move: 4,143 of
/// 4,144 either way. An allocator cannot change an answer, which is what makes
/// it the one change in this family that needs no argument about soundness.
///
/// It is here, in the driver, rather than in `rean_kernel`. A global allocator
/// is a property of the program, and the kernel is the part you have to trust.
/// Anybody who uses `rean_kernel` as a library picks their own.
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rean::{
    CheckArgs, DeclOutcome, Target, USAGE, Verdict, check_export_streaming, demo, lex_file,
    prepare, prove, run_declaration, show, stack_bytes,
};
use std::process::ExitCode;

fn main() -> ExitCode {
    let child = std::thread::Builder::new()
        .stack_size(stack_bytes(std::env::var("REAN_STACK").ok().as_deref()))
        .spawn(run)
        .expect("the main thread must start");
    match child.join() {
        Ok(code) => code,
        // The child already printed the panic message.
        Err(_) => ExitCode::FAILURE,
    }
}

fn run() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("lex") => match args.get(1) {
            Some(path) => run_lex(path),
            None => fail("lex needs a path"),
        },
        Some("check") => run_target(&args[1..], true),
        Some("export") => run_target(&args[1..], false),
        Some("show") => run_show(&args[1..]),
        Some("run") => run_run(&args[1..]),
        Some("prove") => run_prove(),
        Some("demo") => {
            print!("{}", demo());
            ExitCode::SUCCESS
        }
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

fn run_lex(path: &str) -> ExitCode {
    let report = match lex_file(path) {
        Ok(report) => report,
        Err(message) => return fail(&message),
    };
    for line in &report.lines {
        println!("{line}");
    }
    if report.error_count == 0 {
        println!("\n{} tokens, no error", report.token_count);
        return ExitCode::SUCCESS;
    }
    print!("\n{}", report.diagnostics);
    println!("{} error(s)", report.error_count);
    ExitCode::FAILURE
}

/// Runs `check` or `export`.
///
/// The export step comes first and it prints what it did, because it can take
/// longer than the check and because the path it writes is what a reader needs
/// in order to run the check again without paying for the export twice.
fn run_target(args: &[String], checks: bool) -> ExitCode {
    let args = match CheckArgs::parse(args, checks) {
        Ok(args) => args,
        Err(message) => return fail(&message),
    };
    let ready = match prepare(&args.target, &args.decls, args.out.as_deref()) {
        Ok(ready) => ready,
        // An error here is Lean's message about the reader's own file, or it is
        // the one about a missing exporter. Neither is helped by the usage
        // text, so print it on its own.
        Err(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    };
    if let Some(report) = &ready.export {
        println!("{}", report.line());
    }
    if !args.check {
        println!("{}", ready.path.display());
        return ExitCode::SUCCESS;
    }
    run_check(&ready.path.to_string_lossy())
}

fn run_check(path: &str) -> ExitCode {
    println!("{path}");
    // Print each declaration as it is decided, so a long file shows progress.
    let mut show = |outcome: &DeclOutcome| {
        let (label, message) = match &outcome.verdict {
            Verdict::Ok => ("ok   ", None),
            Verdict::Failed(message) => ("FAIL ", Some(message)),
            Verdict::Blocked(message) => ("block", Some(message)),
        };
        println!("  {label} {:10} {}", outcome.kind, outcome.name);
        if let Some(message) = message {
            for line in message.lines() {
                println!("          {line}");
            }
        }
        // `REAN_TALLY` fills this in, and only for a declaration that failed.
        // The rows name the rule that fired and how often, which is the
        // question a profiler cannot answer. See `rean_kernel::tally`.
        if !outcome.tally.is_empty() {
            println!("          most stack used: {}", bytes_text(outcome.deepest));
            // `REAN_TALLY=all` prints every row. Fourteen is the shape of the
            // problem and the tail is where a cause hides.
            let rows = match std::env::var("REAN_TALLY").as_deref() {
                Ok("all") => outcome.tally.len(),
                _ => 14,
            };
            for (rule, count) in outcome.tally.iter().take(rows) {
                println!("          {count:>12}  {rule}");
            }
        }
    };
    let report = match check_export_streaming(path, &mut show) {
        Ok(report) => report,
        Err(message) => return fail(&message),
    };
    if !report.totals.is_empty() {
        println!("\n  over the whole run:");
        for (what, count) in &report.totals {
            println!("  {count:>12}  {what}");
        }
    }
    println!("\n  {}", report.meta);
    println!("\n{}", report.score());
    println!("{}", report.trust());
    if report.failed() == 0 && report.blocked() == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Prints one declaration as the kernel sees it.
///
/// The target can be a `.lean` file or a module, so this works on the reader's
/// own code and not only on an export they already have.
fn run_show(args: &[String]) -> ExitCode {
    let full = args.iter().any(|arg| arg == "--full");
    let plain: Vec<&String> = args.iter().filter(|arg| !arg.starts_with("--")).collect();
    let (Some(target), Some(name)) = (plain.first(), plain.get(1)) else {
        return fail("show needs a target and a declaration name");
    };
    let target_kind = match Target::parse(target) {
        Ok(kind) => kind,
        Err(message) => return fail(&message),
    };
    // A `.lean` file or a module has to be exported first, and the whole
    // closure of one is 345 MB. So name the declaration to the exporter too:
    // `rean show Demo.lean twice_two` exports 759 KB instead.
    let decls = match &target_kind {
        Target::Export(_) => Vec::new(),
        _ => vec![(*name).clone()],
    };
    let ready = match prepare(&target_kind, &decls, None) {
        Ok(ready) => ready,
        Err(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    };
    let report = match show(&ready.path.to_string_lossy(), name, full) {
        Ok(report) => report,
        Err(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    };
    println!("{} {}{}", report.kind, report.name, report.levels);
    println!("\ntype\n  {}", report.ty.replace('\n', "\n  "));
    match (&report.value, report.value_cut) {
        (None, _) if report.nodes > 0 => println!(
            "\nvalue\n  {} nodes, counted as a tree, and not printed. \
             `--full` prints the first megabyte of it.",
            report.nodes
        ),
        (None, _) => println!("\nvalue\n  none. A {} has no value.", report.kind),
        (Some(value), 0) => println!("\nvalue\n  {}", value.replace('\n', "\n  ")),
        (Some(value), cut) => {
            println!("\nvalue\n  {}", value.replace('\n', "\n  "));
            println!(
                "  ... and {cut} more bytes. `--full` prints up to a megabyte \
                 of it, which is the bound that `Expr::PRETTY_LIMIT` sets for \
                 every printer in the kernel."
            );
        }
    }
    if report.nodes > 0 {
        println!("\n{} nodes in the value, counted as a tree", report.nodes);
    }
    println!("rests on {} constant(s)", report.uses.len());
    if report.axioms.is_empty() {
        println!("trust: no axiom");
    } else {
        println!("trust: {}", report.axioms.join(", "));
    }
    ExitCode::SUCCESS
}

/// Checks one declaration and then runs it.
///
/// Both stages print, in order, because the order is the whole claim: our
/// kernel said yes, and then our evaluator said what it comes to.
fn run_run(args: &[String]) -> ExitCode {
    let check_first = !args.iter().any(|arg| arg == "--no-check");
    let steps = args
        .iter()
        .position(|arg| arg == "--steps")
        .and_then(|at| args.get(at + 1))
        .and_then(|value| value.parse::<u64>().ok());
    let out = args
        .iter()
        .position(|arg| arg == "--out")
        .and_then(|at| args.get(at + 1));
    // An option that takes a value hides that value from the plain arguments,
    // or `--steps 2000` reads as a target called `2000`.
    let plain: Vec<&String> = args
        .iter()
        .enumerate()
        .filter(|(index, arg)| {
            !arg.starts_with("--")
                && !matches!(
                    args.get(index.wrapping_sub(1)).map(String::as_str),
                    Some("--steps" | "--out")
                )
        })
        .map(|(_, arg)| arg)
        .collect();
    let (Some(target), Some(name)) = (plain.first(), plain.get(1)) else {
        return fail("run needs a target and a declaration name");
    };
    let target_kind = match Target::parse(target) {
        Ok(kind) => kind,
        Err(message) => return fail(&message),
    };
    // The closure of one declaration, and not of the whole module. A program
    // that imports the prelude pulls 345 MB in otherwise.
    //
    // One more name comes with it, and it is the **runtime's** rather than the
    // program's. `rean_eval` reads a `Char` by asking `Char.toNat`, because the
    // representation of a `Char` changes between Lean versions and the function
    // that reads it does not. A program that prints a number never mentions
    // `Char.toNat`, and printing one needs it.
    //
    // `String.toList` is **not** asked for, and that is measured. It reads a
    // string the program built as a byte array, which is the other half of the
    // same idea, and asking for it took this program's export from 4.6 MB to
    // **16.9 MB** and brought in the UTF-8 decoding family that chapters 16 and
    // 17 are about: ten declarations our kernel cannot check at the default
    // budget. So the runtime asks for it only if the program did, which
    // `Evaluator::ask` handles by looking before it leaps.
    let decls = match &target_kind {
        Target::Export(_) => Vec::new(),
        _ => vec![(*name).clone(), "Char.toNat".to_string()],
    };
    let ready = match prepare(&target_kind, &decls, out.map(String::as_str)) {
        Ok(ready) => ready,
        Err(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    };
    if let Some(report) = &ready.export {
        println!("{}", report.line());
    }
    // The check prints as it finishes, through this, so that the verdict is
    // above the program's own output rather than below it.
    let mut say = |score: &str| println!("{score}");
    let report = match run_declaration(
        &ready.path.to_string_lossy(),
        name,
        check_first,
        steps,
        &mut say,
    ) {
        Ok(report) => report,
        Err(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    };
    if report.checked.is_none() {
        println!("level 1: not checked, because `--no-check` was given");
    }
    if !report.refused.is_empty() {
        println!(
            "         {} declaration(s) did not check and were left out",
            report.refused.len()
        );
    }
    if report.as_program {
        // The program has written whatever it writes by now. What is left is
        // the result of the action, which for an `IO Unit` carries nothing, so
        // the line says that it ran rather than printing the plumbing.
        println!("\n{} ran{}", report.name, report.outcome);
    } else {
        println!("\n{} = {}", report.name, report.value);
    }
    println!("{} steps, {} levels deep", report.steps, report.deepest);
    ExitCode::SUCCESS
}

/// Prints a byte count in the unit that suits it.
///
/// A small declaration uses kilobytes of stack and a deep one uses hundreds of
/// megabytes, and "0 MiB" says nothing about the first.
fn bytes_text(bytes: usize) -> String {
    if bytes >= 1024 * 1024 {
        format!("{} MiB", bytes / (1024 * 1024))
    } else {
        format!("{} KiB", bytes / 1024)
    }
}

fn run_prove() -> ExitCode {
    let report = prove();
    println!("== the proof ==\n{}", report.proof);
    println!("\n== the proposition ==\n{}", report.proposition);
    println!(
        "\n== infer_type ==\nthe proof has type : {}",
        report.inferred
    );
    println!("\n== check ==");
    match &report.rejected {
        None => println!("accepted. The proposition holds."),
        Some(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    }
    println!("the proposition lives in : {}", report.lives_in);
    println!("\n== a proof that does not check ==");
    println!(
        "rejected:\n  {}",
        report.bad_proof_message.replace('\n', "\n  ")
    );
    println!("\n== what still needs chapter 2 ==");
    for line in &report.needs_environment {
        println!("{line}");
    }
    ExitCode::SUCCESS
}
