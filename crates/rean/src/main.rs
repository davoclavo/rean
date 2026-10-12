//! The command line.
//!
//! This file does the printing and nothing else. Every decision lives in the
//! library, so a test can reach it.

use rean::{
    CheckArgs, DeclOutcome, USAGE, Verdict, check_export_streaming, demo, lex_file, prepare, prove,
    stack_bytes,
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
            for (rule, count) in outcome.tally.iter().take(14) {
                println!("          {count:>12}  {rule}");
            }
        }
    };
    let report = match check_export_streaming(path, &mut show) {
        Ok(report) => report,
        Err(message) => return fail(&message),
    };
    println!("\n  {}", report.meta);
    println!("\n{}", report.score());
    println!("{}", report.trust());
    if report.failed() == 0 && report.blocked() == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
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
