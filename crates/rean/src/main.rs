//! The command line.
//!
//! This file does the printing and nothing else. Every decision lives in the
//! library, so a test can reach it.

use rean::{DeclOutcome, USAGE, Verdict, check_export_streaming, demo, lex_file, prove};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("lex") => match args.get(1) {
            Some(path) => run_lex(path),
            None => fail("lex needs a path"),
        },
        Some("check") => match args.get(1) {
            Some(path) => run_check(path),
            None => fail("check needs a path to an .ndjson file"),
        },
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
