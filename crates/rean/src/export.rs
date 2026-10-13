//! The front door: a `.lean` file goes in, an export file comes out.
//!
//! # What this is, and what it is not
//!
//! `rean check foo.ndjson` needs an export file, and until now a reader had to
//! build `lean4export` and run it by hand. The instructions filled a page of
//! `fixtures/lean4export/PROVENANCE.md`, and that page is the reason nobody
//! pointed the checker at their own code.
//!
//! This module removes that step. It finds the real Lean, compiles one file,
//! runs the exporter, and hands back the path of the result.
//!
//! **It does not make our pipeline read the file.** Lean's own elaborator does
//! stage 2 and stage 3 here, and our kernel does stage 4. That is checkpoint
//! level 1 of `docs/ROADMAP.md`, and level 1 is the whole reason `lean4export`
//! exists: an independent kernel must read the terms that Lean produced, not
//! the terms that our own elaborator would like to produce. Level 2 is the one
//! that needs our parser.
//!
//! # Why the driver owns this
//!
//! No library crate of this workspace reads a file or starts a process. The
//! driver does both, so a test can call every stage directly. See the crate
//! table of the README.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

/// The module that holds the Lean prelude.
///
/// `rean check prelude` is the common case, and `Init` is the name of it.
pub const PRELUDE: &str = "Init";

/// The real Lean, and the exporter that belongs to the same toolchain.
///
/// The two **must** come from one toolchain. An exporter reads the `.olean`
/// files that its own Lean wrote, and the format of those changes between
/// versions, so a mismatched pair fails with a message about a header rather
/// than about a version.
#[derive(Debug, Clone)]
pub struct Toolchain {
    /// The `lean` binary, which compiles a file to a `.olean`.
    pub lean: PathBuf,
    /// The `lean4export` binary, which writes the NDJSON.
    pub exporter: PathBuf,
    /// Where Lean keeps `Init.olean`, for `LEAN_PATH`.
    pub libdir: PathBuf,
    /// What `lean --version` reports, for the record.
    pub version: String,
}

/// The two variables that override the search.
const LEAN_VAR: &str = "REAN_LEAN";
const EXPORTER_VAR: &str = "REAN_LEANEXPORT";

/// The names that the exporter is known by.
///
/// Upstream builds `lean4export`. A toolchain that carries it beside `lean`
/// often shortens the name, so look for both.
const EXPORTER_NAMES: [&str; 2] = ["lean4export", "leanexport"];

impl Toolchain {
    /// Finds a Lean and an exporter that belong together.
    ///
    /// The order is: the two variables, then the directory that holds the
    /// `lean` on `PATH`, then every toolchain that `elan` has installed.
    ///
    /// A directory counts only when it holds **both** binaries, because the
    /// pair must match. The error names the two variables, so a reader with an
    /// exporter somewhere else is never stuck.
    pub fn find() -> Result<Toolchain, String> {
        let lean_override = from_var(LEAN_VAR)?;
        let exporter_override = from_var(EXPORTER_VAR)?;

        let (lean, exporter) = match (lean_override, exporter_override) {
            (Some(lean), Some(exporter)) => (lean, exporter),
            (lean, exporter) => {
                let paired = search_roots()
                    .into_iter()
                    .find_map(|root| pair_in(&root, lean.as_deref(), exporter.as_deref()));
                match paired {
                    Some(pair) => pair,
                    None => return Err(not_found(lean.as_deref(), exporter.as_deref())),
                }
            }
        };

        let version = run_for_line(&lean, &["--version"])?;
        let libdir = PathBuf::from(run_for_line(&lean, &["--print-libdir"])?);
        Ok(Toolchain {
            lean,
            exporter,
            libdir,
            version,
        })
    }

    /// Compiles one `.lean` file and exports it.
    ///
    /// The module name is the stem of the file, so `Demo.lean` becomes the
    /// module `Demo`. A file whose name is not a module name of its own, such
    /// as one module of a package in a subdirectory, needs
    /// [`Toolchain::export_module`] over a built package instead.
    ///
    /// `decls` limits the export to those declarations and what they rest on.
    /// An empty list exports the whole closure of the module, the prelude
    /// included, which is the honest default: an independent checker that
    /// trusts the prelude checks nothing.
    pub fn export_source(
        &self,
        source: &Path,
        decls: &[String],
        work: &Path,
    ) -> Result<ExportReport, String> {
        let module = module_name(source)?;
        // `Path::parent` of a bare file name is the **empty** path, and `lean
        // -R ""` reports "no such file or directory" about a file it does not
        // name. So a bare name means this directory.
        let root = match source.parent() {
            Some(dir) if !dir.as_os_str().is_empty() => dir,
            _ => Path::new("."),
        };
        std::fs::create_dir_all(work)
            .map_err(|err| format!("cannot make the work directory {}: {err}", work.display()))?;

        // Stage 1 to 3, by the real Lean. An error here is the user's file,
        // not our checker, so pass Lean's own message straight through.
        let olean = work.join(format!("{module}.olean"));
        let compile = Command::new(&self.lean)
            .arg("-R")
            .arg(root)
            .arg("-o")
            .arg(&olean)
            .arg(source)
            .output()
            .map_err(|err| format!("cannot run {}: {err}", self.lean.display()))?;
        if !compile.status.success() {
            let text = String::from_utf8_lossy(&compile.stdout);
            let errors = String::from_utf8_lossy(&compile.stderr);
            return Err(format!(
                "lean refused {}:\n{}{}",
                source.display(),
                text.trim_end(),
                errors.trim_end()
            ));
        }

        // The work directory holds the new `.olean`, and `libdir` holds the
        // library. The source directory comes last, for a sibling module that
        // a package build already compiled.
        self.export(
            &module,
            decls,
            &[work.to_path_buf(), root.to_path_buf()],
            work,
        )
    }

    /// Exports a module that is already compiled.
    ///
    /// `Init` is the prelude. A module of a package needs that package's build
    /// directory in `extra_path`, which `REAN_LEAN_PATH` supplies.
    pub fn export_module(
        &self,
        module: &str,
        decls: &[String],
        extra_path: &[PathBuf],
        work: &Path,
    ) -> Result<ExportReport, String> {
        std::fs::create_dir_all(work)
            .map_err(|err| format!("cannot make the work directory {}: {err}", work.display()))?;
        self.export(module, decls, extra_path, work)
    }

    /// Runs the exporter, with `LEAN_PATH` built from `roots` and the library.
    fn export(
        &self,
        module: &str,
        decls: &[String],
        roots: &[PathBuf],
        work: &Path,
    ) -> Result<ExportReport, String> {
        let path = work.join(format!("{module}.ndjson"));
        // **Write somewhere private, then rename.**
        //
        // The name of the file comes from the name of the module, so two runs
        // on one module write the same path. Two of our own tests did that in
        // parallel and the second one read a **truncated** file: 36 KB of
        // export and then "EOF while parsing an object".
        //
        // A rename on one filesystem is atomic, so a reader sees either the old
        // file or the whole new one. Two writers still race for the name, and
        // each of them wins a complete file.
        let partial = work.join(format!("{module}.ndjson.{}", std::process::id()));
        let file = std::fs::File::create(&partial)
            .map_err(|err| format!("cannot write {}: {err}", partial.display()))?;

        // Every entry is made absolute. `lean4export` does not find
        // `Demo.olean` through a search path entry of `.`, and the error it
        // gives names the entries, so the fault is visible and the fix is
        // this.
        let mut search: Vec<PathBuf> = roots
            .iter()
            .map(|root| std::fs::canonicalize(root).unwrap_or_else(|_| root.clone()))
            .collect();
        search.push(self.libdir.clone());
        if let Some(extra) = std::env::var_os("REAN_LEAN_PATH") {
            search.extend(std::env::split_paths(&extra));
        }
        let lean_path = std::env::join_paths(&search)
            .map_err(|err| format!("cannot build LEAN_PATH: {err}"))?;

        let mut command = Command::new(&self.exporter);
        command.env("LEAN_PATH", &lean_path).arg(module);
        // The exporter starts `lean` itself, and it looks for it on `PATH`.
        // Without this the error is "could not execute external process
        // 'lean'", from a reader who has a perfectly good Lean installed and
        // simply not on the path.
        if let Some(dir) = self.lean.parent() {
            let mut path: Vec<PathBuf> = vec![dir.to_path_buf()];
            if let Some(existing) = std::env::var_os("PATH") {
                path.extend(std::env::split_paths(&existing));
            }
            if let Ok(joined) = std::env::join_paths(&path) {
                command.env("PATH", joined);
            }
        }
        // The exporter reads a list of declarations after a bare `--`. Without
        // one it exports the whole transitive closure of the module.
        if !decls.is_empty() {
            command.arg("--").args(decls);
        }

        let started = Instant::now();
        let run = command
            .stdout(file)
            .output()
            .map_err(|err| format!("cannot run {}: {err}", self.exporter.display()))?;
        let seconds = started.elapsed().as_secs_f64();

        // A name that the module does not hold makes the exporter stop part
        // way, and the file it leaves behind has dangling indices. So report
        // the failure and delete the file, rather than let the reader check a
        // truncated export and read our own reader's complaint instead.
        if !run.status.success() {
            let _ = std::fs::remove_file(&partial);
            return Err(format!(
                "{} refused module `{module}`:\n{}",
                self.exporter.display(),
                String::from_utf8_lossy(&run.stderr).trim_end()
            ));
        }

        std::fs::rename(&partial, &path).map_err(|err| {
            format!(
                "cannot put {} in place as {}: {err}",
                partial.display(),
                path.display()
            )
        })?;
        let bytes = std::fs::metadata(&path).map(|meta| meta.len()).unwrap_or(0);
        Ok(ExportReport {
            path,
            module: module.to_string(),
            bytes,
            seconds,
            toolchain: self.version.clone(),
        })
    }
}

/// What the exporter wrote, and what it cost.
#[derive(Debug, Clone)]
pub struct ExportReport {
    /// The NDJSON file. It stays on disk, so a second run can check it again
    /// without paying for the export.
    pub path: PathBuf,
    pub module: String,
    pub bytes: u64,
    pub seconds: f64,
    /// What `lean --version` reported. Pin this next to any measurement.
    pub toolchain: String,
}

impl ExportReport {
    /// Returns the line that `rean check` prints before it starts checking.
    ///
    /// The version is cut down to the number. `lean --version` reports the
    /// target triple, the commit and the build type as well, and the `meta`
    /// line of the export file carries all three for the record. One line of
    /// progress does not need them twice.
    pub fn line(&self) -> String {
        format!(
            "export: {} -> {} ({}) in {:.1}s, by Lean {}",
            self.module,
            self.path.display(),
            size_text(self.bytes),
            self.seconds,
            self.short_version()
        )
    }

    /// Returns the version number out of what `lean --version` printed.
    pub fn short_version(&self) -> String {
        match self.toolchain.split_once("version ") {
            Some((_, rest)) => rest
                .split([',', ' '])
                .next()
                .unwrap_or_default()
                .to_string(),
            // A `lean --version` that nobody here has seen is passed through
            // whole. Cutting at the first space would report "something" for
            // "something else", which is worse than the long line.
            None => self.toolchain.clone(),
        }
    }
}

/// Returns a file size that a reader can take in at a glance.
///
/// A prelude export is 345 MB and a one declaration slice is 40 KB, and
/// "0.0 MB" tells the reader nothing about the second one.
fn size_text(bytes: u64) -> String {
    const KB: f64 = 1024.0;
    const MB: f64 = 1024.0 * 1024.0;
    let bytes = bytes as f64;
    if bytes >= MB {
        format!("{:.1} MB", bytes / MB)
    } else if bytes >= KB {
        format!("{:.0} KB", bytes / KB)
    } else {
        format!("{bytes:.0} bytes")
    }
}

/// Where an export file goes when the caller names no directory.
///
/// A prelude export is 345 MB, so it does not belong beside the user's source.
/// It stays in the temporary directory, and the report prints the path.
///
/// A target that is a `.lean` file or a module is exported **every time**. A
/// cached export is a claim about a source file that may have changed since,
/// and a checker that reports on a file nobody is editing any more is worse
/// than one that takes 14 seconds. The path is printed so that a reader who
/// wants the same terms twice can name the `.ndjson` instead, which needs no
/// Lean at all.
pub fn default_work_dir() -> PathBuf {
    match std::env::var_os("REAN_EXPORT_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => std::env::temp_dir().join("rean-export"),
    }
}

/// Returns `true` when the path names a file that our reader can read as is.
pub fn is_export_file(target: &str) -> bool {
    Path::new(target)
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("ndjson"))
}

/// Returns `true` when the path names Lean source.
pub fn is_lean_source(target: &str) -> bool {
    Path::new(target)
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("lean"))
}

/// Turns a file path into the Lean module name that holds it.
fn module_name(source: &Path) -> Result<String, String> {
    let stem = source
        .file_stem()
        .and_then(|stem| stem.to_str())
        .ok_or_else(|| format!("{} has no module name", source.display()))?;
    // Lean accepts much more than this in a name, and a module name that needs
    // a guillemet is not a name that a file should carry. Refuse it here, where
    // the message can say why, rather than inside the exporter.
    let plain = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    if stem.is_empty() || !stem.chars().all(plain) {
        return Err(format!(
            "`{stem}` is not a plain module name, so `lean` cannot derive one \
             from the file name. Build the package and use `--module` instead."
        ));
    }
    Ok(stem.to_string())
}

/// Reads one of the two override variables.
fn from_var(name: &str) -> Result<Option<PathBuf>, String> {
    from_value(name, std::env::var_os(name))
}

/// The decision behind [`from_var`], with the value passed in.
///
/// The value is a parameter so that a test can reach the decision without
/// setting an environment variable. That is not a style preference. Setting one
/// is `unsafe` in this edition because the whole process shares it, and a test
/// of mine that did it **hung** the test binary: the tests run in parallel, and
/// the others were reading the environment to find a toolchain.
fn from_value(name: &str, value: Option<std::ffi::OsString>) -> Result<Option<PathBuf>, String> {
    let Some(value) = value else {
        return Ok(None);
    };
    let path = PathBuf::from(value);
    if !path.is_file() {
        return Err(format!(
            "{name} names {}, which is not a file",
            path.display()
        ));
    }
    Ok(Some(path))
}

/// The directories to look in, in order.
fn search_roots() -> Vec<PathBuf> {
    let mut roots = Vec::new();
    // The `lean` that the user's shell would run, so a `devbox shell` or an
    // `elan` default is honoured first.
    if let Some(lean) = on_path("lean")
        && let Some(dir) = lean.parent()
    {
        roots.push(dir.to_path_buf());
    }
    for name in EXPORTER_NAMES {
        if let Some(exporter) = on_path(name)
            && let Some(dir) = exporter.parent()
        {
            roots.push(dir.to_path_buf());
        }
    }
    // Then every toolchain that `elan` installed. The newest first, by the
    // time it was written, because a reader who just installed one means that
    // one.
    if let Some(home) = std::env::var_os("HOME") {
        let toolchains = PathBuf::from(home).join(".elan/toolchains");
        if let Ok(entries) = std::fs::read_dir(&toolchains) {
            let mut found: Vec<(std::time::SystemTime, PathBuf)> = entries
                .filter_map(Result::ok)
                .map(|entry| {
                    let when = entry
                        .metadata()
                        .and_then(|meta| meta.modified())
                        .unwrap_or(std::time::UNIX_EPOCH);
                    (when, entry.path().join("bin"))
                })
                .collect();
            found.sort_by(|a, b| b.0.cmp(&a.0));
            roots.extend(found.into_iter().map(|(_, dir)| dir));
        }
    }
    roots
}

/// Returns the pair of binaries in `root`, if both are there.
///
/// An override takes the place of the binary it names, so a reader can supply
/// an exporter they built themselves and still use the toolchain's `lean`.
fn pair_in(
    root: &Path,
    lean: Option<&Path>,
    exporter: Option<&Path>,
) -> Option<(PathBuf, PathBuf)> {
    let lean = match lean {
        Some(given) => given.to_path_buf(),
        None => executable(root, "lean")?,
    };
    let exporter = match exporter {
        Some(given) => given.to_path_buf(),
        None => EXPORTER_NAMES
            .iter()
            .find_map(|name| executable(root, name))?,
    };
    Some((lean, exporter))
}

/// Returns `root/name` when it is a file.
fn executable(root: &Path, name: &str) -> Option<PathBuf> {
    let path = root.join(name);
    path.is_file().then_some(path)
}

/// Looks one name up on `PATH`.
fn on_path(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path).find_map(|dir| executable(&dir, name))
}

/// The message for a reader who has no exporter.
///
/// It names what is missing and the variable that fixes it. The build
/// instructions live in `fixtures/lean4export/PROVENANCE.md`, and this message
/// points there rather than repeating them.
fn not_found(lean: Option<&Path>, exporter: Option<&Path>) -> String {
    let missing = match (lean.is_some(), exporter.is_some()) {
        (true, false) | (false, false) => "lean4export",
        (false, true) => "lean",
        (true, true) => "a matching pair of lean and lean4export",
    };
    format!(
        "cannot find {missing}.\n\
         \n\
         An export needs the real Lean and `lean4export` from the **same**\n\
         toolchain. `rean` looks on PATH and in ~/.elan/toolchains.\n\
         \n\
         Set {LEAN_VAR} and {EXPORTER_VAR} to name them yourself, or see\n\
         fixtures/lean4export/PROVENANCE.md for how to build the exporter.\n\
         \n\
         An `.ndjson` file that somebody else exported needs none of this:\n\
         `rean check fixtures/lean4export/shapes.ndjson` works on its own."
    )
}

/// Runs a binary and returns its first line of output.
fn run_for_line(binary: &Path, args: &[&str]) -> Result<String, String> {
    let out = Command::new(binary)
        .args(args)
        .output()
        .map_err(|err| format!("cannot run {}: {err}", binary.display()))?;
    if !out.status.success() {
        return Err(format!(
            "{} {} failed:\n{}",
            binary.display(),
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim_end()
        ));
    }
    let text = String::from_utf8_lossy(&out.stdout);
    Ok(text.lines().next().unwrap_or("").trim().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_size_reads_in_the_unit_that_suits_it() {
        assert_eq!(size_text(345_690_186), "329.7 MB");
        assert_eq!(size_text(40_960), "40 KB");
        assert_eq!(size_text(12), "12 bytes");
    }

    #[test]
    fn an_ndjson_path_is_an_export_and_a_lean_path_is_source() {
        assert!(is_export_file("full.ndjson"));
        assert!(is_export_file("FULL.NDJSON"));
        assert!(!is_export_file("Demo.lean"));
        assert!(is_lean_source("Demo.lean"));
        assert!(!is_lean_source("Init"));
        // A bare module name is neither, so `check` treats it as a module.
        assert!(!is_export_file("Init"));
    }

    #[test]
    fn the_module_name_is_the_stem_of_the_file() {
        assert_eq!(module_name(Path::new("a/b/Demo.lean")).unwrap(), "Demo");
        assert_eq!(module_name(Path::new("Demo.lean")).unwrap(), "Demo");
    }

    #[test]
    fn a_name_that_lean_cannot_derive_is_refused_here() {
        // A dot in the stem would make `lean` derive a different name than the
        // one we would pass to the exporter, so refuse it with a reason.
        let err = module_name(Path::new("My.Module.lean")).unwrap_err();
        assert!(err.contains("not a plain module name"), "{err}");
        assert!(err.contains("--module"), "{err}");
    }

    #[test]
    fn an_override_that_names_nothing_is_an_error_and_not_a_silent_search() {
        // A reader who sets the variable to a typo must hear about the typo.
        // Falling back to a search would check the wrong Lean and say nothing.
        let err = from_value(LEAN_VAR, Some("/nowhere/at/all/lean".into())).unwrap_err();
        assert!(err.contains("is not a file"), "{err}");
        assert!(err.contains(LEAN_VAR), "{err}");
    }

    #[test]
    fn no_override_is_not_an_error() {
        assert_eq!(from_value(LEAN_VAR, None), Ok(None));
    }

    #[test]
    fn the_error_names_the_variable_that_fixes_it() {
        let message = not_found(Some(Path::new("/bin/lean")), None);
        assert!(message.contains("lean4export"), "{message}");
        assert!(message.contains(EXPORTER_VAR), "{message}");
        assert!(message.contains("shapes.ndjson"), "{message}");
    }

    /// Makes a directory with the files named in it, and returns the path.
    ///
    /// `whose` is the name of the test. The tests run in parallel in one
    /// process, so a directory named after its **contents** is shared by two
    /// tests that want the same contents, and one of them deletes it while the
    /// other is reading. That failed once, as a flake, which is the worst way
    /// to find out.
    fn a_directory_holding(whose: &str, files: &[&str]) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "rean-export-test-{}-{whose}-{}",
            std::process::id(),
            files.join("-")
        ));
        std::fs::create_dir_all(&dir).expect("the directory must be there");
        for file in files {
            std::fs::write(dir.join(file), b"not really a binary").expect("the file must be there");
        }
        dir
    }

    #[test]
    fn a_pair_is_taken_only_from_a_directory_that_holds_both() {
        // The two must match, so one of them alone is not a pair. A directory
        // with only `lean` in it is the common case on a machine where nobody
        // has built the exporter, and taking `lean` from there and the
        // exporter from somewhere else is how a version mismatch happens.
        let lean_only = a_directory_holding("pair", &["lean"]);
        assert_eq!(pair_in(&lean_only, None, None), None);

        let exporter_only = a_directory_holding("pair", &["lean4export"]);
        assert_eq!(pair_in(&exporter_only, None, None), None);

        let both = a_directory_holding("pair", &["lean", "lean4export"]);
        let (lean, exporter) = pair_in(&both, None, None).expect("both are there");
        assert_eq!(lean, both.join("lean"));
        assert_eq!(exporter, both.join("lean4export"));

        // The short name is accepted as well, because a toolchain that carries
        // the exporter beside `lean` often renames it.
        let short = a_directory_holding("pair", &["lean", "leanexport"]);
        let (_, exporter) = pair_in(&short, None, None).expect("both are there");
        assert_eq!(exporter, short.join("leanexport"));

        for dir in [lean_only, exporter_only, both, short] {
            let _ = std::fs::remove_dir_all(dir);
        }
    }

    #[test]
    fn an_override_stands_in_for_the_binary_it_names() {
        // A reader who built the exporter themselves keeps the toolchain's
        // `lean`, so one override must not require the other.
        let lean_only = a_directory_holding("override", &["lean"]);
        let mine = PathBuf::from("/somewhere/of/my/own/lean4export");
        let (lean, exporter) =
            pair_in(&lean_only, None, Some(&mine)).expect("the override completes the pair");
        assert_eq!(lean, lean_only.join("lean"));
        assert_eq!(exporter, mine);
        let _ = std::fs::remove_dir_all(lean_only);
    }

    #[test]
    fn the_message_says_which_of_the_two_is_missing() {
        assert!(not_found(None, None).contains("lean4export"));
        assert!(not_found(Some(Path::new("/bin/lean")), None).contains("lean4export"));
        // An exporter with no Lean beside it.
        let no_lean = not_found(None, Some(Path::new("/bin/lean4export")));
        assert!(no_lean.contains("cannot find lean"), "{no_lean}");
        // Both named and still no pair: the two are in different places.
        let neither = not_found(
            Some(Path::new("/bin/lean")),
            Some(Path::new("/bin/lean4export")),
        );
        assert!(neither.contains("matching pair"), "{neither}");
    }

    #[test]
    fn the_version_is_cut_down_to_the_number() {
        let report = |toolchain: &str| ExportReport {
            path: PathBuf::from("x.ndjson"),
            module: "X".to_string(),
            bytes: 0,
            seconds: 0.0,
            toolchain: toolchain.to_string(),
        };
        assert_eq!(
            report("Lean (version 4.35.0-rc3, arm64-apple-darwin24.6.0, commit abc, Release)")
                .short_version(),
            "4.35.0-rc3"
        );
        // A `lean --version` that this reader has never seen is passed through
        // rather than mangled.
        assert_eq!(report("something else").short_version(), "something else");
    }

    #[test]
    fn the_report_line_names_the_toolchain_because_a_measurement_needs_it() {
        let report = ExportReport {
            path: PathBuf::from("/tmp/Init.ndjson"),
            module: "Init".to_string(),
            bytes: 345_690_186,
            seconds: 16.4,
            toolchain:
                "Lean (version 4.35.0-rc3, arm64-apple-darwin24.6.0, commit 470d5ce, Release)"
                    .to_string(),
        };
        let line = report.line();
        assert!(line.contains("Init"), "{line}");
        assert!(line.contains("329.7 MB"), "{line}");
        assert!(line.contains("Lean 4.35.0-rc3"), "{line}");
        // The triple and the commit stay out of the line. The `meta` line of
        // the export file carries them.
        assert!(!line.contains("arm64"), "{line}");
    }
}
