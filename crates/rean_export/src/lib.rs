//! Reads a `lean4export` NDJSON file into a [`rean_kernel::Environment`].
//!
//! This is chapter 3 of `docs/ROADMAP.md`: the first contact with the ground
//! truth. The real Lean elaborates a module and writes its declarations here.
//! We read them back and check them with our own kernel. If our kernel
//! disagrees with Lean's, one of the two is wrong, and the file says which
//! declaration to look at.
//!
//! # The shape of the file
//!
//! One JSON object per line. The first line is a `meta` object with three
//! version numbers. Every later line defines one object at an index, and it
//! refers to earlier objects by index.
//!
//! ```json
//! {"in":1,"str":{"pre":0,"str":"Nat"}}
//! {"il":1,"succ":0}
//! {"ie":0,"sort":1}
//! ```
//!
//! Four facts come from a real file and not from the format document:
//!
//! - Name index 0 is **implicit**. It is the anonymous name.
//! - Level index 0 is **implicit**. It is `Level::Zero`.
//! - Term index 0 is **not** implicit. The first term line defines it.
//! - A reference always points backwards, so one pass is enough.
//!
//! The format document on the `lean4export` master branch describes a newer
//! format than the fixture. So this reader accepts both spellings where they
//! differ, and it reports the version it read.

mod reader;

pub use reader::{ExportError, Meta, Module, read_module, read_str};
