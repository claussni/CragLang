// This file is part of Crag.
//
// Copyright (C) 2026 Ralf Claussnitzer
//
// Crag is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// Crag is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// Crag. If not, see <https://www.gnu.org/licenses/>.

//! `crag fmt` (Specification §20.6, §20.9): formats files in place.
//!
//! `crag fmt` and `crag fmt all` format every module of the project in the
//! current directory, `crag fmt <file>…` the files named, and `crag fmt -`
//! standard input to standard output. With `--check` nothing is written;
//! the files that would change are listed.

use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use crag_fmt::FormatError;

use crate::diagnostics::render_at;

/// The name of the package at `root`, from its manifest.
fn package_name(root: &Path) -> Option<String> {
    let text = std::fs::read_to_string(root.join("package.crag")).ok()?;
    text.lines().find_map(|line| {
        let mut words = line.split_whitespace();
        (words.next() == Some("package")).then(|| words.next().map(str::to_string))?
    })
}

/// Runs `crag fmt` with its arguments; the exit status.
pub fn crag_fmt(root: &Path, args: &[&str], out: &mut dyn Write) -> u8 {
    let check = args.contains(&"--check");
    let args: Vec<&str> = args.iter().copied().filter(|a| *a != "--check").collect();
    let package = package_name(root);
    let package = package.as_deref();
    if args == ["-"] {
        let mut text = String::new();
        if let Err(e) = std::io::stdin().read_to_string(&mut text) {
            let _ = writeln!(out, "error: cannot read standard input: {e}");
            return 1;
        }
        return match crag_fmt::format(&text, package) {
            Ok(formatted) if check => u8::from(formatted != text),
            Ok(formatted) => {
                let _ = std::io::stdout().write_all(formatted.as_bytes());
                0
            }
            Err(e) => {
                report(&e, "<stdin>", &text, out);
                1
            }
        };
    }
    let files: Vec<PathBuf> = if args.is_empty() || args == ["all"] {
        if !root.join("package.crag").exists() {
            let _ = writeln!(out, "error: no package.crag here; name the files to format");
            return 2;
        }
        match crag_package::content::module_files(root) {
            Ok(paths) => paths.into_iter().map(|p| root.join(p)).collect(),
            Err(e) => {
                let _ = writeln!(out, "error: cannot read {}: {e}", root.display());
                return 1;
            }
        }
    } else {
        args.iter().map(PathBuf::from).collect()
    };
    let mut status = 0;
    for path in files {
        let shown = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .display()
            .to_string();
        let text = match std::fs::read_to_string(&path) {
            Ok(text) => text,
            Err(e) => {
                let _ = writeln!(out, "error: cannot read {shown}: {e}");
                status = 1;
                continue;
            }
        };
        match crag_fmt::format(&text, package) {
            Ok(formatted) if formatted == text => {}
            Ok(_) if check => {
                let _ = writeln!(out, "{shown}: not formatted");
                status = 1;
            }
            Ok(formatted) => {
                if let Err(e) = std::fs::write(&path, formatted) {
                    let _ = writeln!(out, "error: cannot write {shown}: {e}");
                    status = 1;
                }
            }
            Err(e) => {
                report(&e, &shown, &text, out);
                status = 1;
            }
        }
    }
    status
}

fn report(error: &FormatError, file: &str, text: &str, out: &mut dyn Write) {
    match error {
        FormatError::Syntax(errors) => {
            for e in errors {
                let _ = write!(
                    out,
                    "{}",
                    render_at("error", &e.message, file, text, e.range.clone())
                );
            }
            let _ = writeln!(out, "{file}: not formatted, since it does not parse");
        }
        FormatError::Changed => {
            let _ = writeln!(
                out,
                "{file}: not formatted: the layout would change what it means, a bug in the formatter"
            );
        }
    }
}
