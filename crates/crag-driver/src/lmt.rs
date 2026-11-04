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

//! `crag lmt` (Specification §18.7): the limits of code transport.
//! `crag lmt new <document>` draws a salt for a budget document and
//! writes each budget's token file.
//!
//! Next to the document `name.json` it writes the salt to `name.salt`
//! and each budget's token file to `name-<budget>.token`, readable by
//! their owner alone. A receiver's budget directory holds the document and
//! its salt, a sender's the token files of the budgets it sends under. A
//! salt that exists already is kept from being overwritten, since a new
//! one changes every token.

use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};

use crag_budget::Document;
use crag_budget::document::{KEY, hex};

/// Writes the salt and the token files of the document at `path`, telling
/// `out` what it wrote; the exit status.
pub fn crag_lmt_new(path: &Path, out: &mut dyn Write) -> u8 {
    match write_tokens(path) {
        Ok(written) => {
            for file in written {
                let _ = writeln!(out, "wrote {}", file.display());
            }
            0
        }
        Err(why) => {
            let _ = writeln!(out, "error: {why}");
            1
        }
    }
}

/// The files `crag lmt new` writes for the document at `path`: the salt
/// first, then the token files in the document's order.
pub fn files(path: &Path, document: &Document) -> (PathBuf, Vec<PathBuf>) {
    let dir = path.parent().unwrap_or(Path::new("."));
    let stem = path
        .file_stem()
        .map_or("budgets".into(), |s| s.to_string_lossy());
    let salt = dir.join(format!("{stem}.salt"));
    let tokens = document
        .budgets
        .iter()
        .map(|(name, _)| dir.join(format!("{stem}-{name}.token")))
        .collect();
    (salt, tokens)
}

fn write_tokens(path: &Path) -> Result<Vec<PathBuf>, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let document = Document::parse(&text).map_err(|why| format!("{}: {why}", path.display()))?;
    let (salt_path, token_paths) = files(path, &document);
    let mut salt = [0; KEY];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut salt))
        .map_err(|e| format!("cannot draw a salt: {e}"))?;
    let write = |file: &Path, text: &str, new: bool| -> Result<(), String> {
        let mut options = OpenOptions::new();
        options.write(true).mode(0o600);
        if new {
            options.create_new(true);
        } else {
            options.create(true).truncate(true);
        }
        options
            .open(file)
            .and_then(|mut f| f.write_all(text.as_bytes()))
            .map_err(|e| match e.kind() {
                std::io::ErrorKind::AlreadyExists => format!(
                    "{} exists; remove it to draw a new salt, which changes every token",
                    file.display()
                ),
                _ => format!("cannot write {}: {e}", file.display()),
            })
    };
    write(&salt_path, &(hex(&salt) + "\n"), true)?;
    let mut written = vec![salt_path];
    for ((_, text), file) in document.token_files(&salt).into_iter().zip(token_paths) {
        write(&file, &text, false)?;
        written.push(file);
    }
    Ok(written)
}
