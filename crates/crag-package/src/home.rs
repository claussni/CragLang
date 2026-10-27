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

//! The user's settings that concern packages (Specification §20.8.3): the
//! registries, by name, in `registries.crag` in the settings directory.
//!
//! ```text
//! registry team "/srv/crag"
//! registry local "registry"
//! ```
//!
//! A relative path is relative to the settings directory. The first
//! registry is the default one to publish to.

use std::fs;
use std::path::{Path, PathBuf};

use crag_syntax::{TokenKind, lex};

use crate::registry::Registry;

/// The directory of settings and caches: `CRAG_HOME`, else the place the
/// host system's layout gives.
pub fn crag_home() -> Option<PathBuf> {
    if let Some(home) = std::env::var_os("CRAG_HOME").filter(|h| !h.is_empty()) {
        return Some(PathBuf::from(home));
    }
    let home = PathBuf::from(std::env::var_os("HOME")?);
    Some(if cfg!(target_os = "macos") {
        home.join("Library/Application Support/Crag")
    } else {
        home.join(".crag")
    })
}

/// A registry the settings name, which may not have been opened yet.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistryEntry {
    pub name: String,
    pub dir: PathBuf,
}

/// The registries of `registries.crag` in `home`; none when it does not
/// exist.
pub fn registry_entries(home: &Path) -> Result<Vec<RegistryEntry>, String> {
    let file = home.join("registries.crag");
    let text = match fs::read_to_string(&file) {
        Ok(text) => text,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(format!("cannot read {}: {e}", file.display())),
    };
    let tokens = lex(&text);
    let mut entries: Vec<RegistryEntry> = Vec::new();
    for decl in tokens
        .split(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof))
        .filter(|d| !d.is_empty())
    {
        let line = text[..decl[0].start as usize].matches('\n').count() + 1;
        let bad = || {
            format!(
                "{}:{line}: write `registry <name> \"<folder>\"`",
                file.display()
            )
        };
        let [word, name, path] = decl else {
            return Err(bad());
        };
        if word.text(&text) != "registry"
            || name.kind != TokenKind::Ident
            || path.kind != TokenKind::Str
        {
            return Err(bad());
        }
        let name = name.text(&text).to_string();
        let path = crag_hir::literal::string(&[path.text(&text)])
            .map_err(|e| format!("{}:{line}: {e}", file.display()))?;
        let path: String = path
            .into_iter()
            .map(|p| match p {
                crag_hir::literal::Piece::Text(t) => t,
                crag_hir::literal::Piece::Hole(_) => String::new(),
            })
            .collect();
        if entries.iter().any(|e| e.name == name) {
            return Err(format!(
                "{}:{line}: registry `{name}` is named twice",
                file.display()
            ));
        }
        entries.push(RegistryEntry {
            name,
            dir: home.join(path),
        });
    }
    Ok(entries)
}

/// The registries the settings name, opened.
pub fn registries(home: &Path) -> Result<Vec<Registry>, String> {
    registry_entries(home)?
        .iter()
        .map(|e| Registry::open(&e.name, &e.dir))
        .collect()
}
