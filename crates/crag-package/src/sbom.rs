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

//! The SBOM `sbom.crag` (Specification §14.5.1, §16.7): every package the
//! build uses, with its version and content hash. It is committed with the
//! project; the build verifies the resolved packages against it and
//! refuses on a mismatch until it is regenerated on purpose.
//!
//! ```text
//! // The packages this build uses. `crag sbom regenerate` writes it.
//! package geo 1.2 hash "9f3c…"
//! package billing 1.2 path "../billing"
//! ```
//!
//! A package from a `path:` source is a folder under development, so it is
//! recorded without a hash and not verified.

use crate::resolve::{Origin, Resolution};
use crate::version::Version;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub name: String,
    pub version: Version,
    pub hash: Option<String>,
    pub path: Option<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Sbom {
    /// By name.
    pub entries: Vec<Entry>,
}

const HEADER: &str = "// The packages this build uses. `crag sbom regenerate` writes it.\n";

impl Sbom {
    pub fn of(resolution: &Resolution) -> Sbom {
        let mut entries: Vec<Entry> = resolution
            .packages
            .iter()
            .map(|p| Entry {
                name: p.name.clone(),
                version: p.version,
                hash: match p.origin {
                    Origin::Registry(_) => Some(p.hash.clone()),
                    Origin::Path(_) => None,
                },
                path: match &p.origin {
                    Origin::Path(shown) => Some(shown.trim_start_matches("path:").to_string()),
                    Origin::Registry(_) => None,
                },
            })
            .collect();
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        Sbom { entries }
    }

    pub fn write(&self) -> String {
        let mut out = HEADER.to_string();
        for e in &self.entries {
            out.push_str(&format!("package {} {}", e.name, e.version));
            if let Some(hash) = &e.hash {
                out.push_str(&format!(" hash \"{hash}\""));
            }
            if let Some(path) = &e.path {
                out.push_str(&format!(" path \"{path}\""));
            }
            out.push('\n');
        }
        out
    }

    pub fn parse(text: &str) -> Result<Sbom, String> {
        let mut entries = Vec::new();
        for (i, line) in text.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with("//") {
                continue;
            }
            let bad = || format!("sbom.crag:{}: cannot read `{line}`", i + 1);
            let words: Vec<&str> = line.split_whitespace().collect();
            let ["package", name, version, rest @ ..] = &words[..] else {
                return Err(bad());
            };
            let mut entry = Entry {
                name: name.to_string(),
                version: Version::parse(version).map_err(|_| bad())?,
                hash: None,
                path: None,
            };
            let quoted = |w: &str| {
                w.strip_prefix('"')
                    .and_then(|w| w.strip_suffix('"'))
                    .map(str::to_string)
            };
            match rest {
                ["hash", h] => entry.hash = Some(quoted(h).ok_or_else(bad)?),
                ["path", p] => entry.path = Some(quoted(p).ok_or_else(bad)?),
                _ => return Err(bad()),
            }
            entries.push(entry);
        }
        Ok(Sbom { entries })
    }

    /// What changes from `self` to `new`, one line each: `+` for a package
    /// added, `-` for one removed, `~` for another version or content.
    pub fn diff(&self, new: &Sbom) -> Vec<String> {
        let mut lines = Vec::new();
        for old in &self.entries {
            match new.entries.iter().find(|e| e.name == old.name) {
                None => lines.push(format!("- {} {}", old.name, old.version)),
                Some(e) if e.version.to_string() != old.version.to_string() => {
                    lines.push(format!("~ {} {} -> {}", old.name, old.version, e.version))
                }
                Some(e) if e.hash != old.hash || e.path != old.path => {
                    lines.push(format!("~ {} {}: other content", old.name, old.version))
                }
                Some(_) => {}
            }
        }
        for e in &new.entries {
            if !self.entries.iter().any(|o| o.name == e.name) {
                lines.push(format!("+ {} {}", e.name, e.version));
            }
        }
        lines
    }
}
