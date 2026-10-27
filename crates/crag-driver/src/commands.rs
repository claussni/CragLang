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

//! Arguments of the commands that both surfaces reach (Specification
//! §20.6). The shell writes `--release` and `--registry=team`, the REPL
//! `release` and `registry: team`; both become the same `Args`.

use std::collections::{BTreeMap, BTreeSet};

/// What a command accepts besides positional arguments.
#[derive(Clone, Copy, Debug, Default)]
pub struct Spec {
    pub switches: &'static [&'static str],
    pub values: &'static [&'static str],
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Args {
    pub positional: Vec<String>,
    pub switches: BTreeSet<String>,
    pub values: BTreeMap<String, String>,
}

impl Args {
    /// From the shell's words.
    pub fn shell(words: &[&str], spec: Spec) -> Result<Args, String> {
        let mut args = Args::default();
        for word in words {
            if let Some(flag) = word.strip_prefix("--") {
                match flag.split_once('=') {
                    Some((name, value)) if spec.values.contains(&name) => {
                        args.values.insert(name.into(), value.into());
                    }
                    None if spec.switches.contains(&flag) => {
                        args.switches.insert(flag.into());
                    }
                    _ => return Err(format!("unknown option `{word}`")),
                }
            } else {
                args.positional.push(word.to_string());
            }
        }
        Ok(args)
    }

    /// From the REPL's text after the command: positional words, bare
    /// switches and `name: value`.
    pub fn repl(text: &str, spec: Spec) -> Result<Args, String> {
        let mut args = Args::default();
        let mut words = text.split_whitespace().peekable();
        while let Some(word) = words.next() {
            if let Some(name) = word.strip_suffix(':') {
                if !spec.values.contains(&name) {
                    return Err(format!("unknown argument `{name}:`"));
                }
                let value = words.next().ok_or(format!("`{name}:` needs a value"))?;
                args.values.insert(name.into(), value.into());
            } else if spec.switches.contains(&word) {
                args.switches.insert(word.into());
            } else {
                args.positional.push(word.to_string());
            }
        }
        Ok(args)
    }

    pub fn switch(&self, name: &str) -> bool {
        self.switches.contains(name)
    }

    pub fn value(&self, name: &str) -> Option<&str> {
        self.values.get(name).map(String::as_str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPEC: Spec = Spec {
        switches: &["json", "lib"],
        values: &["version"],
    };

    #[test]
    fn both_surfaces_give_the_same_arguments() {
        let shell = Args::shell(&["geo", "--version=2.0", "--json"], SPEC).unwrap();
        let repl = Args::repl("geo version: 2.0 json", SPEC).unwrap();
        assert_eq!(shell, repl);
        assert_eq!(shell.positional, ["geo"]);
        assert_eq!(shell.value("version"), Some("2.0"));
        assert!(shell.switch("json"));
        assert!(Args::shell(&["--force"], SPEC).is_err());
        assert!(Args::repl("color: red", SPEC).is_err());
    }
}
