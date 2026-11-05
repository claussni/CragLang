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

//! The registry of diagnostic codes (Implementation Plan §11.12.2). Every
//! diagnostic of the compiler has a code that never changes meaning, and
//! the compiler, the language server, the REPL and the agent server show
//! the same one. Each code has an entry in `diagnostics/`: the rule it
//! enforces, why, a failing example and its fix, and the section of the
//! specification. A retired rule keeps its code with a `retired` note.

use std::fmt;

/// A diagnostic's code: a letter for the severity and four digits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DiagCode(&'static str);

impl DiagCode {
    pub fn as_str(self) -> &'static str {
        self.0
    }

    /// The code written as text, if the registry has it.
    pub fn parse(text: &str) -> Option<DiagCode> {
        let text = text.trim();
        ENTRIES
            .iter()
            .find(|e| e.code.0.eq_ignore_ascii_case(text))
            .map(|e| e.code)
    }

    /// The code's entry.
    pub fn entry(self) -> &'static DiagEntry {
        ENTRIES
            .iter()
            .find(|e| e.code == self)
            .expect("every code has an entry")
    }
}

impl fmt::Display for DiagCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

/// What a code means.
#[derive(Debug)]
pub struct DiagEntry {
    pub code: DiagCode,
    /// The name of the rule, in UpperCamelCase, as the code's constant
    /// spells it in upper case.
    pub name: &'static str,
    pub title: &'static str,
    /// The section of the specification, as `3.2`.
    pub spec: &'static str,
    /// Why the rule no longer holds, for a retired code.
    pub retired: Option<&'static str>,
    pub rule: &'static str,
    pub rationale: &'static str,
    /// A program the rule refuses, and the same program fixed. A line
    /// `// file: <path>` starts another file of the program, and
    /// `// file: <path> hex` one whose bytes are written in hexadecimal.
    pub failing: &'static str,
    pub fixed: &'static str,
}

impl DiagEntry {
    /// The entry as the `crag://diagnostic/<code>` resource serves it.
    pub fn markdown(&self) -> String {
        let mut out = format!("# {}: {}\n\n", self.code, self.title);
        if let Some(note) = self.retired {
            out += &format!("Retired: {note}\n\n");
        }
        out += self.rule;
        out += "\n\n";
        if !self.rationale.is_empty() {
            out += &format!("## Why\n\n{}\n\n", self.rationale);
        }
        if !self.failing.is_empty() {
            out += &format!("## Refused\n\n```crag\n{}```\n\n", self.failing);
            out += &format!("## Fixed\n\n```crag\n{}```\n\n", self.fixed);
        }
        out += &format!("Specification: §{}\n", self.spec);
        out
    }

    /// The files of an example: `main.crag` up to the first line
    /// `// file: <path>`, then each named file, as bytes.
    pub fn files(example: &str) -> Vec<(String, Vec<u8>)> {
        let mut files = vec![("main.crag".to_string(), false, String::new())];
        for line in example.lines() {
            if let Some(path) = line.strip_prefix("// file: ") {
                let (path, hex) = match path.trim().strip_suffix(" hex") {
                    Some(path) => (path, true),
                    None => (path.trim(), false),
                };
                files.push((path.trim().to_string(), hex, String::new()));
                continue;
            }
            let text = &mut files.last_mut().unwrap().2;
            text.push_str(line);
            text.push('\n');
        }
        files.retain(|(path, _, text)| path != "main.crag" || !text.trim().is_empty());
        files
            .into_iter()
            .map(|(path, hex, text)| {
                let bytes = match hex {
                    false => text.into_bytes(),
                    true => {
                        let digits: Vec<u8> =
                            text.bytes().filter(|b| b.is_ascii_hexdigit()).collect();
                        digits
                            .chunks(2)
                            .map(|pair| {
                                let pair = std::str::from_utf8(pair).unwrap();
                                u8::from_str_radix(pair, 16).unwrap_or(0)
                            })
                            .collect()
                    }
                };
                (path, bytes)
            })
            .collect()
    }
}

include!(concat!(env!("OUT_DIR"), "/registry.rs"));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codes_are_found_by_their_text() {
        let first = &ENTRIES[0];
        assert_eq!(DiagCode::parse(first.code.as_str()), Some(first.code));
        assert_eq!(
            DiagCode::parse(&first.code.as_str().to_lowercase()),
            Some(first.code)
        );
        assert_eq!(DiagCode::parse("E9999X"), None);
        assert!(first.code.entry().markdown().contains(first.title));
    }

    #[test]
    fn examples_split_into_files() {
        let files = DiagEntry::files(
            "import demo.a\n// file: a.crag\nimport demo.main\n// file: b.bin hex\nff 00\n",
        );
        assert_eq!(
            files,
            [
                ("main.crag".to_string(), b"import demo.a\n".to_vec()),
                ("a.crag".to_string(), b"import demo.main\n".to_vec()),
                ("b.bin".to_string(), vec![0xff, 0x00]),
            ]
        );
    }
}
