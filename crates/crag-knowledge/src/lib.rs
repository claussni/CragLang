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

//! The knowledge bundle (Implementation Plan §11.12.3): the primer, the
//! design principles and the specification, shipped inside the toolchain
//! so an agent reads the language as built and nothing drifts. The spec is
//! the working draft exported into Markdown; `sections` splits it at its
//! headings, and a section's text runs to the next heading of the same or
//! a shallower depth, so a chapter holds its sections.

use std::sync::OnceLock;

const PRIMER: &str = include_str!("../knowledge/primer.md");
const PRINCIPLES: &str = include_str!("../knowledge/principles.md");
const SPEC: &str = include_str!("../knowledge/spec.md");

/// Where Crag differs from the languages agents are trained on.
pub fn primer() -> &'static str {
    PRIMER
}

/// The design principles of §1.1 with their rationale.
pub fn principles() -> &'static str {
    PRINCIPLES
}

/// How a fresh project points agents at the toolchain: the AGENTS.md
/// that `crag package new` writes (Specification §20.10).
pub fn agents_md() -> &'static str {
    include_str!("../knowledge/agents.md")
}

/// The prompt `crag-principles`: how to write Crag like Crag.
pub fn prompt_principles() -> &'static str {
    include_str!("../knowledge/prompt-principles.md")
}

/// The prompt `crag-write-module`, with `{module}` to fill in.
pub fn prompt_write_module() -> &'static str {
    include_str!("../knowledge/prompt-write-module.md")
}

/// The prompt `crag-fix-diagnostics`, with `{target}` to fill in.
pub fn prompt_fix_diagnostics() -> &'static str {
    include_str!("../knowledge/prompt-fix-diagnostics.md")
}

/// One section of the specification.
#[derive(Debug)]
pub struct Section {
    /// `9.3`, or an appendix letter such as `D`.
    pub key: &'static str,
    pub title: &'static str,
    /// The heading and everything under it, subsections included.
    pub text: &'static str,
}

impl Section {
    /// How deep the section is: a chapter or an appendix is 1.
    fn depth(&self) -> usize {
        self.key.split('.').count()
    }
}

/// Every section of the specification, in document order.
pub fn sections() -> &'static [Section] {
    static SECTIONS: OnceLock<Vec<Section>> = OnceLock::new();
    SECTIONS.get_or_init(parse)
}

/// The section with the key, as `§` references and `crag://spec/<key>`
/// name it.
pub fn section(key: &str) -> Option<&'static Section> {
    sections().iter().find(|s| s.key == key)
}

/// The chapters and appendices, for a listing that stays short.
pub fn chapters() -> impl Iterator<Item = &'static Section> {
    sections().iter().filter(|s| s.depth() == 1)
}

/// The keys of every `§` reference in a text: `§9.3` gives `9.3`. A
/// chained reference such as `§20.8.4–20.8.5` gives its first key.
pub fn references(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    for (at, _) in text.match_indices('§') {
        let rest = &text[at + '§'.len_utf8()..];
        let end = rest
            .find(|c: char| !c.is_ascii_alphanumeric() && c != '.')
            .unwrap_or(rest.len());
        let key = rest[..end].trim_end_matches('.');
        if !key.is_empty() {
            out.push(key);
        }
    }
    out
}

/// A `§` reference that resolves to no section of the specification.
pub fn broken_references(text: &str) -> Vec<&str> {
    references(text)
        .into_iter()
        .filter(|key| section(key).is_none())
        .collect()
}

/// Splits the spec at its headings. A heading names a section when what
/// follows the `#`s starts with a dotted number (`### 9.3 Access
/// functions`) or `Appendix` and a letter (`## Appendix D Grammar`).
fn parse() -> Vec<Section> {
    struct Start {
        key: &'static str,
        title: &'static str,
        at: usize,
    }
    let mut starts: Vec<Start> = Vec::new();
    let mut at = 0;
    for line in SPEC.split_inclusive('\n') {
        let heading = line.trim_start_matches('#');
        if line.len() - heading.len() >= 2
            && let Some(rest) = heading.strip_prefix(' ')
        {
            let rest = rest.strip_prefix("Appendix ").unwrap_or(rest);
            let (key, title) = rest.split_once(' ').unwrap_or((rest.trim_end(), ""));
            if !key.is_empty()
                && key
                    .chars()
                    .all(|c| c.is_ascii_digit() || c == '.' || c.is_ascii_uppercase())
            {
                starts.push(Start {
                    key,
                    title: title.trim(),
                    at,
                });
            }
        }
        at += line.len();
    }
    let depth = |key: &str| key.split('.').count();
    (0..starts.len())
        .map(|i| {
            let end = starts[i + 1..]
                .iter()
                .find(|s| depth(s.key) <= depth(starts[i].key))
                .map_or(SPEC.len(), |s| s.at);
            Section {
                key: starts[i].key,
                title: starts[i].title,
                text: SPEC[starts[i].at..end].trim_end(),
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sections_split_at_headings() {
        let errors = section("8.2").unwrap();
        assert_eq!(errors.title, "Handling results with `case` and `pass`");
        assert!(errors.text.contains("no `?` propagation operator"));
        // A chapter holds its sections, up to the next chapter.
        let chapter = section("8").unwrap();
        assert!(chapter.text.contains("### 8.5 Prefixes"));
        assert!(!chapter.text.contains("## 9 Shared state"));
        let grammar = section("D").unwrap();
        assert_eq!(grammar.title, "Grammar");
        assert!(chapters().count() > 20);
        assert!(section("99").is_none());
    }

    #[test]
    fn references_are_found_and_checked() {
        assert_eq!(references("as §9.3 and §8.2 say."), ["9.3", "8.2"]);
        assert_eq!(references("the grammar (§D)"), ["D"]);
        assert_eq!(references("§20.8.4–20.8.5"), ["20.8.4"]);
        assert_eq!(broken_references("§9.3 and §99.9"), ["99.9"]);
    }

    #[test]
    fn the_primer_and_the_principles_link_the_spec() {
        for text in [
            primer(),
            principles(),
            agents_md(),
            prompt_principles(),
            prompt_write_module(),
            prompt_fix_diagnostics(),
        ] {
            assert_eq!(broken_references(text), Vec::<&str>::new());
        }
        // Every primer entry carries its spec link.
        for entry in primer().split("\n## ").skip(1) {
            assert!(entry.contains('§'), "an entry of the primer has no link");
        }
        assert!(references(primer()).len() >= 10);
    }
}
