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

//! The build step of the registry: reads one Markdown file per code from
//! `diagnostics/` and writes the table and a constant per code. It refuses
//! an entry that misses a part, so no code goes without its explanation
//! and its examples (Implementation Plan §11.12.2).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

struct Entry {
    code: String,
    name: String,
    title: String,
    spec: String,
    retired: Option<String>,
    rule: String,
    rationale: String,
    failing: String,
    fixed: String,
}

fn main() {
    let dir = Path::new("diagnostics");
    println!("cargo::rerun-if-changed=diagnostics");
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .expect("the diagnostics directory")
        .map(|e| e.expect("a directory entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "md"))
        .collect();
    files.sort();
    let mut entries = Vec::new();
    let mut problems = Vec::new();
    for path in &files {
        println!("cargo::rerun-if-changed={}", path.display());
        let text = std::fs::read_to_string(path).expect("a readable entry");
        match parse(&text) {
            Ok(entry) => {
                let stem = path.file_stem().unwrap().to_string_lossy();
                if stem != entry.code {
                    problems.push(format!(
                        "{}: the file is named for {stem}, the entry is {}",
                        path.display(),
                        entry.code
                    ));
                }
                entries.push(entry);
            }
            Err(why) => problems.push(format!("{}: {why}", path.display())),
        }
    }
    let mut codes = BTreeMap::new();
    let mut names = BTreeMap::new();
    for e in &entries {
        if let Some(old) = codes.insert(e.code.clone(), e.name.clone()) {
            problems.push(format!("{} is both {old} and {}", e.code, e.name));
        }
        if let Some(old) = names.insert(e.name.clone(), e.code.clone()) {
            problems.push(format!("{} names both {old} and {}", e.name, e.code));
        }
    }
    if !problems.is_empty() {
        panic!(
            "the diagnostic registry is incomplete:\n  {}",
            problems.join("\n  ")
        );
    }
    let mut out = String::new();
    for e in &entries {
        let _ = writeln!(out, "/// {}: {}", e.code, e.title);
        let _ = writeln!(
            out,
            "pub const {}: DiagCode = DiagCode({:?});",
            constant(&e.name),
            e.code
        );
    }
    out += "\n/// Every entry, by code.\npub static ENTRIES: &[DiagEntry] = &[\n";
    for e in &entries {
        let _ = writeln!(
            out,
            "    DiagEntry {{ code: {}, name: {:?}, title: {:?}, spec: {:?}, retired: {:?}, rule: {:?}, rationale: {:?}, failing: {:?}, fixed: {:?} }},",
            constant(&e.name),
            e.name,
            e.title,
            e.spec,
            e.retired,
            e.rule,
            e.rationale,
            e.failing,
            e.fixed
        );
    }
    out += "];\n";
    let target = Path::new(&std::env::var("OUT_DIR").unwrap()).join("registry.rs");
    std::fs::write(target, out).expect("the generated registry");
}

/// `NoMatch` → `NO_MATCH`.
fn constant(name: &str) -> String {
    let mut out = String::new();
    for (i, c) in name.chars().enumerate() {
        if c.is_ascii_uppercase() && i > 0 {
            out.push('_');
        }
        out.push(c.to_ascii_uppercase());
    }
    out
}

/// An entry: a header of `key: value` lines between `---` lines, the rule
/// up to the first section, and the sections `Rationale`, `Failing` and
/// `Fixed`, the last two a `crag` code block each.
fn parse(text: &str) -> Result<Entry, String> {
    let rest = text.strip_prefix("---\n").ok_or("no header")?;
    let (header, body) = rest
        .split_once("\n---\n")
        .ok_or("the header does not end")?;
    let mut fields = BTreeMap::new();
    for line in header.lines() {
        let (key, value) = line
            .split_once(':')
            .ok_or(format!("`{line}` is no `key: value`"))?;
        fields.insert(key.trim().to_string(), value.trim().to_string());
    }
    let field = |key: &str| fields.get(key).cloned().ok_or(format!("no `{key}`"));
    let code = field("code")?;
    let valid = code.len() == 5
        && matches!(code.as_bytes()[0], b'E' | b'W')
        && code[1..].bytes().all(|b| b.is_ascii_digit());
    if !valid {
        return Err(format!(
            "`{code}` is no code: a letter for the severity and four digits"
        ));
    }
    let name = field("name")?;
    if !name.starts_with(|c: char| c.is_ascii_uppercase())
        || !name.chars().all(|c| c.is_ascii_alphanumeric())
    {
        return Err(format!("`{name}` is no name: a word in UpperCamelCase"));
    }
    let retired = fields.get("retired").cloned();
    let mut sections = BTreeMap::new();
    let mut current = String::new();
    let mut rule = String::new();
    for line in body.lines() {
        if let Some(heading) = line.strip_prefix("## ") {
            current = heading.trim().to_string();
            sections.insert(current.clone(), String::new());
            continue;
        }
        let target = match current.is_empty() {
            true => &mut rule,
            false => sections.get_mut(&current).unwrap(),
        };
        target.push_str(line);
        target.push('\n');
    }
    for heading in sections.keys() {
        if !["Rationale", "Failing", "Fixed"].contains(&heading.as_str()) {
            return Err(format!("unknown section `{heading}`"));
        }
    }
    let section = |key: &str| {
        sections
            .get(key)
            .map(|s| s.trim().to_string())
            .unwrap_or_default()
    };
    let code_block = |key: &str| -> Result<String, String> {
        let text = section(key);
        let inner = text
            .strip_prefix("```crag\n")
            .and_then(|t| t.strip_suffix("```"))
            .ok_or(format!("`{key}` is not one `crag` code block"))?;
        Ok(inner.to_string())
    };
    let rule = rule.trim().to_string();
    let rationale = section("Rationale");
    let (failing, fixed) = match retired {
        Some(_) => (String::new(), String::new()),
        None => (code_block("Failing")?, code_block("Fixed")?),
    };
    if rule.is_empty() {
        return Err("no rule".into());
    }
    if retired.is_none() && rationale.is_empty() {
        return Err("no rationale".into());
    }
    Ok(Entry {
        code,
        name,
        title: field("title")?,
        spec: field("spec")?,
        retired,
        rule,
        rationale,
        failing,
        fixed,
    })
}
