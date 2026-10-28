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

//! The manifest `package.crag` (Specification §14.5.1): the package's
//! name and version, the runtime it requires, its text, what it exports
//! and imports and, for an application, its entry module.
//!
//! The manifest lexes as Crag, so strings, comments and line breaks mean
//! what they mean in code. Each declaration is one logical line. The
//! commands that edit the manifest change only the lines they touch
//! (§20.6), so every import remembers where it stands.

use std::ops::Range;
use std::path::PathBuf;

use crag_syntax::{Token, TokenKind, lex};

use crate::version::Version;

/// Where a dependency comes from when the manifest names its source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// `from "path:…"`: a package folder, relative to the manifest's
    /// directory unless absolute.
    Path(PathBuf),
}

/// An `import` of the manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dependency {
    pub name: String,
    pub version: Version,
    /// `import dev`: for test and tool modules only, never shipped.
    pub dev: bool,
    pub source: Option<Source>,
    /// The 1-based line it starts on.
    pub line: usize,
    /// The declaration's bytes in the manifest, and its version's.
    pub span: Range<usize>,
    pub version_span: Range<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Manifest {
    pub package: String,
    pub version: Option<Version>,
    pub runtime: Option<Version>,
    pub name: Option<String>,
    pub summary: Option<String>,
    pub description: Option<String>,
    /// The paths `export` names, selections spelled out.
    pub exports: Vec<String>,
    pub imports: Vec<Dependency>,
    pub main: Option<String>,
    /// The native libraries `cLib` names stand for: each name with the
    /// files to try, in order (§14.5.1).
    pub natives: Vec<(String, Vec<String>)>,
}

/// A mistake in a manifest, at a 1-based line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ManifestError {
    pub line: usize,
    pub message: String,
}

/// Whether `name` is a package name: dotted segments that start with a
/// letter and go on with letters, digits and `_` (§20.4).
pub fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name.split('.').all(|segment| {
            let mut chars = segment.chars();
            chars.next().is_some_and(|c| c.is_ascii_alphabetic())
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}

/// Whether the name is reserved for the bundled standard library.
pub fn reserved(name: &str) -> bool {
    name == "std" || name.starts_with("std.")
}

impl Manifest {
    /// Reads a manifest; every mistake is reported, each at its line.
    pub fn parse(text: &str) -> Result<Manifest, Vec<ManifestError>> {
        let mut manifest = Manifest::default();
        let mut errors = Vec::new();
        let tokens = lex(text);
        let line_of = |at: u32| text[..at as usize].matches('\n').count() + 1;
        let mut seen: Vec<&str> = Vec::new();
        for decl in tokens
            .split(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof))
            .filter(|d| !d.is_empty())
        {
            let line = line_of(decl[0].start);
            let mut fail = |message: String| errors.push(ManifestError { line, message });
            let word = decl[0].text(text);
            let rest = &decl[1..];
            // The declaration's words after the first, as written.
            let raw = match (rest.first(), rest.last()) {
                (Some(first), Some(last)) => &text[first.start as usize..last.end as usize],
                _ => "",
            };
            let once = [
                "package",
                "runtime",
                "name",
                "summary",
                "description",
                "main",
            ];
            if once.contains(&word) {
                if seen.contains(&word) {
                    fail(format!("`{word}` is declared twice"));
                    continue;
                }
                seen.push(word);
            }
            match word {
                "package" => {
                    let parts: Vec<&str> = raw.split_whitespace().collect();
                    let [name, version] = parts[..] else {
                        fail("write `package <name> <version>`".into());
                        continue;
                    };
                    if !valid_name(name) {
                        fail(format!("`{name}` is not a package name"));
                    }
                    manifest.package = name.to_string();
                    match Version::parse(version) {
                        Ok(v) => manifest.version = Some(v),
                        Err(e) => fail(e),
                    }
                }
                "runtime" => match Version::parse(raw) {
                    Ok(v) => manifest.runtime = Some(v),
                    Err(e) => fail(e),
                },
                "name" | "summary" | "description" => match string(text, rest) {
                    Ok(s) => {
                        let field = match word {
                            "name" => &mut manifest.name,
                            "summary" => &mut manifest.summary,
                            _ => &mut manifest.description,
                        };
                        *field = Some(s);
                    }
                    Err(e) => fail(format!("`{word}` takes a string: {e}")),
                },
                "main" => {
                    if valid_name(raw) {
                        manifest.main = Some(raw.to_string());
                    } else {
                        fail(format!("`{raw}` is not a module path"));
                    }
                }
                "export" => match selection(raw) {
                    Some(paths) => manifest.exports.extend(paths),
                    None => fail(format!("`{raw}` is not a module path or selection")),
                },
                "import" => match dependency(text, rest) {
                    Ok(mut dep) => {
                        dep.line = line;
                        dep.span = decl[0].start as usize..decl[decl.len() - 1].end as usize;
                        manifest.imports.push(dep);
                    }
                    Err(e) => fail(e),
                },
                "native" => match native(text, rest) {
                    Ok((name, _)) if manifest.natives.iter().any(|(n, _)| *n == name) => {
                        fail(format!("the native library `{name}` is declared twice"));
                    }
                    Ok(native) => manifest.natives.push(native),
                    Err(e) => fail(e),
                },
                _ => fail(format!(
                    "a manifest declares only package, runtime, name, summary, description, export, import, main and native; not `{word}`"
                )),
            }
        }
        if manifest.package.is_empty() && !errors.iter().any(|e| e.message.contains("package")) {
            errors.push(ManifestError {
                line: 1,
                message: "the manifest has no `package` line".into(),
            });
        }
        // One major of a package per manifest (§14.5, rule 4).
        for (i, dep) in manifest.imports.iter().enumerate() {
            if manifest.imports[..i].iter().any(|d| d.name == dep.name) {
                errors.push(ManifestError {
                    line: dep.line,
                    message: format!("`{}` is imported twice", dep.name),
                });
            }
        }
        if errors.is_empty() {
            Ok(manifest)
        } else {
            Err(errors)
        }
    }

    pub fn import(&self, name: &str) -> Option<&Dependency> {
        self.imports.iter().find(|d| d.name == name)
    }
}

/// The text of the one string a declaration takes.
fn string(text: &str, tokens: &[Token]) -> Result<String, String> {
    let [token] = tokens else {
        return Err("write one string".into());
    };
    if token.kind != TokenKind::Str {
        return Err("write one string, without interpolation".into());
    }
    let pieces = crag_hir::literal::string(&[token.text(text)])?;
    Ok(pieces
        .into_iter()
        .map(|p| match p {
            crag_hir::literal::Piece::Text(t) => t,
            crag_hir::literal::Piece::Hole(_) => String::new(),
        })
        .collect())
}

/// `native L "file", …`, from the tokens after `native`.
fn native(text: &str, tokens: &[Token]) -> Result<(String, Vec<String>), String> {
    let usage = || "write `native <name> \"<file>\", …`".to_string();
    let [name, files @ ..] = tokens else {
        return Err(usage());
    };
    if name.kind != TokenKind::Ident || files.is_empty() {
        return Err(usage());
    }
    let files = files
        .split(|t| t.kind == TokenKind::Comma)
        .map(|file| string(text, file))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("{}: {e}", usage()))?;
    Ok((name.text(text).to_string(), files))
}

/// The paths of `a.b`, or of a selection `a.{b, c}`.
fn selection(raw: &str) -> Option<Vec<String>> {
    let raw: String = raw.chars().filter(|c| !c.is_whitespace()).collect();
    match raw.split_once(".{") {
        Some((prefix, rest)) => {
            let names = rest.strip_suffix('}')?;
            let paths: Vec<String> = names.split(',').map(|n| format!("{prefix}.{n}")).collect();
            (valid_name(prefix) && paths.iter().all(|p| valid_name(p))).then_some(paths)
        }
        None => valid_name(&raw).then(|| vec![raw]),
    }
}

/// `import [dev] P V [from "…"]`, from the tokens after `import`.
fn dependency(text: &str, tokens: &[Token]) -> Result<Dependency, String> {
    let usage = || "write `import [dev] <package> <version> [from \"path:…\"]`".to_string();
    // Words are runs of tokens with nothing between them: `acme.geo` and
    // `1.2.3` lex as several tokens each.
    let mut words: Vec<(String, Range<usize>, &Token)> = Vec::new();
    for token in tokens {
        match words.last_mut() {
            Some((word, range, _))
                if token.trivia_start == token.start && range.end == token.start as usize =>
            {
                word.push_str(token.text(text));
                range.end = token.end as usize;
            }
            _ => words.push((
                token.text(text).to_string(),
                token.start as usize..token.end as usize,
                token,
            )),
        }
    }
    // `dev` is a word only here: a package may be named `dev`.
    let dev = words.len() > 2
        && words[0].0 == "dev"
        && !words[1].0.starts_with(|c: char| c.is_ascii_digit());
    let mut words = words.into_iter().skip(usize::from(dev));
    let (name, _, _) = words.next().ok_or_else(usage)?;
    if !valid_name(&name) {
        return Err(format!("`{name}` is not a package name"));
    }
    if reserved(&name) {
        return Err(format!(
            "`{name}` is bundled with the runtime; modules import it without a manifest entry"
        ));
    }
    let (version, version_span, _) = words.next().ok_or_else(usage)?;
    let version = Version::parse(&version)?;
    let source = match words.next() {
        None => None,
        Some((from, _, _)) if from == "from" => {
            let (_, _, token) = words.next().ok_or_else(usage)?;
            let source = string(text, std::slice::from_ref(token))?;
            match source.split_once(':') {
                Some(("path", path)) => Some(Source::Path(PathBuf::from(path))),
                Some((scheme, _)) => {
                    return Err(format!(
                        "sources of the scheme `{scheme}` are not supported yet; use `path:`"
                    ));
                }
                None => return Err(format!("`{source}` names no scheme; write `path:{source}`")),
            }
        }
        Some(_) => return Err(usage()),
    };
    if words.next().is_some() {
        return Err(usage());
    }
    Ok(Dependency {
        name,
        version,
        dev,
        source,
        line: 0,
        span: 0..0,
        version_span,
    })
}

/// The manifest with an import added after the last one, or after the
/// last declaration when there is none.
pub fn add_import(text: &str, manifest: &Manifest, name: &str, version: &Version) -> String {
    let line = format!("import {name} {version}");
    let at = manifest
        .imports
        .iter()
        .map(|d| d.span.end)
        .max()
        .unwrap_or_else(|| text.trim_end().len());
    let mut out = String::with_capacity(text.len() + line.len() + 2);
    out.push_str(&text[..at]);
    if at == 0 {
        out.push_str(&line);
    } else {
        out.push('\n');
        out.push_str(&line);
    }
    out.push_str(&text[at..]);
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// The manifest without the import, line and all.
pub fn remove_import(text: &str, dep: &Dependency) -> String {
    let start = text[..dep.span.start].rfind('\n').map_or(0, |i| i + 1);
    let end = text[dep.span.end..]
        .find('\n')
        .map_or(text.len(), |i| dep.span.end + i + 1);
    format!("{}{}", &text[..start], &text[end..])
}

/// The manifest with the import's version replaced.
pub fn set_version(text: &str, dep: &Dependency, version: &Version) -> String {
    format!(
        "{}{version}{}",
        &text[..dep.version_span.start],
        &text[dep.version_span.end..]
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const SHOP: &str = r#"package shop 2.1
runtime 1.4

name "Shop"
summary "Carts, orders and payments"
description """
    A storefront toolkit with typed money,
    atomic stock updates.
    """

export shop.cart
export shop.{order, payment}

import http 3.2.1
import json 1.8 // for the API
import billing 1.2 from "path:../billing"
import dev testkit 0.9
import dev 1.0 from "path:dev"
"#;

    #[test]
    fn the_manifest_of_the_specification_reads() {
        let m = Manifest::parse(SHOP).unwrap();
        assert_eq!(m.package, "shop");
        assert_eq!(m.version, Some(Version::new(2, 1, None)));
        assert_eq!(m.runtime, Some(Version::new(1, 4, None)));
        assert_eq!(m.name.as_deref(), Some("Shop"));
        assert_eq!(
            m.description.as_deref(),
            Some("A storefront toolkit with typed money,\natomic stock updates.")
        );
        assert_eq!(m.exports, ["shop.cart", "shop.order", "shop.payment"]);
        let names: Vec<_> = m
            .imports
            .iter()
            .map(|d| (d.name.as_str(), d.version.to_string(), d.dev))
            .collect();
        assert_eq!(
            names,
            [
                ("http", "3.2.1".to_string(), false),
                ("json", "1.8".to_string(), false),
                ("billing", "1.2".to_string(), false),
                ("testkit", "0.9".to_string(), true),
                ("dev", "1.0".to_string(), false),
            ]
        );
        assert_eq!(
            m.import("billing").unwrap().source,
            Some(Source::Path("../billing".into()))
        );
        assert_eq!(m.import("json").unwrap().line, 15);
        assert_eq!(
            &SHOP[m.import("http").unwrap().version_span.clone()],
            "3.2.1"
        );
    }

    #[test]
    fn mistakes_are_reported_at_their_lines() {
        let errors = Manifest::parse(
            "package demo 0.1\nruntime one\nimport std.io 1.0\nimport geo 1.0\nimport geo 1.1\nlet x = 1\nimport x 1.0 from \"git:x\"\n",
        )
        .unwrap_err();
        let lines: Vec<usize> = errors.iter().map(|e| e.line).collect();
        assert_eq!(lines, [2, 3, 6, 7, 5], "{errors:?}");
        assert!(Manifest::parse("runtime 1.0\n").is_err());
    }

    #[test]
    fn native_libraries_name_the_files_to_try() {
        let m = Manifest::parse(
            "package demo 0.1\nnative sqlite \"libsqlite3.so.0\", \"libsqlite3.so\"\nnative m \"libm.so.6\"\n",
        )
        .unwrap();
        assert_eq!(
            m.natives,
            [
                (
                    "sqlite".to_string(),
                    vec!["libsqlite3.so.0".to_string(), "libsqlite3.so".to_string()]
                ),
                ("m".to_string(), vec!["libm.so.6".to_string()]),
            ]
        );
        let errors = Manifest::parse(
            "package demo 0.1\nnative m\nnative \"libm.so.6\"\nnative m \"a\" \"b\"\nnative c \"libc.so.6\"\nnative c \"libc.so\"\n",
        )
        .unwrap_err();
        let lines: Vec<usize> = errors.iter().map(|e| e.line).collect();
        assert_eq!(lines, [2, 3, 4, 6], "{errors:?}");
        assert!(errors[3].message.contains("declared twice"), "{errors:?}");
    }

    #[test]
    fn edits_touch_only_their_lines() {
        let m = Manifest::parse(SHOP).unwrap();
        let added = add_import(SHOP, &m, "geo", &Version::new(1, 1, None));
        assert!(
            added.ends_with("import dev 1.0 from \"path:dev\"\nimport geo 1.1\n"),
            "{added}"
        );
        let removed = remove_import(SHOP, m.import("json").unwrap());
        assert_eq!(
            removed,
            SHOP.replace("import json 1.8 // for the API\n", "")
        );
        let set = set_version(SHOP, m.import("http").unwrap(), &Version::new(3, 4, None));
        assert_eq!(set, SHOP.replace("http 3.2.1", "http 3.4"));
        let bare = "package demo 0.1\nruntime 0.0\nmain demo.app";
        let m = Manifest::parse(bare).unwrap();
        assert_eq!(
            add_import(bare, &m, "geo", &Version::new(1, 0, None)),
            "package demo 0.1\nruntime 0.0\nmain demo.app\nimport geo 1.0\n"
        );
    }
}
