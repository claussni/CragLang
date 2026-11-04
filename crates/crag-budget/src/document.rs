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

//! Budget documents and what is derived from them.
//!
//! A document lists the budgets, with a name, a date and an issuer to
//! manage it by. Each budget's token is BLAKE3 keyed by the salt over the
//! document's canonical form followed by the budget's name ([`token`]).
//! The canonical form is the document's JSON with every object's keys
//! sorted and no space between tokens, as `serde_json` writes a value.
//!
//! A token file gives a sender one budget: the document's management
//! fields, the budget's name and limits, and the token as hex. The limits
//! are there for the sender to read; only the receiver enforces them.

use serde_json::Value;

/// The bytes of a salt, a token and a MAC.
pub const KEY: usize = 32;

/// Where a budget comes from: its document's management fields and its
/// own name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    pub document: String,
    pub date: String,
    pub issuer: String,
    pub name: String,
}

/// A budget's limits, none where the document leaves one out.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Limits {
    /// The steps all its runs may take, receiving included.
    pub steps: Option<u64>,
    /// The bytes its runs may hold at once.
    pub memory: Option<u64>,
    /// The trees it may send.
    pub runs: Option<u64>,
}

/// A budget document: its management fields and its budgets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Document {
    pub name: String,
    pub date: String,
    pub issuer: String,
    /// Each budget's name and limits, in the document's order.
    pub budgets: Vec<(String, Limits)>,
    /// The canonical form the tokens are derived from.
    pub canonical: Vec<u8>,
}

impl Document {
    /// Reads a budget document, which must hold exactly the fields the
    /// specification names.
    pub fn parse(text: &str) -> Result<Document, String> {
        let value: Value =
            serde_json::from_str(text).map_err(|e| format!("not a JSON document: {e}"))?;
        let top = fields(
            &value,
            "the document",
            &["name", "date", "issuer", "budgets"],
        )?;
        let name = string(top, "name", "the document")?;
        let date = string(top, "date", "the document")?;
        let issuer = string(top, "issuer", "the document")?;
        let Some(Value::Array(list)) = top.get("budgets") else {
            return Err("the document lacks a list of `budgets`".into());
        };
        if list.is_empty() {
            return Err("the document lists no budget".into());
        }
        let mut budgets: Vec<(String, Limits)> = Vec::new();
        for (i, entry) in list.iter().enumerate() {
            let what = format!("budget {}", i + 1);
            let entry = fields(entry, &what, &["name", "steps", "memory", "runs"])?;
            let name = string(entry, "name", &what)?;
            if !valid_name(&name) {
                return Err(format!(
                    "{what} is named `{name}`; a budget's name is letters, digits, `.`, `_` and `-`"
                ));
            }
            if budgets.iter().any(|(b, _)| *b == name) {
                return Err(format!("two budgets are named `{name}`"));
            }
            let limits = limits(entry, &name)?;
            budgets.push((name, limits));
        }
        let canonical = serde_json::to_vec(&value).expect("a value writes");
        Ok(Document {
            name,
            date,
            issuer,
            budgets,
            canonical,
        })
    }

    /// The budget of this name: its origin and limits.
    pub fn budget(&self, name: &str) -> Option<(Origin, Limits)> {
        let (_, limits) = self.budgets.iter().find(|(b, _)| b == name)?;
        Some((self.origin(name), *limits))
    }

    fn origin(&self, name: &str) -> Origin {
        Origin {
            document: self.name.clone(),
            date: self.date.clone(),
            issuer: self.issuer.clone(),
            name: name.to_string(),
        }
    }

    /// The token of the budget of this name.
    pub fn token(&self, salt: &[u8; KEY], name: &str) -> [u8; KEY] {
        token(salt, &self.canonical, name)
    }

    /// The token file of each budget, by its name, in the document's
    /// order.
    pub fn token_files(&self, salt: &[u8; KEY]) -> Vec<(String, String)> {
        self.budgets
            .iter()
            .map(|(name, limits)| {
                let file = TokenFile {
                    origin: self.origin(name),
                    limits: *limits,
                    token: self.token(salt, name),
                };
                (name.clone(), file.write())
            })
            .collect()
    }
}

/// The object `value` must be, with no keys but these.
fn fields<'a>(
    value: &'a Value,
    what: &str,
    known: &[&str],
) -> Result<&'a serde_json::Map<String, Value>, String> {
    let Value::Object(map) = value else {
        return Err(format!("{what} is not an object"));
    };
    if let Some(key) = map.keys().find(|k| !known.contains(&k.as_str())) {
        return Err(format!("{what} has an unknown field `{key}`"));
    }
    Ok(map)
}

fn string(map: &serde_json::Map<String, Value>, key: &str, what: &str) -> Result<String, String> {
    match map.get(key) {
        Some(Value::String(s)) => Ok(s.clone()),
        Some(_) => Err(format!("`{key}` of {what} is not a string")),
        None => Err(format!("{what} lacks `{key}`")),
    }
}

fn limits(map: &serde_json::Map<String, Value>, name: &str) -> Result<Limits, String> {
    let limit = |key: &str| -> Result<Option<u64>, String> {
        match map.get(key) {
            None => Ok(None),
            Some(v) => v
                .as_u64()
                .filter(|&n| n <= i64::MAX as u64)
                .map(Some)
                .ok_or_else(|| format!("`{key}` of `{name}` is not a whole number")),
        }
    };
    Ok(Limits {
        steps: limit("steps")?,
        memory: limit("memory")?,
        runs: limit("runs")?,
    })
}

/// Whether a budget's name may name its token's file.
fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && !name.starts_with('.')
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-'))
}

/// A budget's token: BLAKE3 keyed by the salt over the document's
/// canonical form followed by the budget's name.
pub fn token(salt: &[u8; KEY], canonical: &[u8], name: &str) -> [u8; KEY] {
    let mut hasher = blake3::Hasher::new_keyed(salt);
    hasher.update(canonical);
    hasher.update(name.as_bytes());
    *hasher.finalize().as_bytes()
}

/// The bytes as lowercase hex.
pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The key that `text`, hex with spaces around it, spells.
pub fn unhex(text: &str) -> Option<[u8; KEY]> {
    let text = text.trim();
    if text.len() != 2 * KEY {
        return None;
    }
    let mut key = [0; KEY];
    for (i, byte) in key.iter_mut().enumerate() {
        *byte = u8::from_str_radix(text.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(key)
}

/// A sender's token file: the budget it is of and the token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenFile {
    pub origin: Origin,
    pub limits: Limits,
    pub token: [u8; KEY],
}

impl TokenFile {
    pub fn parse(text: &str) -> Result<TokenFile, String> {
        let value: Value =
            serde_json::from_str(text).map_err(|e| format!("not a token file: {e}"))?;
        let what = "the token file";
        let map = fields(
            &value,
            what,
            &[
                "document", "date", "issuer", "budget", "steps", "memory", "runs", "token",
            ],
        )?;
        let origin = Origin {
            document: string(map, "document", what)?,
            date: string(map, "date", what)?,
            issuer: string(map, "issuer", what)?,
            name: string(map, "budget", what)?,
        };
        let limits = limits(map, &origin.name)?;
        let token = unhex(&string(map, "token", what)?)
            .ok_or("the token file holds no token of 64 hex digits")?;
        Ok(TokenFile {
            origin,
            limits,
            token,
        })
    }

    pub fn write(&self) -> String {
        let mut value = serde_json::json!({
            "document": self.origin.document,
            "date": self.origin.date,
            "issuer": self.origin.issuer,
            "budget": self.origin.name,
            "token": hex(&self.token),
        });
        for (key, limit) in [
            ("steps", self.limits.steps),
            ("memory", self.limits.memory),
            ("runs", self.limits.runs),
        ] {
            if let Some(n) = limit {
                value[key] = n.into();
            }
        }
        serde_json::to_string_pretty(&value).expect("a value writes") + "\n"
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub(crate) const DOCUMENT: &str = r#"{
  "name": "partner-reports",
  "date": "2026-11-04",
  "issuer": "ops@example.org",
  "budgets": [
    { "name": "acme", "steps": 1000, "memory": 4096, "runs": 3 },
    { "name": "globex", "runs": 1 }
  ]
}"#;

    pub(crate) const SALT: [u8; KEY] = [7; KEY];

    #[test]
    fn a_document_reads_and_its_canonical_form_ignores_layout() {
        let d = Document::parse(DOCUMENT).unwrap();
        assert_eq!(d.name, "partner-reports");
        assert_eq!(d.budgets.len(), 2);
        assert_eq!(d.budgets[1].1.steps, None);
        let compact: String = DOCUMENT.split_whitespace().collect();
        assert_eq!(Document::parse(&compact).unwrap().canonical, d.canonical);
        // Each budget has its own token, and another salt gives others.
        assert_ne!(d.token(&SALT, "acme"), d.token(&SALT, "globex"));
        assert_ne!(d.token(&[8; KEY], "acme"), d.token(&SALT, "acme"));
        // A changed document gives other tokens.
        let changed = Document::parse(&DOCUMENT.replace("1000", "1001")).unwrap();
        assert_ne!(changed.token(&SALT, "acme"), d.token(&SALT, "acme"));
    }

    #[test]
    fn a_malformed_document_is_refused() {
        for (text, why) in [
            ("[]", "not an object"),
            (
                &DOCUMENT.replace("\"issuer\"", "\"owner\""),
                "unknown field",
            ),
            (&DOCUMENT.replace("\"globex\"", "\"acme\""), "two budgets"),
            (&DOCUMENT.replace("\"globex\"", "\"../x\""), "letters"),
            (&DOCUMENT.replace("1000", "-1"), "whole number"),
            (&DOCUMENT.replace("\"budgets\"", "\"x\""), "unknown field"),
        ] {
            let e = Document::parse(text).unwrap_err();
            assert!(e.contains(why), "{e}");
        }
    }

    #[test]
    fn a_token_file_round_trips() {
        let d = Document::parse(DOCUMENT).unwrap();
        let files = d.token_files(&SALT);
        let acme = TokenFile::parse(&files[0].1).unwrap();
        assert_eq!(acme.origin.name, "acme");
        assert_eq!(acme.origin.issuer, "ops@example.org");
        assert_eq!(acme.limits.steps, Some(1000));
        assert_eq!(acme.token, d.token(&SALT, "acme"));
        let globex = TokenFile::parse(&files[1].1).unwrap();
        assert_eq!(
            globex.limits,
            Limits {
                runs: Some(1),
                ..Limits::default()
            }
        );
        assert_eq!(unhex(&format!(" {}\n", hex(&acme.token))), Some(acme.token));
        assert_eq!(unhex("00"), None);
    }
}
