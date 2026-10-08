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

//! Decoding literals (§2.6). The lexer cut them by shape only; here digits,
//! escapes, braces and the indentation of triple-quoted strings are
//! checked and turned into values.

/// A literal's value. Whether it fits its type is for inference to say.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Int(u128),
    /// The digits as written, without separators: a decimal is a `Fixed`
    /// or a `Float` depending on the expected type.
    Float(String),
    Str(String),
    Bytes(Vec<u8>),
    CodePoint(char),
}

pub fn int(text: &str) -> Result<u128, String> {
    let (radix, digits) = match text.get(..2) {
        Some("0x") => (16, &text[2..]),
        Some("0b") => (2, &text[2..]),
        Some("0o") => (8, &text[2..]),
        _ => (10, text),
    };
    let digits: String = digits.chars().filter(|&c| c != '_').collect();
    if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
        return Err(format!("`{text}` is not a number"));
    }
    u128::from_str_radix(&digits, radix).map_err(|_| format!("`{text}` is too large"))
}

pub fn float(text: &str) -> Result<String, String> {
    let digits: String = text.chars().filter(|&c| c != '_').collect();
    match digits.parse::<f64>() {
        Ok(_) if digits.starts_with(|c: char| c.is_ascii_digit()) => Ok(digits),
        _ => Err(format!("`{text}` is not a number")),
    }
}

pub fn code_point(text: &str) -> Result<char, String> {
    let Some(inner) = text
        .strip_prefix('\'')
        .and_then(|t| t.strip_suffix('\''))
        .filter(|_| text.len() >= 2)
    else {
        return Err("unclosed code point literal".into());
    };
    let mut out = Vec::new();
    unescape(inner, Escapes::Text, &mut out)?;
    let decoded = String::from_utf8(out).expect("escapes in text are UTF-8");
    let mut chars = decoded.chars();
    match (chars.next(), chars.next()) {
        (Some(c), None) => Ok(c),
        _ => Err("a code point literal holds exactly one character".into()),
    }
}

pub fn bytes(text: &str) -> Result<Vec<u8>, String> {
    let inner = text
        .strip_prefix("b\"")
        .and_then(|t| t.strip_suffix('"'))
        .filter(|_| text.len() >= 3)
        .ok_or("unclosed byte literal")?;
    let mut out = Vec::new();
    unescape(inner, Escapes::Bytes, &mut out)?;
    Ok(out)
}

/// Part of a string literal with interpolations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Piece {
    Text(String),
    /// The interpolation at this index.
    Hole(usize),
}

/// Decodes a string from its tokens: one `Str` token, or a `StrStart` or
/// `TripleStrStart`, `StrMid`s and a `StrEnd`, with one interpolation
/// between each two.
pub fn string(tokens: &[&str]) -> Result<Vec<Piece>, String> {
    let first = tokens.first().copied().unwrap_or_default();
    let triple = first.starts_with("\"\"\"");
    let quote = if triple { "\"\"\"" } else { "\"" };
    let last = tokens.len() - 1;
    let mut pieces = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        let mut text = *token;
        text = if i == 0 {
            &text[quote.len().min(text.len())..]
        } else {
            &text[1..]
        };
        if i < last {
            text = &text[..text.len() - 1];
        } else {
            text = text.strip_suffix(quote).ok_or("unclosed string")?;
        }
        if i > 0 {
            pieces.push(Piece::Hole(i - 1));
        }
        pieces.push(Piece::Text(text.to_string()));
    }
    if triple {
        pieces = dedent(pieces)?;
    }
    pieces
        .into_iter()
        .filter(|p| *p != Piece::Text(String::new()))
        .map(|piece| match piece {
            Piece::Text(raw) => {
                let mut out = Vec::new();
                unescape(&raw, Escapes::Text, &mut out)?;
                Ok(Piece::Text(
                    String::from_utf8(out).expect("escapes in text are UTF-8"),
                ))
            }
            hole => Ok(hole),
        })
        .collect()
}

/// The content of a triple-quoted string without the line breaks after the
/// opening and before the closing quotes, and without the indentation all
/// content lines share (§2.6).
fn dedent(pieces: Vec<Piece>) -> Result<Vec<Piece>, String> {
    let mut lines: Vec<Vec<Piece>> = vec![Vec::new()];
    for piece in pieces {
        match piece {
            Piece::Text(text) => {
                for (i, part) in text.split('\n').enumerate() {
                    if i > 0 {
                        lines.push(Vec::new());
                    }
                    lines
                        .last_mut()
                        .unwrap()
                        .push(Piece::Text(part.to_string()));
                }
            }
            hole => lines.last_mut().unwrap().push(hole),
        }
    }
    let blank = |line: &[Piece]| {
        line.iter()
            .all(|p| matches!(p, Piece::Text(t) if t.trim().is_empty()))
    };
    if lines.len() < 2 || !blank(&lines[0]) {
        return Err("a triple-quoted string starts on the line after its `\"\"\"`".into());
    }
    if !blank(lines.last().unwrap()) {
        return Err("a triple-quoted string ends on the line before its `\"\"\"`".into());
    }
    lines.remove(0);
    lines.pop();
    let indent = |line: &[Piece]| match line.first() {
        Some(Piece::Text(t)) => t.len() - t.trim_start_matches([' ', '\t']).len(),
        _ => 0,
    };
    let common = lines
        .iter()
        .filter(|l| !blank(l))
        .map(|l| indent(l))
        .min()
        .unwrap_or(0);
    let mut out = Vec::new();
    for (i, mut line) in lines.into_iter().enumerate() {
        if i > 0 {
            out.push(Piece::Text("\n".into()));
        }
        if let Some(Piece::Text(t)) = line.first_mut() {
            *t = t.get(common..).unwrap_or_default().to_string();
        }
        out.extend(line);
    }
    // Neighbouring texts as one.
    let mut merged: Vec<Piece> = Vec::new();
    for piece in out {
        match (merged.last_mut(), piece) {
            (Some(Piece::Text(a)), Piece::Text(b)) => a.push_str(&b),
            (_, piece) => merged.push(piece),
        }
    }
    Ok(merged)
}

#[derive(Clone, Copy, PartialEq)]
enum Escapes {
    /// Strings and code points: interpolation braces are doubled.
    Text,
    /// Byte literals, which also take `\xHH`.
    Bytes,
}

fn unescape(raw: &str, escapes: Escapes, out: &mut Vec<u8>) -> Result<(), String> {
    let mut chars = raw.chars().peekable();
    let push = |c: char, out: &mut Vec<u8>| {
        let mut buffer = [0; 4];
        out.extend_from_slice(c.encode_utf8(&mut buffer).as_bytes());
    };
    while let Some(c) = chars.next() {
        match c {
            '\\' => {
                let escaped = chars.next().ok_or("a `\\` ends the literal")?;
                let c = match escaped {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '0' => '\0',
                    '\\' | '"' | '\'' => escaped,
                    'x' if escapes == Escapes::Bytes => {
                        let hex: String = chars.by_ref().take(2).collect();
                        let byte = u8::from_str_radix(&hex, 16)
                            .ok()
                            .filter(|_| hex.len() == 2)
                            .ok_or("`\\x` takes two hexadecimal digits")?;
                        out.push(byte);
                        continue;
                    }
                    'u' => {
                        let bad = || "`\\u{…}` takes one to six hexadecimal digits".to_string();
                        if chars.next() != Some('{') {
                            return Err(bad());
                        }
                        let hex: String = chars.by_ref().take_while(|&c| c != '}').collect();
                        if hex.is_empty() || hex.len() > 6 {
                            return Err(bad());
                        }
                        let value = u32::from_str_radix(&hex, 16).map_err(|_| bad())?;
                        char::from_u32(value)
                            .ok_or(format!("`\\u{{{hex}}}` is not a Unicode scalar value"))?
                    }
                    other => return Err(format!("unknown escape `\\{other}`")),
                };
                push(c, out);
            }
            '{' | '}' if escapes == Escapes::Text => {
                if chars.next() != Some(c) {
                    return Err(format!("a literal `{c}` is written `{c}{c}`"));
                }
                push(c, out);
            }
            c => push(c, out),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(pieces: &[Piece]) -> String {
        pieces
            .iter()
            .map(|p| match p {
                Piece::Text(t) => t.clone(),
                Piece::Hole(i) => format!("<{i}>"),
            })
            .collect()
    }

    #[test]
    fn numbers() {
        assert_eq!(int("1_000"), Ok(1000));
        assert_eq!(int("0xFF_FF"), Ok(0xffff));
        assert_eq!(int("0b1010"), Ok(10));
        assert_eq!(int("0o755"), Ok(0o755));
        assert!(int("12ab").is_err());
        assert!(int("0x").is_err());
        assert!(int(&"9".repeat(40)).is_err());
        assert_eq!(float("1_000.5"), Ok("1000.5".into()));
        assert_eq!(float("1e-9"), Ok("1e-9".into()));
        assert!(float("1.5x").is_err());
    }

    #[test]
    fn escapes_and_braces() {
        let s = |tokens: &[&str]| string(tokens).map(|p| text(&p));
        assert_eq!(s(&[r#""a\n\"b\u{1F600}""#]), Ok("a\n\"b😀".into()));
        assert_eq!(s(&[r#""{{x}}""#]), Ok("{x}".into()));
        assert_eq!(s(&["\"a {", "} b {", "}\""]), Ok("a <0> b <1>".into()));
        assert!(s(&[r#""\q""#]).is_err());
        assert!(s(&[r#""\x41""#]).is_err());
        assert!(s(&[r#""a}b""#]).is_err());
        assert!(s(&["\"open"]).is_err());
        assert_eq!(bytes(r#"b"\x00\xffA""#), Ok(vec![0, 255, b'A']));
        assert_eq!(code_point(r"'\''"), Ok('\''));
        assert!(code_point("'ab'").is_err());
    }

    #[test]
    fn triple_quoted_strings_lose_their_indentation() {
        let s = |tokens: &[&str]| string(tokens).map(|p| text(&p));
        assert_eq!(
            s(&[
                "\"\"\"\n    SELECT name\n      FROM orders\n\n    WHERE id = {",
                "}\n    \"\"\""
            ]),
            Ok("SELECT name\n  FROM orders\n\nWHERE id = <0>".into())
        );
        assert!(s(&["\"\"\"text\n\"\"\""]).is_err());
    }
}
