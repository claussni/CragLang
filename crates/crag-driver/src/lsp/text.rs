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

//! Positions as the protocol counts them, line and character, and byte
//! offsets as the compiler does. Characters are UTF-16 code units unless
//! the client accepts UTF-8 (LSP 3.17 `positionEncoding`).

use serde_json::{Value, json};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Encoding {
    Utf8,
    Utf16,
}

impl Encoding {
    pub fn name(self) -> &'static str {
        match self {
            Encoding::Utf8 => "utf-8",
            Encoding::Utf16 => "utf-16",
        }
    }
}

/// The byte offset of `(line, character)` in `text`, clamped to the line
/// and the text.
pub fn offset(text: &str, line: u32, character: u32, encoding: Encoding) -> u32 {
    let mut start = 0;
    for _ in 0..line {
        match text[start..].find('\n') {
            Some(i) => start += i + 1,
            None => return text.len() as u32,
        }
    }
    let end = text[start..].find('\n').map_or(text.len(), |i| start + i);
    let line = &text[start..end];
    let mut units = 0;
    for (i, c) in line.char_indices() {
        if units >= character {
            return (start + i) as u32;
        }
        units += match encoding {
            Encoding::Utf8 => c.len_utf8() as u32,
            Encoding::Utf16 => c.len_utf16() as u32,
        };
    }
    end as u32
}

/// The line and character of a byte offset.
pub fn position(text: &str, offset: u32, encoding: Encoding) -> (u32, u32) {
    let mut offset = (offset as usize).min(text.len());
    while !text.is_char_boundary(offset) {
        offset -= 1;
    }
    let before = &text[..offset];
    let line = before.matches('\n').count() as u32;
    let start = before.rfind('\n').map_or(0, |i| i + 1);
    let character = match encoding {
        Encoding::Utf8 => (offset - start) as u32,
        Encoding::Utf16 => text[start..offset].encode_utf16().count() as u32,
    };
    (line, character)
}

pub fn json_position(text: &str, offset: u32, encoding: Encoding) -> Value {
    let (line, character) = position(text, offset, encoding);
    json!({"line": line, "character": character})
}

pub fn json_range(text: &str, range: std::ops::Range<u32>, encoding: Encoding) -> Value {
    json!({
        "start": json_position(text, range.start, encoding),
        "end": json_position(text, range.end, encoding),
    })
}

/// The byte offset of a protocol position, `{"line", "character"}`.
pub fn from_json(text: &str, position: &Value, encoding: Encoding) -> Option<u32> {
    let line = position.get("line")?.as_u64()? as u32;
    let character = position.get("character")?.as_u64()? as u32;
    Some(offset(text, line, character, encoding))
}

/// Applies one content change of `didChange`: a range and its new text,
/// or the whole text when the change has no range.
pub fn apply_change(text: &mut String, change: &Value, encoding: Encoding) -> Option<()> {
    let new = change.get("text")?.as_str()?;
    match change.get("range") {
        Some(range) => {
            let start = from_json(text, range.get("start")?, encoding)? as usize;
            let end = from_json(text, range.get("end")?, encoding)? as usize;
            let (start, end) = (start.min(end), start.max(end));
            text.replace_range(start..end, new);
        }
        None => *text = new.to_string(),
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utf16_counts_code_units() {
        let text = "a€𝄞b\nxy";
        assert_eq!(position(text, 8, Encoding::Utf16), (0, 4));
        assert_eq!(offset(text, 0, 4, Encoding::Utf16), 8);
        assert_eq!(position(text, 8, Encoding::Utf8), (0, 8));
        assert_eq!(offset(text, 1, 1, Encoding::Utf16), 11);
        // Past the end of a line or the text: clamped.
        assert_eq!(offset(text, 0, 99, Encoding::Utf16), 9);
        assert_eq!(offset(text, 9, 0, Encoding::Utf16), 12);
    }

    #[test]
    fn changes_apply_in_order() {
        let mut text = "let x = 1\n".to_string();
        let change = json!({"range": {"start": {"line": 0, "character": 8}, "end": {"line": 0, "character": 9}}, "text": "42"});
        apply_change(&mut text, &change, Encoding::Utf16).unwrap();
        assert_eq!(text, "let x = 42\n");
        apply_change(&mut text, &json!({"text": "new"}), Encoding::Utf16).unwrap();
        assert_eq!(text, "new");
    }
}
