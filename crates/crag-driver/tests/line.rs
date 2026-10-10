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

//! The line editor: keys from what a terminal sends, and what they do.

use crag_driver::line::{Key, Line, Outcome, decode};

/// Every key in the bytes.
fn keys(mut bytes: &[u8]) -> Vec<Key> {
    let mut out = Vec::new();
    while let Some((key, len)) = decode(bytes) {
        out.push(key);
        bytes = &bytes[len..];
    }
    assert!(bytes.is_empty(), "left over: {bytes:?}");
    out
}

/// Types the keys into a fresh line.
fn typed(keys: &[Key], history: &[String]) -> (Line, Vec<Outcome>) {
    let names = ["total", "tally", "type"];
    let complete = |prefix: &str| -> Vec<String> {
        names
            .iter()
            .filter(|n| n.starts_with(prefix))
            .map(|n| n.to_string())
            .collect()
    };
    let mut line = Line::default();
    let outcomes = keys
        .iter()
        .map(|&k| line.key(k, history, &complete))
        .collect();
    (line, outcomes)
}

fn chars(text: &str) -> Vec<Key> {
    text.chars().map(Key::Char).collect()
}

#[test]
fn bytes_decode_to_keys() {
    assert_eq!(
        keys(b"a\xc3\xa4\r\x7f\t"),
        [
            Key::Char('a'),
            Key::Char('ä'),
            Key::Enter,
            Key::Backspace,
            Key::Tab
        ]
    );
    assert_eq!(
        keys(b"\x1b[A\x1b[B\x1b[C\x1b[D\x1b[H\x1b[F\x1bOH\x1bOF\x1b[3~\x1b[1~\x1b[4~"),
        [
            Key::Up,
            Key::Down,
            Key::Right,
            Key::Left,
            Key::Home,
            Key::End,
            Key::Home,
            Key::End,
            Key::Delete,
            Key::Home,
            Key::End
        ]
    );
    assert_eq!(
        keys(b"\x01\x05\x02\x06\x03\x04\x0b\x15\x17\x10\x0e"),
        [
            Key::Home,
            Key::End,
            Key::Left,
            Key::Right,
            Key::Interrupt,
            Key::EndOfInput,
            Key::KillToEnd,
            Key::KillToStart,
            Key::KillWord,
            Key::Up,
            Key::Down
        ]
    );
    // A modified arrow is the arrow; a sequence it does not know is one
    // key.
    assert_eq!(keys(b"\x1b[1;5C\x1b[5~"), [Key::Right, Key::Unknown]);
    // A key cut short waits for its rest.
    assert_eq!(decode(b"\x1b["), None);
    assert_eq!(decode(b"\xc3"), None);
}

#[test]
fn keys_edit_the_line() {
    use Key::*;
    let mut k = chars("let x = 1");
    k.extend([
        Home,
        Right,
        Right,
        Right,
        Char('s'),
        End,
        Backspace,
        Char('2'),
    ]);
    let (line, outcomes) = typed(&k, &[]);
    assert_eq!(line.text(), "lets x = 2");
    assert!(outcomes.iter().all(|o| *o == Outcome::Edited));

    let mut k = chars("one two three");
    k.extend([
        KillWord,
        Left,
        Left,
        KillToEnd,
        Home,
        Delete,
        Right,
        KillToStart,
    ]);
    let (line, _) = typed(&k, &[]);
    assert_eq!(line.text(), "e tw");
    assert_eq!(line.cursor, 0);

    let (_, outcomes) = typed(&[Char('x'), Enter], &[]);
    assert_eq!(outcomes[1], Outcome::Done);
    let (_, outcomes) = typed(&[Char('x'), Interrupt], &[]);
    assert_eq!(outcomes[1], Outcome::Dropped);
    // Ctrl-D ends only an empty line; otherwise it deletes.
    let (line, outcomes) = typed(&[Char('x'), Left, EndOfInput, EndOfInput], &[]);
    assert_eq!(line.text(), "");
    assert_eq!(outcomes[2..], [Outcome::Edited, Outcome::Ended]);
}

#[test]
fn up_and_down_walk_the_history() {
    use Key::*;
    let history = ["first".to_string(), "second".to_string()];
    let mut k = chars("draft");
    k.push(Up);
    let (line, _) = typed(&k, &history);
    assert_eq!(line.text(), "second");
    k.extend([Up, Up]);
    let (line, _) = typed(&k, &history);
    assert_eq!(line.text(), "first");
    k.extend([Down, Down]);
    let (line, _) = typed(&k, &history);
    // Past the newest entry, the line as it was.
    assert_eq!(line.text(), "draft");
    assert_eq!(line.cursor, 5);
    let (line, _) = typed(&[Down], &history);
    assert_eq!(line.text(), "");
}

#[test]
fn tab_completes_a_name() {
    use Key::*;
    let mut k = chars("x + to");
    k.push(Tab);
    let (line, outcomes) = typed(&k, &[]);
    assert_eq!(line.text(), "x + total");
    assert_eq!(outcomes.last(), Some(&Outcome::Edited));
    // The name before the cursor, inside the line.
    let mut k = chars("ta + 1");
    k.extend([Home, Right, Right, Tab]);
    let (line, _) = typed(&k, &[]);
    assert_eq!(line.text(), "tally + 1");
    assert_eq!(line.cursor, 5);
    // Several names: what they share, and the list.
    let (line, outcomes) = typed(&[Char('t'), Tab], &[]);
    assert_eq!(line.text(), "t");
    assert_eq!(
        outcomes.last(),
        Some(&Outcome::Choices(vec![
            "total".into(),
            "tally".into(),
            "type".into()
        ]))
    );
    let (line, _) = typed(&[Char('q'), Tab], &[]);
    assert_eq!(line.text(), "q");
}
