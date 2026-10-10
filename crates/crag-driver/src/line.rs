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

//! The REPL's line editor (Implementation Plan §11.6.2).
//!
//! On a terminal, the editor puts it in raw mode while a line is read and
//! back between lines, so a run gets Ctrl-C as SIGINT. It decodes the keys,
//! edits the line, and draws it again after each key: one row, which a line
//! wider than the terminal overflows. The keys are those of most shells:
//! arrows, Home and End, Delete and Backspace, Ctrl-A, -E, -K, -U and -W, Up
//! and Down for the history, Tab to complete a name, Ctrl-C to drop the
//! input and Ctrl-D to end on an empty line. On anything else, such as a
//! pipe, it reads plain lines and shows no prompt.

use std::io::{self, BufRead, Read, Write};

use crate::repl::is_complete;

/// A key, as decoded from what the terminal sends.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Key {
    Char(char),
    Enter,
    Backspace,
    Delete,
    Left,
    Right,
    Home,
    End,
    Up,
    Down,
    Tab,
    /// Ctrl-C.
    Interrupt,
    /// Ctrl-D.
    EndOfInput,
    /// Ctrl-K: delete to the end of the line.
    KillToEnd,
    /// Ctrl-U: delete to the start of the line.
    KillToStart,
    /// Ctrl-W: delete the word before the cursor.
    KillWord,
    /// A sequence the editor does not know.
    Unknown,
}

/// The first key in `bytes` and how many bytes it took; none when the
/// bytes end inside a key.
pub fn decode(bytes: &[u8]) -> Option<(Key, usize)> {
    let &first = bytes.first()?;
    Some(match first {
        b'\r' | b'\n' => (Key::Enter, 1),
        0x7f | 0x08 => (Key::Backspace, 1),
        b'\t' => (Key::Tab, 1),
        0x01 => (Key::Home, 1),
        0x02 => (Key::Left, 1),
        0x03 => (Key::Interrupt, 1),
        0x04 => (Key::EndOfInput, 1),
        0x05 => (Key::End, 1),
        0x06 => (Key::Right, 1),
        0x0b => (Key::KillToEnd, 1),
        0x0e => (Key::Down, 1),
        0x10 => (Key::Up, 1),
        0x15 => (Key::KillToStart, 1),
        0x17 => (Key::KillWord, 1),
        0x1b => return escape(bytes),
        _ if first < 0x20 => (Key::Unknown, 1),
        _ => {
            let len = match first {
                0xc0..=0xdf => 2,
                0xe0..=0xef => 3,
                0xf0..=0xf7 => 4,
                _ => 1,
            };
            let text = bytes.get(..len)?;
            match std::str::from_utf8(text) {
                Ok(s) => (Key::Char(s.chars().next().expect("one char")), len),
                Err(_) => (Key::Unknown, 1),
            }
        }
    })
}

/// An escape sequence: `ESC [ …` or `ESC O …`.
fn escape(bytes: &[u8]) -> Option<(Key, usize)> {
    let &kind = bytes.get(1)?;
    if kind != b'[' && kind != b'O' {
        return Some((Key::Unknown, 1));
    }
    // Parameters, then the final byte.
    let end = bytes[2..].iter().position(|b| (0x40..=0x7e).contains(b))? + 2;
    let key = match (&bytes[2..end], bytes[end]) {
        (_, b'A') => Key::Up,
        (_, b'B') => Key::Down,
        (_, b'C') => Key::Right,
        (_, b'D') => Key::Left,
        (_, b'H') | (b"1" | b"7", b'~') => Key::Home,
        (_, b'F') | (b"4" | b"8", b'~') => Key::End,
        (b"3", b'~') => Key::Delete,
        _ => Key::Unknown,
    };
    Some((key, end + 1))
}

/// What a key did to the line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The line changed, or the cursor moved.
    Edited,
    /// Enter: the line is done.
    Done,
    /// Ctrl-C: the input is dropped.
    Dropped,
    /// Ctrl-D on an empty line: no more input.
    Ended,
    /// Tab found several names: they are shown below the line.
    Choices(Vec<String>),
}

/// A line being edited, and where it is in the history.
#[derive(Debug, Default)]
pub struct Line {
    pub text: Vec<char>,
    /// The index of the char the cursor is before.
    pub cursor: usize,
    /// The history entry shown, counted from the newest, and the line as
    /// it was before Up.
    recalled: Option<(usize, Vec<char>)>,
}

impl Line {
    pub fn text(&self) -> String {
        self.text.iter().collect()
    }

    /// Applies a key. `complete` gives the names that start with a prefix.
    pub fn key(
        &mut self,
        key: Key,
        history: &[String],
        complete: &dyn Fn(&str) -> Vec<String>,
    ) -> Outcome {
        match key {
            Key::Char(c) => {
                self.text.insert(self.cursor, c);
                self.cursor += 1;
            }
            Key::Enter => return Outcome::Done,
            Key::Interrupt => return Outcome::Dropped,
            Key::EndOfInput if self.text.is_empty() => return Outcome::Ended,
            Key::EndOfInput | Key::Delete => {
                if self.cursor < self.text.len() {
                    self.text.remove(self.cursor);
                }
            }
            Key::Backspace => {
                if self.cursor > 0 {
                    self.cursor -= 1;
                    self.text.remove(self.cursor);
                }
            }
            Key::Left => self.cursor = self.cursor.saturating_sub(1),
            Key::Right => self.cursor = (self.cursor + 1).min(self.text.len()),
            Key::Home => self.cursor = 0,
            Key::End => self.cursor = self.text.len(),
            Key::KillToEnd => self.text.truncate(self.cursor),
            Key::KillToStart => {
                self.text.drain(..self.cursor);
                self.cursor = 0;
            }
            Key::KillWord => {
                let mut start = self.cursor;
                while start > 0 && self.text[start - 1].is_whitespace() {
                    start -= 1;
                }
                while start > 0 && !self.text[start - 1].is_whitespace() {
                    start -= 1;
                }
                self.text.drain(start..self.cursor);
                self.cursor = start;
            }
            Key::Up => self.recall(history, 1),
            Key::Down => self.recall(history, -1),
            Key::Tab => return self.complete(complete),
            Key::Unknown => {}
        }
        Outcome::Edited
    }

    /// Shows an older (`step` 1) or newer (-1) history entry; past the
    /// newest, the line as it was.
    fn recall(&mut self, history: &[String], step: isize) {
        let at = match &self.recalled {
            Some((at, _)) => *at as isize + step,
            None if step > 0 => 0,
            None => return,
        };
        if at >= history.len() as isize {
            return;
        }
        if at < 0 {
            let (_, saved) = self.recalled.take().expect("recalled");
            self.text = saved;
        } else {
            let saved = match self.recalled.take() {
                Some((_, saved)) => saved,
                None => std::mem::take(&mut self.text),
            };
            self.text = history[history.len() - 1 - at as usize].chars().collect();
            self.recalled = Some((at as usize, saved));
        }
        self.cursor = self.text.len();
    }

    /// Completes the name before the cursor: with the one name that fits,
    /// or with what all that fit share, listing them.
    fn complete(&mut self, complete: &dyn Fn(&str) -> Vec<String>) -> Outcome {
        let mut start = self.cursor;
        while start > 0 && (self.text[start - 1].is_alphanumeric() || self.text[start - 1] == '_') {
            start -= 1;
        }
        let prefix: String = self.text[start..self.cursor].iter().collect();
        let names = complete(&prefix);
        let Some(first) = names.first() else {
            return Outcome::Edited;
        };
        let shared = names.iter().fold(first.clone(), |shared, name| {
            shared
                .chars()
                .zip(name.chars())
                .take_while(|(a, b)| a == b)
                .map(|(a, _)| a)
                .collect()
        });
        let rest: Vec<char> = shared.chars().skip(prefix.chars().count()).collect();
        let len = rest.len();
        self.text.splice(self.cursor..self.cursor, rest);
        self.cursor += len;
        match names.len() {
            1 => Outcome::Edited,
            _ => Outcome::Choices(names),
        }
    }
}

/// How a line ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Got {
    Line(String),
    /// Ctrl-C dropped it.
    Dropped,
    /// The input ended.
    Ended,
}

/// The editor: the history and the terminal, if input comes from one.
pub struct LineEditor {
    pub history: Vec<String>,
    terminal: Option<Terminal>,
    input: io::StdinLock<'static>,
}

impl LineEditor {
    pub fn new() -> LineEditor {
        LineEditor {
            history: Vec::new(),
            terminal: Terminal::open(),
            input: io::stdin().lock(),
        }
    }

    /// Reads one line, after the prompt on a terminal.
    pub fn read_line(
        &mut self,
        prompt: &str,
        complete: &dyn Fn(&str) -> Vec<String>,
    ) -> io::Result<Got> {
        let Some(terminal) = &self.terminal else {
            let mut line = String::new();
            return Ok(match self.input.read_line(&mut line)? {
                0 => Got::Ended,
                _ => Got::Line(line.trim_end_matches(['\n', '\r']).to_string()),
            });
        };
        let _raw = terminal.raw()?;
        let mut out = io::stdout().lock();
        let mut line = Line::default();
        let mut pending: Vec<u8> = Vec::new();
        draw(&mut out, prompt, &line)?;
        loop {
            let mut buf = [0u8; 64];
            let n = self.input.read(&mut buf)?;
            if n == 0 {
                return Ok(Got::Ended);
            }
            pending.extend(&buf[..n]);
            while let Some((key, len)) = decode(&pending) {
                pending.drain(..len);
                match line.key(key, &self.history, complete) {
                    Outcome::Edited => {}
                    Outcome::Done => {
                        write!(out, "\r\n")?;
                        return Ok(Got::Line(line.text()));
                    }
                    Outcome::Dropped => {
                        write!(out, "^C\r\n")?;
                        return Ok(Got::Dropped);
                    }
                    Outcome::Ended => {
                        write!(out, "\r\n")?;
                        return Ok(Got::Ended);
                    }
                    Outcome::Choices(names) => write!(out, "\r\n{}\r\n", names.join("  "))?,
                }
                draw(&mut out, prompt, &line)?;
            }
        }
    }
}

impl Default for LineEditor {
    fn default() -> LineEditor {
        LineEditor::new()
    }
}

/// Draws the line again: the prompt and the text, the rest of the row
/// cleared, the cursor in place.
fn draw(out: &mut impl Write, prompt: &str, line: &Line) -> io::Result<()> {
    write!(out, "\r{prompt}{}\x1b[K", line.text())?;
    let back = line.text.len() - line.cursor;
    if back > 0 {
        write!(out, "\x1b[{back}D")?;
    }
    out.flush()
}

/// Reads an input: lines until the parser finds it complete, or an empty
/// line ends it as it is. None when the input ended.
pub fn read_input(
    editor: &mut LineEditor,
    complete: &dyn Fn(&str) -> Vec<String>,
) -> Option<String> {
    let mut text = String::new();
    loop {
        let prompt = if text.is_empty() { "crag> " } else { "  ... " };
        match editor.read_line(prompt, complete) {
            Ok(Got::Line(line)) => {
                if !text.is_empty() {
                    text.push('\n');
                }
                text += &line;
                if text.trim().is_empty() {
                    text.clear();
                    continue;
                }
                if line.trim().is_empty() || is_complete(&text) {
                    let input = text.trim_end().to_string();
                    if editor.history.last() != Some(&input) {
                        editor.history.push(input.clone());
                    }
                    return Some(input);
                }
            }
            Ok(Got::Dropped) => text.clear(),
            Ok(Got::Ended) | Err(_) => {
                return (!text.trim().is_empty()).then_some(text);
            }
        }
    }
}

/// Standard input when it is a terminal, with its settings.
struct Terminal {
    cooked: libc::termios,
}

/// Raw mode while it lives.
struct Raw<'a>(&'a Terminal);

impl Terminal {
    fn open() -> Option<Terminal> {
        // SAFETY: reads the settings of standard input into a zeroed struct.
        unsafe {
            if libc::isatty(libc::STDIN_FILENO) == 0 || libc::isatty(libc::STDOUT_FILENO) == 0 {
                return None;
            }
            let mut cooked: libc::termios = std::mem::zeroed();
            (libc::tcgetattr(libc::STDIN_FILENO, &mut cooked) == 0).then_some(Terminal { cooked })
        }
    }

    /// Keys come one by one and unechoed, Ctrl-C as a key; output is
    /// processed as before.
    fn raw(&self) -> io::Result<Raw<'_>> {
        let mut raw = self.cooked;
        raw.c_lflag &= !(libc::ICANON | libc::ECHO | libc::ISIG | libc::IEXTEN);
        raw.c_iflag &= !(libc::IXON | libc::ICRNL | libc::INLCR);
        raw.c_cc[libc::VMIN] = 1;
        raw.c_cc[libc::VTIME] = 0;
        // SAFETY: sets the settings of standard input from a valid struct.
        if unsafe { libc::tcsetattr(libc::STDIN_FILENO, libc::TCSADRAIN, &raw) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(Raw(self))
    }
}

impl Drop for Raw<'_> {
    fn drop(&mut self) {
        // SAFETY: restores the settings `Terminal::open` read.
        unsafe { libc::tcsetattr(libc::STDIN_FILENO, libc::TCSADRAIN, &self.0.cooked) };
    }
}
