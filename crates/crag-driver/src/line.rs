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

//! The plain REPL's input (Implementation Plan §11.6.2).
//!
//! The plain REPL runs only when standard input or output is not a terminal,
//! such as a pipe: on a terminal `crag` opens the UI instead. So it reads
//! plain lines and shows no prompt.

use std::io::BufRead;

use crate::repl::is_complete;

/// Reads an input: lines until the parser finds it complete, or an empty
/// line ends it as it is. None when the input ended.
pub fn read_input(input: &mut impl BufRead) -> Option<String> {
    let mut text = String::new();
    loop {
        let mut line = String::new();
        match input.read_line(&mut line) {
            Ok(0) | Err(_) => return (!text.trim().is_empty()).then_some(text),
            Ok(_) => {}
        }
        let line = line.trim_end_matches(['\n', '\r']);
        if !text.is_empty() {
            text.push('\n');
        }
        text += line;
        if text.trim().is_empty() {
            text.clear();
            continue;
        }
        if line.trim().is_empty() || is_complete(&text) {
            return Some(text.trim_end().to_string());
        }
    }
}
