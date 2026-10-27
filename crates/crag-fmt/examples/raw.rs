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

//! Prints the layout of a file without the formatter's check, and where
//! its shape differs from the file's: `raw <file> [width]`.

fn main() {
    let path = std::env::args().nth(1).expect("usage: raw <file> [width]");
    let width = std::env::args()
        .nth(2)
        .map_or(crag_fmt::WIDTH, |w| w.parse().unwrap());
    let text = std::fs::read_to_string(path).unwrap();
    let out = crag_fmt::format_to(&text, None, width)
        .unwrap_or_else(|_| crag_fmt::unchecked(&text, None).unwrap());
    print!("{out}");
    let before = crag_fmt::shape_of(&text).unwrap();
    match crag_fmt::shape_of(&out) {
        Ok(after) if after == before => eprintln!("same shape"),
        Ok(after) => {
            let at = before
                .bytes()
                .zip(after.bytes())
                .position(|(a, b)| a != b)
                .unwrap_or(0);
            let from = at.saturating_sub(120);
            eprintln!("before: …{}", &before[from..(at + 120).min(before.len())]);
            eprintln!("after:  …{}", &after[from..(at + 120).min(after.len())]);
        }
        Err(e) => eprintln!("output does not parse: {e:?}"),
    }
}
