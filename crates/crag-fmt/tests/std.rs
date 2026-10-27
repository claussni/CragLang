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

//! The standard library is kept formatted.

use std::path::Path;

#[test]
fn the_standard_library_is_formatted() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    files.sort();
    for path in files {
        let text = std::fs::read_to_string(&path).unwrap();
        let once =
            crag_fmt::format(&text, None).unwrap_or_else(|e| panic!("{}: {e:?}", path.display()));
        assert_eq!(
            once,
            text,
            "{} is not formatted; run `crag fmt` on it",
            path.display()
        );
    }
}
