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

//! The `crag` command. M1 has `run` and `test` (Specification §20.6); they
//! work on the project in the current directory.

use std::process::ExitCode;

use crag_driver::{crag_run, crag_test};

const USAGE: &str = "usage: crag run\n       crag test [filter]\n";

fn main() -> ExitCode {
    crag_runtime::abort_on_panic();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = std::path::Path::new(".");
    match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        ["run"] => ExitCode::from(crag_run(root, &mut std::io::stderr())),
        ["test"] => test(root, None),
        ["test", filter] => test(root, Some(filter)),
        _ => {
            eprint!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

fn test(root: &std::path::Path, filter: Option<&str>) -> ExitCode {
    let report = crag_test(root, filter, &mut std::io::stdout());
    ExitCode::from(if report.success() { 0 } else { 1 })
}
