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

//! The `crag` command. Without arguments it opens the REPL (Specification
//! §20); `run` and `test` (§20.6) work on the project in the current
//! directory, as the REPL does when there is one. `crag __image` is not
//! for people: the session manager starts images with it (Implementation
//! Plan §11.6.1).

use std::process::ExitCode;

use crag_driver::{crag_repl, crag_run, crag_test};

const USAGE: &str = "usage: crag\n       crag run\n       crag test [filter]\n";

fn main() -> ExitCode {
    crag_runtime::abort_on_panic();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = std::path::Path::new(".");
    match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        [] => ExitCode::from(crag_repl(root)),
        ["run"] => ExitCode::from(crag_run(root, &mut std::io::stderr())),
        ["test"] => test(root, None),
        ["test", filter] => test(root, Some(filter)),
        [crag_session::host::IMAGE_ARG, kind, socket] => image(kind, socket),
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

fn image(kind: &str, socket: &str) -> ExitCode {
    let Some(kind) = crag_session::ImageKind::from_name(kind) else {
        eprintln!("crag image: no image is called `{kind}`");
        return ExitCode::from(2);
    };
    match crag_session::serve(kind, std::path::Path::new(socket)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("crag image: {e}");
            ExitCode::from(1)
        }
    }
}
