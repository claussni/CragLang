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
//! §20); `run`, `test` and `fmt` (§20.6) work on the project in the
//! current directory, as the REPL does when there is one. `crag __image` is not
//! for people: the session manager starts images with it (Implementation
//! Plan §11.6.1).

use std::io::IsTerminal;
use std::process::ExitCode;

use crag_driver::{crag_fmt, crag_repl, crag_run, crag_test};

const USAGE: &str = "usage: crag
       crag new <name> [--lib]
       crag add <package> [version]
       crag remove <package>
       crag upgrade <package> [--version=V] | crag upgrade all
       crag outdated [--json]
       crag deps [--json]
       crag sbom diff [--json] | crag sbom regenerate
       crag package
       crag publish <registry>
       crag registry new <name> <folder> | add <name> <folder> | list | remove <name>
       crag run [argument...]
       crag test [filter]
       crag fmt [--check] [all | - | file...]
       crag lsp
       crag dap
";

fn main() -> ExitCode {
    crag_runtime::abort_on_panic();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = std::path::Path::new(".");
    // What compiles keeps its code in the persisted store.
    let compiles = matches!(
        args.first().map(String::as_str),
        None | Some("run" | "test" | "dap" | "package" | "publish")
    );
    if compiles {
        crag_driver::persist::install();
    }
    let status = match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        // On a terminal the UI; else the plain REPL, as scripts use it.
        [] if std::io::stdin().is_terminal() && std::io::stdout().is_terminal() => {
            ExitCode::from(crag_driver::crag_ui(root))
        }
        [] => ExitCode::from(crag_repl(root)),
        ["run", ref rest @ ..] => {
            // The program sees what follows `run` as its arguments (§19.7).
            crag_runtime::set_program_args(rest.iter().map(|a| a.as_bytes().to_vec()).collect());
            ExitCode::from(crag_run(root, &mut std::io::stderr()))
        }
        ["test"] => test(root, None),
        ["test", filter] => test(root, Some(filter)),
        ["fmt", ref rest @ ..] => ExitCode::from(crag_fmt(root, rest, &mut std::io::stderr())),
        [
            command @ ("new" | "add" | "remove" | "upgrade" | "outdated" | "deps" | "sbom"
            | "package" | "publish" | "registry"),
            ref rest @ ..,
        ] => package_command(root, command, rest),
        ["lsp"] => ExitCode::from(crag_driver::lsp::serve(std::io::stdin(), std::io::stdout())),
        ["dap"] => dap(),
        [crag_session::host::IMAGE_ARG, kind, socket] => image(kind, socket),
        _ => {
            eprint!("{USAGE}");
            ExitCode::from(2)
        }
    };
    if compiles {
        crag_driver::persist::finish(root);
    }
    status
}

/// A command of the package manager, with the shell's arguments.
fn package_command(root: &std::path::Path, command: &str, rest: &[&str]) -> ExitCode {
    use crag_driver::packages::{Args, command as command_of};
    let Some((spec, run)) = command_of(command) else {
        unreachable!("main matches the commands");
    };
    let args = match Args::shell(rest, spec) {
        Ok(args) => args,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    ExitCode::from(run(root, &args, &mut std::io::stdout()))
}

fn test(root: &std::path::Path, filter: Option<&str>) -> ExitCode {
    let report = crag_test(root, filter, &mut std::io::stdout());
    ExitCode::from(if report.success() { 0 } else { 1 })
}

/// `crag dap`. The protocol keeps the standard output it was started with;
/// file descriptor 1 then refers to standard error, so the images the
/// adapter starts, which inherit it, cannot write into the protocol.
fn dap() -> ExitCode {
    use std::os::fd::FromRawFd;
    let command = match crag_session::ImageCommand::current() {
        Ok(command) => command,
        Err(e) => {
            eprintln!("crag dap: cannot find the crag binary: {e}");
            return ExitCode::from(1);
        }
    };
    // SAFETY: duplicating and replacing descriptors of this process, which
    // nothing else uses yet.
    let protocol = unsafe {
        let protocol = libc::dup(1);
        if protocol < 0 || libc::dup2(2, 1) < 0 {
            eprintln!("crag dap: {}", std::io::Error::last_os_error());
            return ExitCode::from(1);
        }
        std::fs::File::from_raw_fd(protocol)
    };
    ExitCode::from(crag_driver::dap::serve(std::io::stdin(), protocol, command))
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
