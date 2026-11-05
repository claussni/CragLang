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
//! current directory, as the REPL does when there is one, and the
//! commands of an area come after its name: `crag package add`, `crag
//! registry list`. `crag __image` is not
//! for people: the session manager starts images with it (Implementation
//! Plan §11.6.1).

use std::io::IsTerminal;
use std::process::ExitCode;

use crag_driver::{crag_fmt, crag_repl, crag_run, crag_test};

const USAGE: &str = "usage: crag
       crag build [--skip-tests]
       crag run [--budgets <dir>] [argument...]
       crag test [filter]
       crag fmt [--check] [all | - | file...]
       crag lmt new <document>
       crag package new <name> [--lib]
       crag package add <package> [version]
       crag package remove <package>
       crag package upgrade <package> [--version=V] | crag package upgrade all
       crag package outdated [--json]
       crag package deps [--json]
       crag package sbom diff [--json] | crag package sbom regenerate
       crag package pack
       crag package publish <registry>
       crag registry new <name> <folder> | add <name> <folder> | list | remove <name>
       crag lsp
       crag dap
       crag mcp [--allow-io]
";

fn main() -> ExitCode {
    crag_runtime::abort_on_panic();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = std::path::Path::new(".");
    // What compiles keeps its code in the persisted store.
    let words: Vec<&str> = args.iter().map(String::as_str).collect();
    let compiles = matches!(
        words[..],
        [] | ["build" | "run" | "test" | "dap" | "mcp", ..] | ["package", "pack" | "publish", ..]
    );
    if compiles {
        crag_driver::persist::install();
    }
    let status = match words[..] {
        // On a terminal the UI; else the plain REPL, as scripts use it.
        [] if std::io::stdin().is_terminal() && std::io::stdout().is_terminal() => {
            ExitCode::from(crag_driver::crag_ui(root))
        }
        [] => ExitCode::from(crag_repl(root)),
        ["run", "--budgets"] => {
            eprintln!("error: `--budgets` needs a directory");
            ExitCode::from(1)
        }
        ["run", ref rest @ ..] => {
            // The budget directory, else `CRAG_BUDGETS` (§18.7).
            let (budgets, rest) = match rest {
                ["--budgets", dir, rest @ ..] => (Some(std::path::Path::new(*dir)), rest),
                rest => (None, rest),
            };
            match crag_runtime::budgets::init(budgets) {
                Err(why) => {
                    eprintln!("error: {why}");
                    ExitCode::from(1)
                }
                Ok(()) => {
                    // The program sees what follows as its arguments (§19.7).
                    let args = rest.iter().map(|a| a.as_bytes().to_vec()).collect();
                    crag_runtime::set_program_args(args);
                    ExitCode::from(crag_run(root, &mut std::io::stderr()))
                }
            }
        }
        ["build", ref rest @ ..] => build(root, rest),
        ["test"] => test(root, None),
        ["test", filter] => test(root, Some(filter)),
        ["lmt", "new", document] => ExitCode::from(crag_driver::lmt::crag_lmt_new(
            std::path::Path::new(document),
            &mut std::io::stderr(),
        )),
        ["fmt", ref rest @ ..] => ExitCode::from(crag_fmt(root, rest, &mut std::io::stderr())),
        ["package", command, ref rest @ ..]
            if crag_driver::packages::is_package_command(command) =>
        {
            package_command(root, command, rest)
        }
        ["registry", ref rest @ ..] => package_command(root, "registry", rest),
        ["lsp"] => ExitCode::from(crag_driver::lsp::serve(std::io::stdin(), std::io::stdout())),
        ["dap"] => dap(),
        ["mcp"] => mcp(false),
        ["mcp", "--allow-io"] => mcp(true),
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

fn build(root: &std::path::Path, rest: &[&str]) -> ExitCode {
    use crag_driver::commands::Args;
    let args = match Args::shell(rest, crag_driver::build::BUILD) {
        Ok(args) => args,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    ExitCode::from(crag_driver::crag_build(root, &args, &mut std::io::stdout()))
}

fn test(root: &std::path::Path, filter: Option<&str>) -> ExitCode {
    let report = crag_test(root, filter, &mut std::io::stdout());
    ExitCode::from(if report.success() { 0 } else { 1 })
}

/// `crag dap`, the debug adapter.
fn dap() -> ExitCode {
    let Some((protocol, command)) = protocol_output("dap") else {
        return ExitCode::from(1);
    };
    ExitCode::from(crag_driver::dap::serve(std::io::stdin(), protocol, command))
}

/// `crag mcp`, the agent server; with `--allow-io` the user lets `eval`
/// run code with the `io` effect (Specification §20.10).
fn mcp(io_eval: bool) -> ExitCode {
    let Some((protocol, command)) = protocol_output("mcp") else {
        return ExitCode::from(1);
    };
    let grants = crag_driver::agent::Grants {
        io_eval,
        yes: false,
    };
    ExitCode::from(crag_driver::agent::serve(protocol, command, grants))
}

/// For a server whose images print: the standard output it was started
/// with, for the protocol, and the command that starts images. File
/// descriptor 1 then refers to standard error, so the images it starts,
/// which inherit it, cannot write into the protocol.
fn protocol_output(name: &str) -> Option<(std::fs::File, crag_session::ImageCommand)> {
    use std::os::fd::FromRawFd;
    let command = match crag_session::ImageCommand::current() {
        Ok(command) => command,
        Err(e) => {
            eprintln!("crag {name}: cannot find the crag binary: {e}");
            return None;
        }
    };
    // SAFETY: duplicating and replacing descriptors of this process, which
    // nothing else uses yet.
    let protocol = unsafe {
        let protocol = libc::dup(1);
        if protocol < 0 || libc::dup2(2, 1) < 0 {
            eprintln!("crag {name}: {}", std::io::Error::last_os_error());
            return None;
        }
        std::fs::File::from_raw_fd(protocol)
    };
    Some((protocol, command))
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
