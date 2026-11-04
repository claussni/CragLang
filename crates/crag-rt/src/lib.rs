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

//! The runtime archive (Implementation Plan §11.10.4): the runtime and the
//! start of a release executable, built as a static library for each
//! target, which the linker combines with a program's object (§11.10.5).
//!
//! The archive defines the runtime's functions under the symbols release
//! code calls them by, `crag_abi::RuntimeFn::symbol`, and the C `main`.
//! `main` reads the table the object writer put at `crag_code`
//! (`crag_abi::release`), builds the code map and the type descriptors
//! from it, and runs the root `crag_main` as the scheduler's root task, as
//! `crag run` runs `main` (Specification §19.7): its arguments are the
//! program's, a result of `ExitCode` is the exit status, and a trap is
//! reported on standard error with the status 70.
//!
//! The archive is built for `x86_64-unknown-linux-musl`, whose C library
//! and start files come with the Rust target, so executables link
//! statically and need nothing of the host they are built on.
//!
//! A program that runs received code links with the archive of
//! `crag-rt-receive` instead, this crate with the feature `receive`: it
//! holds the receiver of code (Implementation Plan §11.10.9), which `main`
//! makes from the bundle in the table and gives the scheduler.

use std::ffi::{CStr, c_char, c_int};
use std::sync::Arc;

use crag_abi::release::{HEADER, Receiving, Table};
use crag_abi::{CodeObject, FuncId};
use crag_runtime::{
    CodeMap, Fiber, FiberConfig, FiberState, Scheduler, SchedulerConfig, Trap, Types, record_field,
};

/// The root a release executable starts at.
pub const MAIN: &str = "crag_main";

/// The exit status of a program a trap ended, as `crag run` gives it.
const EXIT_TRAP: c_int = 70;

unsafe extern "C" {
    /// The start of the table the object writer wrote, at the symbol
    /// `crag_abi::release::SYMBOL`.
    static crag_code: [u8; HEADER];
}

/// Starts the program with the arguments after its name.
///
/// # Safety
///
/// Only the C start calls this, with `argc` strings at `argv`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    crag_runtime::abort_on_panic();
    let args = (1..argc.max(1) as usize)
        // SAFETY: as the caller promises.
        .map(|i| unsafe { CStr::from_ptr(*argv.add(i)) }.to_bytes().to_vec())
        .collect();
    crag_runtime::set_program_args(args);
    match run() {
        Ok(status) => status,
        Err(message) => {
            eprintln!("crag: {message}");
            1
        }
    }
}

/// Runs `crag_main` to its end: the exit status.
fn run() -> Result<c_int, String> {
    // SAFETY: the linker placed the table at the symbol, its length in its
    // header, and nothing writes it.
    let table = unsafe {
        let header = &*std::ptr::addr_of!(crag_code);
        let len = Table::len(header)?;
        Table::decode(std::slice::from_raw_parts(header.as_ptr(), len))?
    };
    let root = table
        .roots
        .iter()
        .find(|r| r.name == MAIN)
        .ok_or_else(|| format!("the program has no root {MAIN}"))?;
    let entry = |place: u32| {
        let f = &table.functions[place as usize];
        (f.start + u64::from(f.object.entry)) as usize
    };
    let mut map = CodeMap::new();
    for (n, f) in table.functions.iter().enumerate() {
        let object = CodeObject {
            // SAFETY: the linker placed the function's code there.
            code: unsafe { std::slice::from_raw_parts(f.start as *const u8, f.len as usize) }
                .to_vec(),
            ..f.object.clone()
        };
        map.add(FuncId(n as u32), entry(n as u32), &object);
    }
    // SAFETY: the stubs are part of the executable.
    unsafe { map.set_task_entries(table.task_entries.map(|e| e as usize)) };
    // The budgets of code transport, from `CRAG_BUDGETS` (§18.7).
    crag_runtime::budgets::init(None)?;
    let types = Arc::new(Types::new(table.types.iter().cloned()));
    let scheduler = Scheduler::new(SchedulerConfig::default(), types, Arc::new(map));
    if let Some(receiving) = &table.receiving {
        receive(&scheduler, receiving)?;
    }
    // SAFETY: the stub was compiled for the root's words, and both are part
    // of the executable.
    let fiber = unsafe {
        Fiber::new(
            root.entry as usize,
            entry(root.place),
            &[],
            FiberConfig::default(),
        )
    }
    .map_err(|e| format!("cannot map a stack: {e}"))?;
    scheduler.spawn(fiber);
    let fiber = scheduler.wait().pop().ok_or("the root task did not stop")?;
    match fiber.state() {
        FiberState::Finished => {
            let words = fiber.results().expect("finished");
            // SAFETY: the words are the root's live result, of its shapes.
            let code = unsafe { record_field(&root.shapes, root.result, &words, "code") };
            Ok(code.map_or(0, |w| w[0] as c_int))
        }
        FiberState::Trapped => {
            eprint!("{}", report(&table, fiber.trap().expect("trapped")));
            Ok(EXIT_TRAP)
        }
        state => Err(format!("the root task ended {state:?}")),
    }
}

/// Gives the scheduler the program's receiver of code, made from the
/// bundle the table holds, which shares the cells of the program's values.
#[cfg(feature = "receive")]
fn receive(scheduler: &Scheduler, receiving: &Receiving) -> Result<(), String> {
    let bundle = crag_receive::Bundle::decode(&receiving.bundle)?;
    let cells = receiving
        .cells
        .iter()
        .map(|(value, at)| (value.clone(), *at as usize))
        .collect();
    let receiver = crag_receive::Receiver::new(bundle, cells)
        .map_err(|e| format!("cannot start the receiver of code: {e}"))?;
    receiver.install(scheduler);
    Ok(())
}

/// A program that runs received code is linked with the archive that has
/// the receiver; this one has none.
#[cfg(not(feature = "receive"))]
fn receive(_: &Scheduler, _: &Receiving) -> Result<(), String> {
    Err("the program runs received code, but was linked without its receiver".into())
}

/// A trap as the user sees it: what went wrong, where, and the functions
/// it happened in. Release executables carry no sources, so the place is
/// the module, line and column.
fn report(table: &Table, trap: &Trap) -> String {
    let what = match &trap.detail {
        Some(detail) => format!("{}: {detail}", trap.kind.message()),
        None => trap.kind.message().to_string(),
    };
    let mut out = format!("trap: {what}\n");
    let function = |func: FuncId| table.functions.get(func.0 as usize);
    let module = trap
        .stack
        .first()
        .and_then(|f| function(f.func))
        .map(|f| f.object.module.as_str());
    if let (Some(module), Some(position)) = (module, trap.position) {
        // The origin of the position, in whatever code holds it.
        let at = table.functions.iter().find_map(|f| {
            f.object.origins.iter().find(|o| {
                let of = match (o.inlined as usize).checked_sub(1) {
                    Some(k) => f.object.inlined.get(k).map(|c| c.module.as_str()),
                    None => Some(f.object.module.as_str()),
                };
                o.offset == position && of == Some(module)
            })
        });
        if let Some(at) = at {
            out += &format!(" --> {module}:{}:{}\n", at.line, at.column);
        }
    }
    // Runs of one function, as recursion makes them, are told once.
    let mut k = 0;
    while k < trap.stack.len() {
        let frame = trap.stack[k];
        let run = trap.stack[k..].iter().take_while(|&&f| f == frame).count();
        let mut name = function(frame.func)
            .map_or_else(|| format!("function {}", frame.func.0), |f| f.name.clone());
        if frame.inlined {
            name += " (inlined)";
        }
        out += &match run {
            1 => format!("  in {name}\n"),
            n => format!("  in {name}, {n} frames\n"),
        };
        k += run;
    }
    out
}
