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

//! The image's side: the loop that answers the host (Implementation Plan
//! §11.6.1, §11.6.3).
//!
//! The image only loads code; the host compiles it, entry stubs included.
//! Shipped functions are loaded with the M0 loader, the descriptors of
//! their types join the worker's, and their stack maps join the code map
//! that unwinding reads. A function is run on a fiber of its own through
//! the stub for its words.
//!
//! A function shipped again replaces the code it had (§11.6.4): the new
//! code fills its slot, so every later call reaches it, while frames
//! still running the old code finish there. The old code stays loaded and
//! in the code map.
//!
//! SIGINT interrupts a run (§11.6.2): the image asks the running fiber to
//! pause at its next safepoint, a function entry or a loop's back-edge, and
//! answers `Interrupted`. The fiber is dropped; what its frames held is
//! not released yet. The terminal sends SIGINT to the image together with
//! the host, which ignores it while the REPL runs.

use std::collections::HashMap;
use std::io;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicPtr, Ordering};

use crag_abi::{CodeObject, FuncId, RuntimeFn, Shapes, SlotKey, TypeDescriptor};
use crag_loader::{CodeArena, SymbolTable, load, replace_group};
use crag_runtime::{
    CodeMap, Fiber, FiberConfig, FiberState, PrintLimits, StopHandle, StopReason, Types, Worker,
    decode_value, print_value, release_value,
};

use crate::host::ImageKind;
use crate::protocol::{
    Fill, Message, PROTOCOL_VERSION, ShippedFunction, Stub, read_message, write_message,
};

/// The address range reserved for an image's code.
const ARENA: usize = 1 << 30;

/// The stop handle of the fiber running now, for the SIGINT handler; null
/// between runs. The image has one thread, so the handler never runs while
/// the handle is replaced.
static RUNNING: AtomicPtr<StopHandle> = AtomicPtr::new(std::ptr::null_mut());

extern "C" fn on_interrupt(_signal: libc::c_int) {
    let handle = RUNNING.load(Ordering::SeqCst);
    if !handle.is_null() {
        // SAFETY: the handle lives while it is published; requesting a stop
        // only stores atomically, which a signal handler may do.
        unsafe { (*handle).request_stop(StopReason::Pause) };
    }
}

/// Has SIGINT pause the running fiber. The handler runs on the alternate
/// signal stack the standard library sets up, not on the fiber's, whose
/// margin is small.
fn handle_interrupts() -> io::Result<()> {
    // SAFETY: installs a handler that only does what a handler may.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = on_interrupt as *const () as usize;
        action.sa_flags = libc::SA_ONSTACK | libc::SA_RESTART;
        libc::sigemptyset(&mut action.sa_mask);
        if libc::sigaction(libc::SIGINT, &action, std::ptr::null_mut()) != 0 {
            return Err(io::Error::last_os_error());
        }
    }
    Ok(())
}

/// The code an image has loaded and the worker that runs it.
pub struct Image {
    arena: CodeArena,
    symbols: SymbolTable,
    /// Each function's latest entry and words of parameters and results.
    functions: HashMap<FuncId, (usize, u32, u32)>,
    /// Each entry stub's entry, by words of parameters and results.
    stubs: HashMap<(u32, u32), usize>,
    types: Vec<(u32, TypeDescriptor)>,
    /// Every function loaded, with its entry, for the code map.
    code: Vec<(FuncId, usize, CodeObject)>,
    worker: Worker,
}

impl Image {
    pub fn new() -> io::Result<Image> {
        let mut symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            symbols.define_runtime(func, crag_runtime::runtime_fn_addr(func));
        }
        Ok(Image {
            arena: CodeArena::new(ARENA)?,
            symbols,
            functions: HashMap::new(),
            stubs: HashMap::new(),
            types: Vec::new(),
            code: Vec::new(),
            worker: Worker::new(),
        })
    }

    /// Answers one message from the host; none for `Shutdown`.
    pub fn answer(&mut self, message: Message) -> Option<Message> {
        Some(match message {
            Message::Ping(n) => Message::Pong(n),
            Message::Shutdown => return None,
            Message::Load {
                types,
                stubs,
                functions,
                reset,
                fills,
            } => match self.load(types, stubs, functions) {
                Ok(()) => {
                    for key in reset {
                        self.symbols.cells().reset(key);
                    }
                    match self.fill(fills) {
                        Ok(()) => Message::Loaded,
                        Err(why) => Message::Failed(why),
                    }
                }
                Err(why) => Message::Failed(why),
            },
            Message::Run(func) => match self.run(func) {
                Ok(words) => Message::Finished(words),
                Err(reply) => reply,
            },
            Message::Show { func, shapes, root } => self.show(func, &shapes, root),
            other => Message::Failed(format!("an image does not take {other:?}")),
        })
    }

    /// Fills cells with the values the compiler computed, built on the
    /// worker's heap. A fill that fails leaves its cell as it was and the
    /// rest unfilled.
    fn fill(&mut self, fills: Vec<Fill>) -> Result<(), String> {
        let types = self.worker.types();
        for f in fills {
            if self.symbols.cells().address(f.cell).is_none() {
                return Err(format!("no cell for {:?}", f.cell));
            }
            // SAFETY: the host compiled the image's code and gave its types'
            // descriptors with it, and the shapes describe the same layouts.
            let words =
                unsafe { decode_value(&f.bytes, &f.shapes, f.root, self.worker.heap(), &types) }
                    .map_err(|e| format!("cannot decode the value of {:?}: {}", f.cell, e.0))?;
            self.symbols.cells().fill(f.cell, &words);
        }
        Ok(())
    }

    /// Loads what the host shipped. When it fails, the functions are not
    /// loaded and the types are not added.
    fn load(
        &mut self,
        types: Vec<(u32, TypeDescriptor)>,
        stubs: Vec<Stub>,
        functions: Vec<ShippedFunction>,
    ) -> Result<(), String> {
        for (index, descriptor) in &types {
            if let Some((_, known)) = self.types.iter().find(|(i, _)| i == index)
                && known != descriptor
            {
                return Err(format!("type {index} has another descriptor already"));
            }
        }
        for stub in stubs {
            let shape = (stub.params, stub.returns);
            if !self.stubs.contains_key(&shape) {
                let entry = load(&mut self.arena, &self.symbols, &stub.object)
                    .map_err(|e| format!("cannot load an entry stub: {e}"))?;
                self.stubs.insert(shape, entry.addr());
            }
        }
        let group: Vec<(SlotKey, &CodeObject)> = functions
            .iter()
            .map(|f| {
                let slot = SlotKey {
                    func: f.id,
                    signature: f.signature,
                };
                (slot, &f.object)
            })
            .collect();
        let entries = replace_group(&mut self.arena, &mut self.symbols, &group)
            .map_err(|e| format!("cannot load the code: {e}"))?;
        for (f, entry) in functions.into_iter().zip(entries) {
            self.functions
                .insert(f.id, (entry.addr(), f.params, f.returns));
            self.code.push((f.id, entry.addr(), f.object));
        }
        for t in types {
            if !self.types.contains(&t) {
                self.types.push(t);
            }
        }
        self.worker
            .set_types(Arc::new(Types::new(self.types.iter().cloned())));
        let mut map = CodeMap::new();
        for (func, entry, object) in &self.code {
            map.add(*func, *entry, object);
        }
        self.worker.set_code_map(Arc::new(map));
        Ok(())
    }

    /// Runs a function as `run` does and shows its result, which it then
    /// releases.
    fn show(&mut self, func: FuncId, shapes: &Shapes, root: u32) -> Message {
        let words = match self.run(func) {
            Ok(words) => words,
            Err(reply) => return reply,
        };
        let shape = &shapes.shapes[root as usize];
        if shape.words() as usize != words.len() {
            return Message::Failed(format!(
                "a shape of {} words for a result of {}",
                shape.words(),
                words.len()
            ));
        }
        let types = self.worker.types();
        // SAFETY: the host describes the function's result, which the run
        // left to the image.
        let text = unsafe {
            let text = print_value(&words, shapes, root, &types, PrintLimits::default());
            release_value(self.worker.heap(), &types, &words, shapes, root);
            text
        };
        Message::Shown(text)
    }

    /// Runs a loaded function without parameters on a fiber of its own:
    /// its result words, or the answer that tells how it ended otherwise.
    fn run(&mut self, func: FuncId) -> Result<Vec<u64>, Message> {
        let Some(&(entry, params, returns)) = self.functions.get(&func) else {
            return Err(Message::Failed(format!(
                "function {} is not loaded",
                func.0
            )));
        };
        if params != 0 {
            return Err(Message::Failed(format!(
                "function {} takes parameters",
                func.0
            )));
        }
        let Some(&stub) = self.stubs.get(&(0, returns)) else {
            return Err(Message::Failed(format!(
                "no entry stub returns {returns} words"
            )));
        };
        // SAFETY: the host compiled the stub for the function's words, and
        // both stay loaded while the image exists, which outlives the fiber.
        let fiber = unsafe { Fiber::new(stub, entry, &[], FiberConfig::default()) };
        let mut fiber = match fiber {
            Ok(fiber) => fiber,
            Err(e) => return Err(Message::Failed(format!("cannot map a fiber's stack: {e}"))),
        };
        let handle = Box::new(fiber.stop_handle());
        RUNNING.store(
            &*handle as *const StopHandle as *mut StopHandle,
            Ordering::SeqCst,
        );
        let state = self.worker.resume(&mut fiber);
        RUNNING.store(std::ptr::null_mut(), Ordering::SeqCst);
        drop(handle);
        Err(match state {
            FiberState::Paused => Message::Interrupted,
            FiberState::Finished => {
                return Ok(fiber.results().expect("finished")[..returns as usize].to_vec());
            }
            FiberState::Trapped => {
                let trap = fiber.trap().expect("trapped");
                Message::Trapped {
                    kind: trap.kind,
                    position: trap.position,
                    stack: trap.stack.clone(),
                }
            }
            state => Message::Failed(format!("the fiber stopped as {state:?}")),
        })
    }
}

/// Connects to the host at `socket`, says `Hello` and answers messages
/// until the host says `Shutdown` or goes away.
pub fn serve(kind: ImageKind, socket: &Path) -> io::Result<()> {
    let ImageKind::Scratch = kind;
    handle_interrupts()?;
    let mut image = Image::new()?;
    let mut stream = UnixStream::connect(socket)?;
    write_message(
        &mut stream,
        &Message::Hello {
            version: PROTOCOL_VERSION,
            pid: std::process::id(),
        },
    )?;
    loop {
        let message = match read_message(&mut stream) {
            Ok(message) => message,
            // The host is gone, so nothing is left to answer.
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(e) => return Err(e),
        };
        match image.answer(message) {
            Some(reply) => write_message(&mut stream, &reply)?,
            None => return Ok(()),
        }
    }
}
