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

use std::collections::HashMap;
use std::io;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::Arc;

use crag_abi::{CodeObject, FuncId, RuntimeFn, SlotKey, TypeDescriptor};
use crag_loader::{CodeArena, SymbolTable, load, replace_group};
use crag_runtime::{CodeMap, Fiber, FiberConfig, FiberState, Types, Worker};

use crate::host::ImageKind;
use crate::protocol::{
    Message, PROTOCOL_VERSION, ShippedFunction, Stub, read_message, write_message,
};

/// The address range reserved for an image's code.
const ARENA: usize = 1 << 30;

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
            } => match self.load(types, stubs, functions) {
                Ok(()) => {
                    for key in reset {
                        self.symbols.cells().reset(key);
                    }
                    Message::Loaded
                }
                Err(why) => Message::Failed(why),
            },
            Message::Run(func) => self.run(func),
            other => Message::Failed(format!("an image does not take {other:?}")),
        })
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

    /// Runs a loaded function without parameters on a fiber of its own.
    fn run(&mut self, func: FuncId) -> Message {
        let Some(&(entry, params, returns)) = self.functions.get(&func) else {
            return Message::Failed(format!("function {} is not loaded", func.0));
        };
        if params != 0 {
            return Message::Failed(format!("function {} takes parameters", func.0));
        }
        let Some(&stub) = self.stubs.get(&(0, returns)) else {
            return Message::Failed(format!("no entry stub returns {returns} words"));
        };
        // SAFETY: the host compiled the stub for the function's words, and
        // both stay loaded while the image exists, which outlives the fiber.
        let fiber = unsafe { Fiber::new(stub, entry, &[], FiberConfig::default()) };
        let mut fiber = match fiber {
            Ok(fiber) => fiber,
            Err(e) => return Message::Failed(format!("cannot map a fiber's stack: {e}")),
        };
        match self.worker.resume(&mut fiber) {
            FiberState::Finished => {
                Message::Finished(fiber.results().expect("finished")[..returns as usize].to_vec())
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
        }
    }
}

/// Connects to the host at `socket`, says `Hello` and answers messages
/// until the host says `Shutdown` or goes away.
pub fn serve(kind: ImageKind, socket: &Path) -> io::Result<()> {
    let ImageKind::Scratch = kind;
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
