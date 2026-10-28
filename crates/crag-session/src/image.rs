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
//! that unwinding reads. A function is run through the stub for its words
//! as the root task of a scheduler, which the run starts and stops, so its
//! tasks run on the scheduler's workers.
//!
//! A function shipped again replaces the code it had (§11.6.4): the new
//! code fills its slot, so every later call reaches it, while frames
//! still running the old code finish there. The old code stays loaded and
//! in the code map.
//!
//! The app image runs the app as `Start` asks and keeps answering while it
//! runs (§11.8.4). A `Load` then replaces code under the running app: the
//! new code is loaded, the app's workers take the code map and
//! descriptors that include it, and only then do its slots point to it,
//! so whatever runs new code can unwind it and free its boxes (§11.8.5).
//!
//! SIGINT interrupts a run (§11.6.2): the image cancels the root task,
//! which stops at its next safepoint, a function entry, a loop's back-edge
//! or a wait, and passes the cancellation to the tasks it started (Plan
//! §11.7.4). The run answers `Interrupted` once they all stopped. The
//! terminal sends SIGINT to the image together with the host, which
//! ignores it while the REPL runs.

use std::collections::HashMap;
use std::io;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use crag_abi::{CodeObject, FuncId, RuntimeFn, Shapes, SlotKey, TypeDescriptor};
use crag_loader::{CodeArena, SymbolTable, load, publish, stage_group};
use crag_runtime::{
    CodeMap, Fiber, FiberConfig, FiberState, PrintLimits, Scheduler, SchedulerConfig, Types,
    Worker, decode_value, print_value, release_value,
};

use crate::host::ImageKind;
use crate::protocol::{
    Fill, Message, PROTOCOL_VERSION, PausedTask, ShippedFunction, Stub, read_message, write_message,
};

/// The address range reserved for an image's code.
const ARENA: usize = 1 << 30;

/// Set by SIGINT. A cancellation takes locks, which a signal handler must
/// not, so the thread that waits for the run cancels it.
static INTERRUPTED: AtomicBool = AtomicBool::new(false);

/// How often the waiting thread looks for an interrupt.
const INTERRUPT_POLL: Duration = Duration::from_millis(20);

/// How long a `Stop` waits for the app's tasks to stop.
const STOP_WAIT: Duration = Duration::from_secs(5);

/// How long a reload waits for the app's workers to take the new tables
/// before new code may be reached.
const TABLES_WAIT: Duration = Duration::from_secs(2);

extern "C" fn on_interrupt(_signal: libc::c_int) {
    INTERRUPTED.store(true, Ordering::SeqCst);
}

/// Has SIGINT interrupt the run. The handler runs on the alternate
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
    /// The code map of everything loaded, with the task entries once the
    /// host shipped their stubs.
    code_map: Arc<CodeMap>,
    /// The worker whose heap holds the values the compiler computed and
    /// the results the image shows.
    worker: Worker,
    /// The app that runs, in the app image.
    app: Option<App>,
    /// The cells of the steps of the code loaded, and the breakpoints:
    /// the cells whose flags are set while no task steps.
    steps: Vec<SlotKey>,
    breaks: Vec<SlotKey>,
    /// Whether every step's flag is set, for a task that steps.
    all_steps: bool,
}

/// The app's run: its scheduler, which keeps running while the image
/// answers the host, and how to cancel its root task.
struct App {
    scheduler: Scheduler,
    cancel: crag_runtime::CancelHandle,
    returns: u32,
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
            code_map: Arc::new(CodeMap::new()),
            worker: Worker::new(),
            app: None,
            steps: Vec::new(),
            breaks: Vec::new(),
            all_steps: false,
        })
    }

    /// Answers one message from the host; none for `Shutdown`.
    pub fn answer(&mut self, message: Message) -> Option<Message> {
        let reply = self.reply(message);
        self.sync_steps();
        reply
    }

    /// Sets every step's flag while a task steps, and only the breakpoints'
    /// otherwise.
    fn sync_steps(&mut self) {
        self.set_all_steps(crag_runtime::debug::stepping());
    }

    fn set_all_steps(&mut self, all: bool) {
        if all == self.all_steps {
            return;
        }
        self.all_steps = all;
        let cells = self.symbols.cells();
        for &key in &self.steps {
            let on = all || self.breaks.contains(&key);
            cells.set_state(key, u64::from(on));
        }
    }

    /// Sets the breakpoints: the flags of their steps' cells.
    fn set_breaks(&mut self, breaks: Vec<(FuncId, u32)>) -> Message {
        let cells = self.symbols.cells();
        for &key in &self.breaks {
            cells.set_state(key, u64::from(self.all_steps));
        }
        self.breaks = breaks
            .iter()
            .map(|&(f, s)| crag_abi::step_cell(f, s))
            .collect();
        for &key in &self.breaks {
            cells.set_state(key, 1);
        }
        crag_runtime::debug::set_breakpoints(breaks);
        Message::Done
    }

    /// Prints the locals of a stopped task's step.
    fn locals(&mut self, task: u64, locals: &[(Shapes, u32)]) -> Message {
        let Some(paused) = crag_runtime::debug::paused()
            .into_iter()
            .find(|p| p.task == task)
        else {
            return Message::Failed(format!("task {task:x} is not stopped"));
        };
        let types = self.worker.types();
        let mut texts = Vec::new();
        let mut at = 0;
        for (shapes, root) in locals {
            let root = *root;
            let words = shapes.shapes[root as usize].words() as usize;
            let Some(slice) = paused.words.get(at..at + words) else {
                return Message::Failed("the locals have fewer words than their shapes".into());
            };
            // SAFETY: the stopped frame holds the values, which the host
            // describes with the shapes of their types.
            let text = unsafe { print_value(slice, shapes, root, &types, PrintLimits::default()) };
            texts.push(text);
            at += words;
        }
        Message::Texts(texts)
    }

    fn reply(&mut self, message: Message) -> Option<Message> {
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
            Message::Start(func) => self.start(func),
            Message::Status => self.status(),
            Message::Stop => self.stop(),
            Message::Breaks(breaks) => self.set_breaks(breaks),
            Message::Pauses => Message::Paused(
                crag_runtime::debug::paused()
                    .into_iter()
                    .map(|p| PausedTask {
                        task: p.task,
                        func: p.func,
                        step: p.step,
                        callers: p.callers,
                    })
                    .collect(),
            ),
            Message::Resume { task, how } => match crag_runtime::debug::Resume::from_index(how) {
                Some(how) => {
                    // The next step may come right away, so a task that
                    // steps finds every flag set before it runs.
                    if how != crag_runtime::debug::Resume::Continue {
                        self.set_all_steps(true);
                    }
                    if crag_runtime::debug::resume(task, how) {
                        Message::Done
                    } else {
                        Message::Failed(format!("task {task:x} is not stopped"))
                    }
                }
                None => Message::Failed(format!("no way of resuming is numbered {how}")),
            },
            Message::Locals { task, locals } => self.locals(task, &locals),
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
        // Loaded, but not reached through the slots until the tables that
        // describe it are everywhere.
        let staged = stage_group(&mut self.arena, &mut self.symbols, &group)
            .map_err(|e| format!("cannot load the code: {e}"))?;
        let entries = staged.entries();
        for (f, entry) in functions.iter().zip(&entries) {
            self.code.push((f.id, entry.addr(), f.object.clone()));
            for reloc in &f.object.relocs {
                if let crag_abi::RelocTarget::Cell(key) = reloc.target
                    && key.signature & crag_abi::STEP_CELL != 0
                    && !self.steps.contains(&key)
                {
                    // A new step's flag starts as the others are.
                    let on = self.all_steps || self.breaks.contains(&key);
                    self.symbols.cells().set_state(key, u64::from(on));
                    self.steps.push(key);
                }
            }
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
        // Tasks start in the stubs for one argument, the task's closure.
        if let [Some(&none), Some(&one), Some(&two)] = [0, 1, 2].map(|r| self.stubs.get(&(1, r))) {
            // SAFETY: the stubs stay loaded as long as the image.
            unsafe { map.set_task_entries([none, one, two]) };
        }
        self.code_map = Arc::new(map);
        self.worker.set_code_map(self.code_map.clone());
        // A running app's workers take the new tables before any of them
        // can reach the new code (Implementation Plan §11.8.5).
        if let Some(app) = &self.app {
            let epoch = app
                .scheduler
                .update_tables(self.worker.types(), self.code_map.clone());
            if !app.scheduler.wait_tables(epoch, TABLES_WAIT) {
                return Err(format!(
                    "the app's workers did not take the new code within {} s",
                    TABLES_WAIT.as_secs()
                ));
            }
        }
        publish(&self.symbols, staged);
        for (f, entry) in functions.into_iter().zip(entries) {
            self.functions
                .insert(f.id, (entry.addr(), f.params, f.returns));
        }
        Ok(())
    }

    /// Starts the app: a loaded function without parameters as the root
    /// task of a scheduler that runs on while the image answers.
    fn start(&mut self, func: FuncId) -> Message {
        if self.app.is_some() {
            return Message::Failed("the app runs already".into());
        }
        let (fiber, returns) = match self.root_fiber(func) {
            Ok(root) => root,
            Err(reply) => return reply,
        };
        let cancel = fiber.cancel_handle();
        let scheduler = Scheduler::new(
            SchedulerConfig::default(),
            self.worker.types(),
            self.code_map.clone(),
        );
        scheduler.spawn(fiber);
        self.app = Some(App {
            scheduler,
            cancel,
            returns,
        });
        Message::Started
    }

    /// How the app is doing: `Running`, or how it ended, once.
    fn status(&mut self) -> Message {
        let Some(app) = &self.app else {
            return Message::Stopped;
        };
        match app.scheduler.wait_timeout(Duration::ZERO) {
            None => Message::Running,
            Some(mut stopped) => {
                let app = self.app.take().expect("an app");
                Self::ended(stopped.pop(), app.returns, false)
            }
        }
    }

    /// Cancels the app and waits, within a bound, for its tasks to stop.
    fn stop(&mut self) -> Message {
        let Some(app) = &self.app else {
            return Message::Stopped;
        };
        // Stopped tasks go on, to be cancelled.
        crag_runtime::debug::release_all();
        app.cancel.cancel();
        match app.scheduler.wait_timeout(STOP_WAIT) {
            Some(_) => {
                self.app = None;
                Message::Stopped
            }
            None => Message::Failed(format!(
                "the app did not stop within {} s",
                STOP_WAIT.as_secs()
            )),
        }
    }

    /// The answer for a root task that stopped.
    fn ended(root: Option<Box<Fiber>>, returns: u32, interrupted: bool) -> Message {
        let Some(fiber) = root else {
            return Message::Failed("the root task is gone".into());
        };
        match fiber.state() {
            FiberState::Trapped if interrupted => Message::Interrupted,
            FiberState::Finished => {
                Message::Finished(fiber.results().expect("finished")[..returns as usize].to_vec())
            }
            FiberState::Trapped => {
                let trap = fiber.trap().expect("trapped");
                Message::Trapped {
                    kind: trap.kind,
                    position: trap.position,
                    stack: trap.stack.clone(),
                    detail: trap.detail.clone(),
                }
            }
            state => Message::Failed(format!("the fiber stopped as {state:?}")),
        }
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

    /// A fiber for a loaded function without parameters, with the words of
    /// its result.
    fn root_fiber(&self, func: FuncId) -> Result<(Box<Fiber>, u32), Message> {
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
        match fiber {
            Ok(fiber) => Ok((fiber, returns)),
            Err(e) => Err(Message::Failed(format!("cannot map a fiber's stack: {e}"))),
        }
    }

    /// Runs a loaded function without parameters as the root task of a
    /// scheduler: its result words, or the answer that tells how it ended
    /// otherwise.
    fn run(&mut self, func: FuncId) -> Result<Vec<u64>, Message> {
        let (fiber, returns) = self.root_fiber(func)?;
        let cancel = fiber.cancel_handle();
        let scheduler = Scheduler::new(
            SchedulerConfig::default(),
            self.worker.types(),
            self.code_map.clone(),
        );
        INTERRUPTED.store(false, Ordering::SeqCst);
        scheduler.spawn(fiber);
        let mut interrupted = false;
        let mut stopped = loop {
            if let Some(stopped) = scheduler.wait_timeout(INTERRUPT_POLL) {
                break stopped;
            }
            if INTERRUPTED.swap(false, Ordering::SeqCst) {
                interrupted = true;
                cancel.cancel();
            }
        };
        drop(scheduler);
        match Self::ended(stopped.pop(), returns, interrupted) {
            Message::Finished(words) => Ok(words),
            other => Err(other),
        }
    }
}

/// Connects to the host at `socket`, says `Hello` and answers messages
/// until the host says `Shutdown` or goes away.
pub fn serve(kind: ImageKind, socket: &Path) -> io::Result<()> {
    // Ctrl-C interrupts REPL input; the app is stopped by the host.
    if kind == ImageKind::Scratch {
        handle_interrupts()?;
    }
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
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return end(image),
            Err(e) => return Err(e),
        };
        match image.answer(message) {
            Some(reply) => write_message(&mut stream, &reply)?,
            None => return end(image),
        }
    }
}

/// Ends the image. A running app is not waited for: its tasks may be in
/// the middle of anything, and the process ending stops them all.
fn end(image: Image) -> io::Result<()> {
    if image.app.is_some() {
        std::process::exit(0);
    }
    Ok(())
}
