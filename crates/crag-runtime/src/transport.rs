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

//! Running received code (Implementation Plan §11.10.9, Specification
//! §18.7): `std.transport.run` hands the tree of an `Expr` to the
//! program's receiver, which checks it and compiles it again in the
//! metered tier, and runs what it accepts as a metered task of its own,
//! next to the program's data.
//!
//! The receiver is the compiler's front end and code generator, which the
//! runtime cannot depend on; a program that can receive code gives its
//! scheduler one (`Scheduler::set_receiver`). It compiles against the
//! program's type indices,
//! so the received code reads and builds the program's values on the
//! program's heap: the input and the captures pass as they are, and the
//! result comes back as it is.
//!
//! The receiver loads its code into an arena of its own and publishes
//! what unwinding and freeing need of it, the code map of the arena and
//! the descriptors of the types the program has none for, to an overlay
//! for the process ([`publish`]): a code map looks there for an address
//! in a receiver's arena, and descriptors for an index they lack. Nothing
//! else changes, so a reload that gives the workers new tables keeps the
//! received code reachable. What is published stays. A receiver numbers
//! the types it adds from a range of its own ([`fresh_types`]), so the
//! descriptors of several programs in one process never meet.
//!
//! The caller waits while the receiver works, on its worker, as a host's
//! name is looked up (§11.7.13); the code itself runs as a task on the
//! scheduler, under the meter, and the caller is suspended until it ends.
//! Running out of steps or memory is a status, not a trap; any other trap
//! of the received code is the caller's. The task inherits no signals,
//! since pure code emits none.
//!
//! Callees accepted although their body hash differs from the sender's
//! are signalled before the code runs (§18.7). The receiver lists them,
//! and while the caller has not emitted their signals yet, the call gives
//! them back instead of running the code; `run` emits a `HashMismatch`
//! for each and calls again, which finds the code in the receiver's store.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicPtr, AtomicU32, Ordering};

use crag_abi::{HEADER_SIZE, Shapes, TrapKind, TypeDescriptor};

use crate::cancel::raise;
use crate::die;
use crate::fiber::{Fiber, TaskContext};
use crate::meter::Meter;
use crate::print::retain_value;
use crate::rc::{Types, retain};
use crate::sched::{FiberRef, WaitReason, local_of, scheduler_of, suspend, wake};
use crate::system::worker_of;
use crate::text::{bytes_of, make_text};
use crate::unwind::CodeMap;

/// Which references received code may resolve to (§18.7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Accept {
    Exact,
    SameMajor,
    Signature,
}

/// A callee accepted although its body hash differs from the sender's:
/// its module and its name.
pub type Mismatch = (String, String);

/// What `run` asks the receiver.
pub struct Request<'a> {
    /// The bytes of the tree, as the `Expr` carries them.
    pub tree: &'a [u8],
    /// The bytes of the function type the code must have, an `FnType`.
    pub expected: &'a [u8],
    pub accept: Accept,
    /// The policy's limits, which receiving counts against first.
    pub steps: u64,
    pub memory: u64,
    /// The program's descriptors, which the received code's must agree
    /// with.
    pub types: &'a Types,
}

/// Received code that the receiver accepted, compiled and published.
pub struct Received {
    /// The entry stub to run it with, for the environment and the input's
    /// words, and the code of the root closure.
    pub stub: usize,
    pub entry: usize,
    /// The input's words and shapes, and the result's words.
    pub input: (Shapes, u32),
    pub input_words: u32,
    pub result_words: u32,
    /// What is left of the limits once receiving took its part.
    pub steps: u64,
    pub memory: u64,
    /// The callees accepted with another body than the sender's.
    pub mismatched: Vec<Mismatch>,
}

/// Why received code does not run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refused {
    Unresolved(String),
    IllTyped(String),
    Impure(String),
    /// Receiving took more of the limits than the policy gives, with the
    /// callees accepted with another body when the tree was checked first.
    StepLimit(Vec<Mismatch>),
    MemoryLimit(Vec<Mismatch>),
}

/// The receiver of a program that can receive code.
pub trait Receive: Send + Sync {
    /// Checks the tree against the expected type as the policy asks,
    /// compiles what it accepts and publishes it.
    fn receive(&self, request: &Request<'_>) -> Result<Received, Refused>;
}

/// The received code of the process: the code map of each receiver's
/// arena, from its start to its end, and the descriptors received code
/// added.
struct Overlay {
    arenas: Vec<(usize, usize, &'static CodeMap)>,
    types: BTreeMap<u32, TypeDescriptor>,
}

static OVERLAY: AtomicPtr<Overlay> = AtomicPtr::new(std::ptr::null_mut());
static PUBLISHING: Mutex<()> = Mutex::new(());

/// Publishes a receiver's code, before anything runs it: the code map of
/// its arena, which holds everything loaded there so far, and the
/// descriptors it adds.
pub fn publish(start: usize, end: usize, code: CodeMap, types: BTreeMap<u32, TypeDescriptor>) {
    let _publishing = PUBLISHING.lock().unwrap_or_else(|e| e.into_inner());
    let code: &'static CodeMap = Box::leak(Box::new(code));
    let mut next = match overlay() {
        Some(o) => Overlay {
            arenas: o.arenas.clone(),
            types: o.types.clone(),
        },
        None => Overlay {
            arenas: Vec::new(),
            types: BTreeMap::new(),
        },
    };
    next.arenas.retain(|a| a.0 != start);
    next.arenas.push((start, end, code));
    next.types.extend(types);
    // The overlay before stays: a reader may hold it.
    OVERLAY.store(Box::into_raw(Box::new(next)), Ordering::Release);
}

/// The type indices one receiver numbers the types it adds in.
pub const FRESH_SPAN: u32 = 1 << 26;

/// The first type index of a new receiver's own range, past every
/// program's.
pub fn fresh_types() -> u32 {
    static NEXT: AtomicU32 = AtomicU32::new(1);
    FRESH_SPAN.saturating_mul(NEXT.fetch_add(1, Ordering::Relaxed))
}

fn overlay() -> Option<&'static Overlay> {
    let overlay = OVERLAY.load(Ordering::Acquire);
    // SAFETY: a published overlay is never freed.
    unsafe { overlay.as_ref() }
}

/// The code map of received code that holds `pc`, if received code does.
pub(crate) fn code_at(pc: usize) -> Option<&'static CodeMap> {
    overlay()?
        .arenas
        .iter()
        .find(|a| (a.0..a.1).contains(&pc))
        .map(|a| a.2)
}

/// The descriptor received code gave a type, which a receiver checks its
/// own against, and descriptors that lack it fall back to.
pub fn received_type(index: u32) -> Option<&'static TypeDescriptor> {
    overlay()?.types.get(&index)
}

/// The statuses of `rt_transport_run`.
const RAN: u64 = 0;
const UNRESOLVED: u64 = 1;
const ILL_TYPED: u64 = 2;
const IMPURE: u64 = 3;
const STEP_LIMIT: u64 = 4;
const MEMORY_LIMIT: u64 = 5;
const MISMATCHED: u64 = 6;

/// The bit of the policy's first word that says the caller emitted the
/// signals of the mismatched callees.
const EMITTED: u64 = 1 << 8;

/// What makes a fiber run received code: the caller waiting for it, and
/// where its result goes.
pub(crate) struct Waiter {
    caller: FiberRef,
    scratch: *mut u64,
}

// SAFETY: the scratch words lie on the side stack of the caller, which is
// suspended until the waiter wakes it, and only the waiter writes them.
unsafe impl Send for Waiter {}

suspending_fn! {
    /// `rt_transport_run(ctx, scratch, x0, x1, i0, i1) -> status`: see
    /// `crag_abi::RuntimeFn::TransportRun`.
    fn rt_transport_run(ctx: *const TaskContext, scratch: *mut u64, x0: u64, x1: u64, i0: u64, i1: u64) -> u64
        => run_entry
}

/// The Rust half of `rt_transport_run`.
///
/// # Safety
///
/// Called only by `rt_transport_run`, with scratch words as it describes
/// them, the environment of a live `Expr` and the words of an input of the
/// type the code expects, which the caller holds across the call.
unsafe extern "C" fn run_entry(
    ctx: *const TaskContext,
    scratch: *mut u64,
    x0: u64,
    x1: u64,
    i0: u64,
    i1: u64,
) -> u64 {
    // SAFETY: as the caller promises.
    unsafe {
        let ctx = &*ctx;
        let word = |i: usize| scratch.add(i).read();
        let emitted = word(0) & EMITTED != 0;
        let accept = match word(0) & !EMITTED {
            0 => Accept::Exact,
            1 => Accept::SameMajor,
            _ => Accept::Signature,
        };
        let env = word(3) as *mut u8;
        // The tree's bytes lie second in the environment
        // (`crag_mir::TREE`).
        let at = env.add(HEADER_SIZE as usize + 16).cast::<u64>();
        let tree = [at.read(), at.add(1).read()];
        let expected = [x0, x1];
        let (_, types) = worker_of(ctx);
        let Some(shared) = scheduler_of(ctx) else {
            raise(ctx, TrapKind::Unsupported, None);
            return 0;
        };
        let receiver = shared
            .receiver
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone();
        let Some(receiver) = receiver else {
            return refuse(
                ctx,
                scratch,
                Refused::Unresolved("this program cannot receive code".into()),
            );
        };
        let request = Request {
            tree: bytes_of(&tree),
            expected: bytes_of(&expected),
            accept,
            steps: word(1),
            memory: word(2),
            types,
        };
        let result = receiver.receive(&request);
        let mismatched = match &result {
            Ok(received) => &received.mismatched[..],
            Err(Refused::StepLimit(m) | Refused::MemoryLimit(m)) => &m[..],
            Err(_) => &[],
        };
        if !emitted && !mismatched.is_empty() {
            let lines: Vec<String> = mismatched
                .iter()
                .map(|(m, n)| format!("{m} {n}\n"))
                .collect();
            give_text(ctx, scratch, &lines.concat());
            return MISMATCHED;
        }
        let received = match result {
            Ok(received) => received,
            Err(refused) => return refuse(ctx, scratch, refused),
        };
        // The code takes its environment and its input: the caller keeps
        // its own.
        retain(env);
        let input = [i0, i1];
        let n = received.input_words as usize;
        let (shapes, root) = &received.input;
        retain_value(&input[..n], shapes, *root);
        let mut args = vec![env as u64];
        args.extend_from_slice(&input[..n]);
        let config = (*ctx.fiber.load(Ordering::Relaxed)).config;
        let mut fiber = Fiber::new(received.stub, received.entry, &args, config)
            .unwrap_or_else(|_| die("out of memory for a stack of received code"));
        fiber.set_meter(Meter {
            steps: received.steps,
            memory: received.memory as usize,
        });
        let caller = suspend(ctx, WaitReason::Received);
        fiber.received = Some(Box::new(Waiter { caller, scratch }));
        shared.launch(fiber, local_of(ctx));
        // The wake gives the status.
        0
    }
}

/// Writes why the code does not run where the caller reads it, and gives
/// the status.
///
/// # Safety
///
/// As `run_entry`'s.
unsafe fn refuse(ctx: &TaskContext, scratch: *mut u64, refused: Refused) -> u64 {
    let (status, message) = match refused {
        Refused::Unresolved(m) => (UNRESOLVED, m),
        Refused::IllTyped(m) => (ILL_TYPED, m),
        Refused::Impure(m) => (IMPURE, m),
        Refused::StepLimit(_) => return STEP_LIMIT,
        Refused::MemoryLimit(_) => return MEMORY_LIMIT,
    };
    // SAFETY: as the caller promises.
    unsafe { give_text(ctx, scratch, &message) };
    status
}

/// Writes a `Str` of `text` where the caller reads it.
///
/// # Safety
///
/// As `run_entry`'s.
unsafe fn give_text(ctx: &TaskContext, scratch: *mut u64, text: &str) {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, _) = worker_of(ctx);
        let [w0, w1] = make_text(heap, &[text.as_bytes()]);
        scratch.write(w0);
        scratch.add(1).write(w1);
    }
}

/// Takes a fiber of received code that stopped from the worker that ran
/// it, and wakes its caller with the status, the result in its scratch
/// words, or the trap raised.
pub(crate) fn finished(mut fiber: Box<Fiber>) {
    let Waiter { caller, scratch } = *fiber.received.take().expect("received code");
    let status = match (fiber.results(), fiber.trap()) {
        (Some(words), _) => {
            // SAFETY: the caller is suspended, and its scratch words wait.
            unsafe {
                scratch.write(words[0]);
                scratch.add(1).write(words[1]);
            }
            RAN
        }
        (None, Some(t)) if t.kind == TrapKind::OutOfSteps => STEP_LIMIT,
        (None, Some(t)) if t.kind == TrapKind::OutOfMemory => MEMORY_LIMIT,
        (None, t) => {
            let kind = t.map_or(TrapKind::Error, |t| t.kind);
            raise(caller.ctx(), kind, None);
            RAN
        }
    };
    drop(fiber);
    wake(caller, [status, 0]);
}
