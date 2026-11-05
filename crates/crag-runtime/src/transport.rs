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
//! the descriptors of the types the program has none for, to the process
//! ([`publish`]): a code map looks there for an address in a receiver's
//! arena, and descriptors for an index they lack. Nothing else changes,
//! so a reload that gives the workers new tables keeps the received code
//! reachable. A publish replaces the arena's code map, which is freed once
//! no stack walk holds it; each descriptor is published once and stays. A receiver numbers the types it adds from a
//! range of its own ([`fresh_types`]), so the descriptors of several
//! programs in one process never meet.
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
//!
//! The receiver may unload code it holds no run of and that no value can
//! reach (Implementation Plan §11.10.9): a run keeps the receiver's hold
//! on its code ([`Received::hold`]) until it stopped.
//!
//! Code travels as bytes (§18.7). `send` encodes an `Expr`, its tree and
//! its environment in the Solid value codec, by the shapes the environment
//! carries (`crag_mir::WIRE`), stamped with one of the process's sending
//! budgets (`rt_transport_encode`). `decode` admits the bytes under the
//! process's receiving budgets, has the receiver check and compile the
//! tree, and decodes the environment into the receiver's layout of it
//! (`rt_transport_decode`). The `Expr` it builds runs the compiled code
//! when it is called, so that code stays loaded, and carries its budget
//! (`crag_mir::BUDGET`). `run` takes the steps and memory it may use from
//! that budget (`crate::budgets`): the policy's, or what is left of the
//! budget where that is less. A run the budget stops, not the policy,
//! gives `BudgetLimit`; once it stopped, the budget gets back the steps it
//! did not take and all its memory.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::{Arc, PoisonError, RwLock};

use crag_abi::{HEADER_SIZE, Shapes, TrapKind, TypeDescriptor};
use crag_budget::message::Message;
use crag_budget::{Grant, Refusal};

use crate::budgets::registry;
use crate::cancel::raise;
use crate::codec::{decode_value, encode_value};
use crate::die;
use crate::fiber::{Fiber, TaskContext};
use crate::meter::Meter;
use crate::print::retain_value;
use crate::rc::{Types, drop_box, retain};
use crate::sched::{FiberRef, Shared, WaitReason, local_of, scheduler_of, suspend, wake};
use crate::system::worker_of;
use crate::text::{bytes_of, in_buffer, make_text};
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

/// What `run` and `decode` ask the receiver.
pub struct Request<'a> {
    /// The bytes of the tree, as the `Expr` carries them.
    pub tree: &'a [u8],
    /// The bytes of the function type the code must have, an `FnType`.
    pub expected: &'a [u8],
    pub accept: Accept,
    /// The policy's limits, which receiving counts against first.
    pub steps: u64,
    pub memory: u64,
    /// Whether the caller signalled the callees accepted with another
    /// body already: until it did, code that has some does not run, and
    /// the caller asks again.
    pub signalled: bool,
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
    /// What keeps the code loaded while it runs: the run drops it once
    /// the code stopped.
    pub hold: Box<dyn Send>,
}

/// Code that arrived as bytes, accepted and compiled for good: what its
/// `Expr` is built from.
pub struct Decoded {
    /// The code of the root closure, which calling the `Expr` runs.
    pub entry: usize,
    /// The shapes of the closure's environment as the receiver lays it
    /// out, and those as the bytes the environment travels on from here.
    pub env: (Shapes, u32),
    pub wire: Vec<u8>,
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

    /// Checks the tree of code that arrived as `receive` does, and keeps
    /// its code loaded for good, since its `Expr` may call it any time.
    fn decode(&self, request: &Request<'_>) -> Result<Decoded, Refused>;
}

/// The code map of each receiver's arena, from its start to its end. A
/// stack walk holds a map while it reads it, so the map a publish
/// replaces is freed once the last walk that read it is done.
static ARENAS: RwLock<Vec<(usize, usize, Arc<CodeMap>)>> = RwLock::new(Vec::new());

/// Whether any receiver published code: until one did, no address is
/// received code's, and a walk takes no lock.
static ANY_ARENA: AtomicBool = AtomicBool::new(false);

/// The descriptors received code added, each published once and kept: a
/// box of the type may live as long as the process.
static TYPES: RwLock<BTreeMap<u32, &'static TypeDescriptor>> = RwLock::new(BTreeMap::new());

static ANY_TYPE: AtomicBool = AtomicBool::new(false);

/// Publishes a receiver's code, before anything runs it: the code map of
/// its arena, which describes everything loaded there now, and the
/// descriptors it adds.
pub fn publish(start: usize, end: usize, code: CodeMap, types: BTreeMap<u32, TypeDescriptor>) {
    if !types.is_empty() {
        let mut known = TYPES.write().unwrap_or_else(PoisonError::into_inner);
        for (index, descriptor) in types {
            known
                .entry(index)
                .or_insert_with(|| Box::leak(Box::new(descriptor)));
        }
        ANY_TYPE.store(true, Ordering::Release);
    }
    let code = Arc::new(code);
    let old = {
        let mut arenas = ARENAS.write().unwrap_or_else(PoisonError::into_inner);
        let old = arenas
            .iter()
            .position(|a| a.0 == start)
            .map(|i| arenas.swap_remove(i));
        arenas.push((start, end, code));
        old
    };
    ANY_ARENA.store(true, Ordering::Release);
    // The map before goes once no walk holds it, outside the lock.
    drop(old);
}

/// The type indices one receiver numbers the types it adds in.
pub const FRESH_SPAN: u32 = 1 << 26;

/// The first type index of a new receiver's own range, past every
/// program's.
pub fn fresh_types() -> u32 {
    static NEXT: AtomicU32 = AtomicU32::new(1);
    FRESH_SPAN.saturating_mul(NEXT.fetch_add(1, Ordering::Relaxed))
}

/// The code map of received code that holds `pc`, if received code does.
pub(crate) fn code_at(pc: usize) -> Option<Arc<CodeMap>> {
    if !ANY_ARENA.load(Ordering::Acquire) {
        return None;
    }
    ARENAS
        .read()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .find(|a| (a.0..a.1).contains(&pc))
        .map(|a| a.2.clone())
}

/// The descriptor received code gave a type, which a receiver checks its
/// own against, and descriptors that lack it fall back to.
pub fn received_type(index: u32) -> Option<&'static TypeDescriptor> {
    if !ANY_TYPE.load(Ordering::Acquire) {
        return None;
    }
    TYPES
        .read()
        .unwrap_or_else(PoisonError::into_inner)
        .get(&index)
        .copied()
}

/// The statuses of `rt_transport_run` and `rt_transport_decode`.
const RAN: u64 = 0;
const UNRESOLVED: u64 = 1;
const ILL_TYPED: u64 = 2;
const IMPURE: u64 = 3;
const STEP_LIMIT: u64 = 4;
const MEMORY_LIMIT: u64 = 5;
const MISMATCHED: u64 = 6;
const UNBUDGETED: u64 = 7;
const BUDGET_LIMIT: u64 = 8;
const NOT_CODE: u64 = 9;

/// The bit of the policy's first word that says the caller emitted the
/// signals of the mismatched callees.
const EMITTED: u64 = 1 << 8;

/// Where the fields of an `Expr`'s environment lie, before its captures:
/// the tree (`crag_mir::TREE`), the shapes it travels by
/// (`crag_mir::WIRE`) and its budget (`crag_mir::BUDGET`).
const TREE_AT: usize = HEADER_SIZE as usize + 16;
const WIRE_AT: usize = HEADER_SIZE as usize + 32;
const BUDGET_AT: usize = HEADER_SIZE as usize + 48;

/// The two words at `at` in a box.
///
/// # Safety
///
/// The box holds two words there.
unsafe fn pair(env: *mut u8, at: usize) -> [u64; 2] {
    // SAFETY: as the caller promises.
    unsafe {
        let p = env.add(at).cast::<u64>();
        [p.read(), p.add(1).read()]
    }
}

/// What makes a fiber run received code: the caller waiting for it, and
/// where its result goes.
pub(crate) struct Waiter {
    caller: FiberRef,
    scratch: *mut u64,
    /// The receiver's hold on the code, until it stopped.
    hold: Box<dyn Send>,
    /// What the run takes from the budget its `Expr` arrived under, and
    /// the budget's index.
    budget: Option<(Grant, u64)>,
}

// SAFETY: the scratch words lie on the side stack of the caller, which is
// suspended until the waiter wakes it, and only the waiter writes them.
unsafe impl Send for Waiter {}

/// The accepting policy in the first scratch word, and whether the
/// caller emitted the signals of mismatched callees.
fn accept_of(word: u64) -> (Accept, bool) {
    let accept = match word & !EMITTED {
        0 => Accept::Exact,
        1 => Accept::SameMajor,
        _ => Accept::Signature,
    };
    (accept, word & EMITTED != 0)
}

/// The program's scheduler and receiver, or the status that says there is
/// none.
///
/// # Safety
///
/// As `rt_transport_run`'s.
unsafe fn receiver_of(
    ctx: &TaskContext,
    scratch: *mut u64,
) -> Result<(Arc<Shared>, Arc<dyn Receive>), u64> {
    // SAFETY: as the caller promises.
    let Some(shared) = (unsafe { scheduler_of(ctx) }) else {
        raise(ctx, TrapKind::Unsupported, None);
        return Err(0);
    };
    let receiver = shared
        .receiver
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone();
    match receiver {
        Some(receiver) => Ok((shared, receiver)),
        // SAFETY: as the caller promises.
        None => Err(unsafe {
            refuse(
                ctx,
                scratch,
                Refused::Unresolved("this program cannot receive code".into()),
            )
        }),
    }
}

suspending_fn!(
    /// `rt_transport_run(ctx, scratch, x0, x1, i0, i1) -> status`: see
    /// `crag_abi::RuntimeFn::TransportRun`.
    ///
    /// # Safety
    ///
    /// The scratch words are as the function describes them, the environment is a
    /// live `Expr`'s, and the words are those of an input of the type the code
    /// expects, which the caller holds across the call.
    fn rt_transport_run(
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
            let (accept, emitted) = accept_of(word(0));
            let env = word(3) as *mut u8;
            let tree = pair(env, TREE_AT);
            let expected = [x0, x1];
            let (_, types) = worker_of(ctx);
            let (shared, receiver) = match receiver_of(ctx, scratch) {
                Ok(found) => found,
                Err(status) => return status,
            };
            // Code that arrived under a budget takes its limits from it too.
            let budget = env.add(BUDGET_AT).cast::<u64>().read();
            let mut grant = None;
            if budget > 0 {
                let index = budget - 1;
                match registry().reserve(index as usize, word(1), word(2)) {
                    Ok(g) => grant = Some((g, index)),
                    Err(Refusal::Limit { .. }) => {
                        scratch.write(index);
                        return BUDGET_LIMIT;
                    }
                    Err(Refusal::Unbudgeted(why)) => {
                        return refuse(ctx, scratch, Refused::Unresolved(why));
                    }
                }
            }
            let (steps, memory) = match &grant {
                Some((g, _)) => (g.steps, g.memory),
                None => (word(1), word(2)),
            };
            let request = Request {
                tree: bytes_of(&tree),
                expected: bytes_of(&expected),
                accept,
                steps,
                memory,
                signalled: emitted,
                types,
            };
            let result = receiver.receive(&request);
            let mismatched = match &result {
                Ok(received) => &received.mismatched[..],
                Err(Refused::StepLimit(m) | Refused::MemoryLimit(m)) => &m[..],
                Err(_) => &[],
            };
            // The code does not run now, so the grant goes back.
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
                Err(refused) => {
                    if let Some((g, index)) = grant {
                        // Receiving that ran out of steps took them all.
                        let (capped, left) = match &refused {
                            Refused::StepLimit(_) => (g.steps_capped, 0),
                            Refused::MemoryLimit(_) => (g.memory_capped, g.steps),
                            _ => (false, g.steps),
                        };
                        g.settle(left);
                        if capped {
                            scratch.write(index);
                            return BUDGET_LIMIT;
                        }
                    }
                    return refuse(ctx, scratch, refused);
                }
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
            fiber.received = Some(Box::new(Waiter {
                caller,
                scratch,
                hold: received.hold,
                budget: grant,
            }));
            shared.launch(fiber, local_of(ctx));
            // The wake gives the status.
            0
        }
    }
);

system_stack_fn!(
    /// `rt_transport_encode(ctx, scratch, env, stamp) -> status`: see
    /// `crag_abi::RuntimeFn::TransportEncode`.
    ///
    /// # Safety
    ///
    /// The caller passes two scratch words and the environment of a live `Expr`,
    /// which it holds.
    fn rt_transport_encode(
        ctx: *const TaskContext,
        scratch: *mut u64,
        env: u64,
        stamp: u64,
    ) -> u64 {
        // SAFETY: as the caller promises.
        unsafe {
            let ctx = &*ctx;
            let env = env as *mut u8;
            let tree = bytes_of(&pair(env, TREE_AT)).to_vec();
            let wire_words = pair(env, WIRE_AT);
            let wire = bytes_of(&wire_words);
            let Some((root, rest)) = wire.split_first_chunk::<4>() else {
                die("an `Expr` without the shapes of its environment");
            };
            let shapes = Shapes::decode(rest)
                .unwrap_or_else(|e| die(&format!("the shapes of an `Expr`: {e}")));
            let (_, types) = worker_of(ctx);
            let encoded = encode_value(&[env as u64], &shapes, u32::from_le_bytes(*root), types);
            let env_bytes = match encoded {
                Ok(bytes) => bytes,
                Err(what) => {
                    let why = format!("its captures hold {}, which cannot be sent", what.0);
                    give_text(ctx, scratch, &why);
                    return 1;
                }
            };
            let stamp = match stamp as i64 {
                ..0 => None,
                index => match registry().stamp(index as usize, &tree, &env_bytes) {
                    Some(stamp) => Some(stamp),
                    None => {
                        give_text(ctx, scratch, "no such budget to send under");
                        return 1;
                    }
                },
            };
            let message = Message {
                stamp,
                tree,
                env: env_bytes,
            };
            give_bytes(ctx, scratch, &message.encode());
            0
        }
    }
);

system_stack_fn!(
    /// `rt_transport_decode(ctx, scratch, x0, x1, b0, b1) -> status`: see
    /// `crag_abi::RuntimeFn::TransportDecode`.
    ///
    /// # Safety
    ///
    /// The scratch words are as the function describes them, and the caller holds
    /// the bytes.
    fn rt_transport_decode(
        ctx: *const TaskContext,
        scratch: *mut u64,
        x0: u64,
        x1: u64,
        b0: u64,
        b1: u64,
    ) -> u64 {
        // SAFETY: as the caller promises.
        unsafe {
            let ctx = &*ctx;
            let word = |i: usize| scratch.add(i).read();
            let (accept, _) = accept_of(word(0));
            let (steps, memory) = (word(1), word(2));
            let bytes = [b0, b1];
            let message = match Message::decode(bytes_of(&bytes)) {
                Ok(message) => message,
                Err(why) => {
                    give_text(ctx, scratch, &why);
                    return NOT_CODE;
                }
            };
            let budget = match registry().admit(message.stamp.as_ref(), &message.tree, &message.env)
            {
                Ok(budget) => budget,
                Err(Refusal::Unbudgeted(why)) => {
                    give_text(ctx, scratch, &why);
                    return UNBUDGETED;
                }
                Err(Refusal::Limit { index, .. }) => {
                    scratch.write(index as u64);
                    return BUDGET_LIMIT;
                }
            };
            let (_, receiver) = match receiver_of(ctx, scratch) {
                Ok(found) => found,
                Err(status) => return status,
            };
            let expected = [x0, x1];
            let (heap, types) = worker_of(ctx);
            let request = Request {
                tree: &message.tree,
                expected: bytes_of(&expected),
                accept,
                steps,
                memory,
                signalled: true,
                types,
            };
            let decoded = match receiver.decode(&request) {
                Ok(decoded) => decoded,
                Err(refused) => return refuse(ctx, scratch, refused),
            };
            let (shapes, root) = &decoded.env;
            let words = match decode_value(&message.env, shapes, *root, heap, types) {
                Ok(words) => words,
                Err(e) => {
                    let why = format!("its captures do not decode: {}", e.0);
                    give_text(ctx, scratch, &why);
                    return NOT_CODE;
                }
            };
            let env = words[0] as *mut u8;
            let (heap, types) = worker_of(ctx);
            // The environment must carry the tree that was checked.
            if bytes_of(&pair(env, TREE_AT)) != &message.tree[..] {
                drop_box(heap, types, env);
                give_text(ctx, scratch, "its environment carries another tree");
                return NOT_CODE;
            }
            // It carries its budget, and travels on in the receiver's layout.
            env.add(BUDGET_AT)
                .cast::<u64>()
                .write(budget.map_or(0, |b| b as u64 + 1));
            let old = pair(env, WIRE_AT);
            let [w0, w1] = make_text(heap, &[&decoded.wire]);
            env.add(WIRE_AT).cast::<u64>().write(w0);
            env.add(WIRE_AT + 8).cast::<u64>().write(w1);
            if in_buffer(old[0]) {
                drop_box(heap, types, old[0] as *mut u8);
            }
            scratch.write(decoded.entry as u64);
            scratch.add(1).write(env as u64);
            RAN
        }
    }
);

/// Writes why the code does not run where the caller reads it, and gives
/// the status.
///
/// # Safety
///
/// As `rt_transport_run`'s.
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
/// As `rt_transport_run`'s.
unsafe fn give_text(ctx: &TaskContext, scratch: *mut u64, text: &str) {
    // SAFETY: as the caller promises.
    unsafe { give_bytes(ctx, scratch, text.as_bytes()) }
}

/// Writes `Bytes` of `bytes` where the caller reads them.
///
/// # Safety
///
/// As `rt_transport_run`'s.
unsafe fn give_bytes(ctx: &TaskContext, scratch: *mut u64, bytes: &[u8]) {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, _) = worker_of(ctx);
        let [w0, w1] = make_text(heap, &[bytes]);
        scratch.write(w0);
        scratch.add(1).write(w1);
    }
}

/// Takes a fiber of received code that stopped from the worker that ran
/// it, and wakes its caller with the status, the result in its scratch
/// words, or the trap raised.
pub(crate) fn finished(mut fiber: Box<Fiber>) {
    let Waiter {
        caller,
        scratch,
        hold,
        budget,
    } = *fiber.received.take().expect("received code");
    let trap = fiber.trap().map(|t| t.kind);
    // A limit the budget set is the budget's.
    let stopped_by = budget.as_ref().and_then(|(g, index)| {
        let capped = match trap {
            Some(TrapKind::OutOfSteps) => g.steps_capped,
            Some(TrapKind::OutOfMemory) => g.memory_capped,
            _ => false,
        };
        capped.then_some(*index)
    });
    if let Some((grant, _)) = budget {
        grant.settle(fiber.steps_left().unwrap_or(0));
    }
    let status = match (fiber.results(), fiber.trap()) {
        _ if stopped_by.is_some() => {
            // SAFETY: the caller is suspended, and its scratch words wait.
            unsafe { scratch.write(stopped_by.unwrap_or(0)) };
            BUDGET_LIMIT
        }
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
    // No frame of the code is left: the receiver may unload it.
    drop(fiber);
    drop(hold);
    wake(caller, [status, 0]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_code_map_goes_once_replaced_and_no_walk_holds_it() {
        // An address range no other test publishes.
        let (start, end) = (0x7e00_0000_0000, 0x7e00_0010_0000);
        publish(start, end, CodeMap::new(), BTreeMap::new());
        let first = Arc::downgrade(&code_at(start + 8).unwrap());
        publish(start, end, CodeMap::new(), BTreeMap::new());
        assert!(first.upgrade().is_none(), "the replaced map stays");
        // A walk that holds the map keeps it until it is done.
        let held = code_at(start + 8).unwrap();
        let second = Arc::downgrade(&held);
        publish(start, end, CodeMap::new(), BTreeMap::new());
        assert!(second.upgrade().is_some());
        drop(held);
        assert!(second.upgrade().is_none(), "the replaced map stays");
        assert!(code_at(end).is_none());
    }
}
