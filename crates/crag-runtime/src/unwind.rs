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

//! Traps and the unwinder (Plan §11.4.14).
//!
//! A check that fails releases what its frame holds and calls `rt_trap`,
//! which never returns. The frames below it are suspended at calls, and the
//! stack map of each call lists the slots of the boxes the frame holds
//! across it, each with a reference of its own. `rt_trap` walks the
//! frame-pointer chain to the fiber's first frame, releases those boxes,
//! records the trap and ends the fiber.
//!
//! A trap stops at the first frame whose call has a trap handler
//! (Specification §8.3.1): the frames above it release what they hold, the
//! trap is recorded in the task context, and that frame continues at the
//! handler. Without one, the trap ends its task. A trap a handler of its
//! own frame takes goes there without the unwinder, through
//! `rt_trap_catch`. Cancellation unwinds the same way, with a `Cancelled`
//! trap that no handler takes (§10.4, Plan §11.7.4).
//!
//! `rt_tx_throw` walks the chain the same way, but stops at the first frame
//! whose call has a handler: the call of an `atomic` block's code, whose
//! attempt the frames above it left (§11.7.14). That frame continues at the
//! handler with its frame pointer and the stack pointer it had at the call,
//! as Cranelift's `try_call` expects, and keeps what it holds.

use std::sync::atomic::Ordering;

use std::collections::HashMap;
use std::sync::Arc;

use crag_abi::{CodeObject, FuncId, HandlerKind, NO_POSITION, TrapKind, TrapOrigin};

use crate::die;
use crate::fiber::{STATUS_TRAPPED, TaskContext, Worker};
use crate::rc::{drop_box, holds_box};
use crate::text::{TextWords, make_text};

/// What the runtime knows of the loaded code: the stack maps of its calls,
/// by return address, and where each function lies.
#[derive(Debug, Default)]
pub struct CodeMap {
    /// Return addresses, sorted, with the offsets of the slots that hold
    /// boxes from the stack pointer at the call.
    safepoints: Vec<(usize, Box<[u32]>)>,
    /// The start and end of each function's code, sorted.
    functions: Vec<(usize, usize, FuncId)>,
    /// Return addresses of calls with a handler, sorted, with the
    /// handler's address, the frame offset of the call and what it takes.
    handlers: Vec<(usize, usize, u32, HandlerKind)>,
    /// Where the traps of each function's code lie in its module.
    origins: HashMap<FuncId, Arc<Origins>>,
    /// The entry stubs a task of a scope starts in, which call a function
    /// value's code with its environment: by the code's number of results.
    task_entries: Option<[usize; 3]>,
}

impl CodeMap {
    pub fn new() -> CodeMap {
        CodeMap::default()
    }

    /// Adds a code object loaded with its entry point at `entry`.
    pub fn add(&mut self, func: FuncId, entry: usize, object: &CodeObject) {
        let base = entry - object.entry as usize;
        self.functions.push((base, base + object.code.len(), func));
        self.functions.sort_unstable_by_key(|f| f.0);
        for map in &object.stack_maps {
            let ret = base + map.return_offset as usize;
            self.safepoints.push((ret, map.slots.clone().into()));
        }
        self.safepoints.sort_unstable_by_key(|s| s.0);
        for h in &object.handlers {
            let ret = base + h.return_offset as usize;
            self.handlers.push((
                ret,
                base + h.handler_offset as usize,
                h.frame_offset,
                h.kind,
            ));
        }
        self.origins.insert(
            func,
            Arc::new(Origins {
                module: object.module.clone(),
                origins: object.origins.clone(),
                details: object.details.clone(),
            }),
        );
        self.handlers.sort_unstable_by_key(|h| h.0);
    }

    /// The handler of the kind of the call returning to `ret` and the
    /// call's frame offset, if it has one.
    fn handler(&self, ret: usize, kind: HandlerKind) -> Option<(usize, u32)> {
        let start = self.handlers.partition_point(|h| h.0 < ret);
        self.handlers[start..]
            .iter()
            .take_while(|h| h.0 == ret)
            .find(|h| h.3 == kind)
            .map(|h| (h.1, h.2))
    }

    /// The module, line and column of a position in the code of `func`,
    /// and what the position word's upper half names.
    pub fn origin(&self, func: FuncId, position: u64) -> Option<(String, u32, u32, String)> {
        let origins = self.origins.get(&func)?;
        let offset = position as u32;
        let i = origins.origins.partition_point(|o| o.position <= offset);
        let at = origins.origins.get(i.checked_sub(1)?)?;
        let detail = (position >> 32) as usize;
        let detail = detail
            .checked_sub(1)
            .and_then(|d| origins.details.get(d).cloned())
            .unwrap_or_default();
        Some((origins.module.clone(), at.line, at.column, detail))
    }

    /// Gives the entry stubs of tasks: from `compile_entry_stub` with one
    /// parameter and zero, one and two results.
    ///
    /// # Safety
    ///
    /// The stubs stay loaded while fibers run with this map.
    pub unsafe fn set_task_entries(&mut self, stubs: [usize; 3]) {
        self.task_entries = Some(stubs);
    }

    pub(crate) fn task_entries(&self) -> Option<[usize; 3]> {
        self.task_entries
    }

    /// The function whose code holds `pc`.
    pub fn function_at(&self, pc: usize) -> Option<FuncId> {
        let i = self.functions.partition_point(|f| f.0 <= pc);
        let &(start, end, func) = self.functions.get(i.checked_sub(1)?)?;
        (start..end).contains(&pc).then_some(func)
    }

    /// The slots of the call returning to `ret`; none for a call that holds
    /// no box across it, or for code not in the map.
    fn slots(&self, ret: usize) -> &[u32] {
        match self.safepoints.binary_search_by_key(&ret, |s| s.0) {
            Ok(i) => &self.safepoints[i].1,
            Err(_) => &[],
        }
    }
}

/// Where the traps of one function's code lie.
#[derive(Debug)]
struct Origins {
    module: String,
    origins: Vec<TrapOrigin>,
    details: Vec<String>,
}

/// Why and where a fiber stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trap {
    pub kind: TrapKind,
    /// The byte offset of the expression that trapped in its module's
    /// source, if code generation knew it.
    pub position: Option<u32>,
    /// The function that trapped, then the functions of the frames below it
    /// in turn, as far as the code map holds them.
    pub stack: Vec<FuncId>,
}

/// `rt_trap(ctx, kind, position)`: see `crag_abi::RuntimeFn::Trap`.
///
/// Passes where the trapping frame's return address lies and its frame
/// pointer to `trap_entry`, on the system stack.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_trap(ctx: *const TaskContext, kind: u64, position: u64) -> ! {
    std::arch::naked_asm!(
        "mov rcx, rsp",
        "mov r8, rbp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {entry}",
        "ud2",
        worker = const std::mem::offset_of!(TaskContext, worker),
        entry = sym trap_entry,
    )
}

/// The Rust half of `rt_trap`: unwinds the fiber's stack to the first
/// frame whose call has a trap handler and continues it there, with the
/// trap recorded for the handler; without one, records the trap and
/// switches to the worker as if the fiber had finished.
///
/// # Safety
///
/// Called only by `rt_trap`. `ret` is where the return address into the
/// trapping frame lies, and `fp` is that frame's frame pointer.
unsafe extern "C" fn trap_entry(
    ctx: *const TaskContext,
    kind: u64,
    position: u64,
    ret: *const usize,
    fp: usize,
) -> ! {
    // SAFETY: `Worker::resume` stored the worker and the fiber in the
    // context, and the fiber's frames are suspended at calls.
    unsafe {
        let worker: *mut Worker = (*ctx).worker.load(Ordering::Relaxed);
        let fiber = (*ctx).fiber.load(Ordering::Relaxed);
        // A trap raised again began where the handler took it.
        let again = kind & RETHROWN != 0;
        let kind = kind & !RETHROWN;
        let trap_kind = TrapKind::from_index(kind).unwrap_or_else(|| die("a trap of no kind"));
        let first = ret.read();
        let earlier = if again {
            std::mem::take(&mut (*fiber).caught_stack)
        } else {
            Vec::new()
        };
        let mut stack = earlier;
        let land_at = |fp_at: usize, handler: usize, offset: u32, unwound: Vec<FuncId>| {
            // The handler's frame and those below it stay.
            (*fiber).caught_stack = unwound;
            if !again {
                (*ctx).caught_ret.store(first, Ordering::Relaxed);
            }
            (*ctx).caught_kind.store(kind, Ordering::Relaxed);
            (*ctx).caught_position.store(position, Ordering::Relaxed);
            land(fp_at - offset as usize, fp_at, handler)
        };
        unwind(worker, ret, fp, trap_kind.catchable(), land_at, &mut stack);
        let trap = Trap {
            kind: trap_kind,
            position: (position != NO_POSITION).then_some(position as u32),
            stack,
        };
        // The fiber takes the trap, so nothing on this stack owns anything
        // when `leave` abandons it.
        (*(*ctx).fiber.load(Ordering::Relaxed)).trap = Some(trap);
        (*ctx).status.store(STATUS_TRAPPED, Ordering::Relaxed);
        leave(worker)
    }
}

/// Releases the boxes every frame below the trapping one holds, from the
/// return address at `ret` and the frame pointer `fp` down the chain to the
/// fiber's first frame, whose saved frame pointer is zero, or, with
/// `catch`, to the first frame whose call has a trap handler, which `land`
/// continues. Returns the functions of the frames the code map knows, the
/// trapping one first.
///
/// # Safety
///
/// As for `trap_entry`.
unsafe fn unwind(
    worker: *mut Worker,
    mut ret: *const usize,
    mut fp: usize,
    catch: bool,
    land: impl Fn(usize, usize, u32, Vec<FuncId>),
    stack: &mut Vec<FuncId>,
) {
    // SAFETY: as the caller promises. Each frame's stack pointer at its call
    // lies just above the return address; the frame pointer of the frame
    // below holds the next link of the chain, and the return address
    // into that frame lies just above it.
    unsafe {
        let code = Worker::code(worker);
        let (heap, types) = Worker::heap_and_types(worker);
        loop {
            let at = ret.read();
            if catch && let Some((handler, offset)) = code.handler(at, HandlerKind::Trap) {
                land(fp, handler, offset, std::mem::take(stack));
                die("a trap handler was left");
            }
            let sp = ret as usize + 8;
            stack.extend(code.function_at(at));
            for &offset in code.slots(at) {
                // A function value's environment may be null, and the
                // first word of an inline string no pointer.
                let ptr = ((sp + offset as usize) as *const *mut u8).read();
                if holds_box(ptr) {
                    drop_box(heap, types, ptr);
                }
            }
            if fp == 0 {
                return;
            }
            ret = (fp + 8) as *const usize;
            fp = (fp as *const usize).read();
        }
    }
}

/// The bit of a trap's kind that `rt_trap_rethrow` sets: the trap is one
/// a handler took, raised again.
const RETHROWN: u64 = 1 << 32;

/// The functions of the frames that called the frame whose frame pointer is
/// `fp`, innermost first, as far as the code map knows them.
///
/// # Safety
///
/// `fp` is the frame pointer of a frame of a fiber's stack whose frames
/// are suspended at calls.
pub(crate) unsafe fn callers(code: &CodeMap, mut fp: usize) -> Vec<FuncId> {
    let mut out = Vec::new();
    // SAFETY: as the caller promises, the chain of frame pointers ends at
    // the fiber's first frame, whose saved frame pointer is zero.
    unsafe {
        while fp != 0 {
            let ret = ((fp + 8) as *const usize).read();
            let Some(func) = code.function_at(ret) else {
                break;
            };
            out.push(func);
            fp = (fp as *const usize).read();
        }
    }
    out
}

/// `rt_tx_throw(ctx)`: see `crag_abi::RuntimeFn::TxThrow`.
///
/// Passes where the throwing frame's return address lies and its frame
/// pointer to `throw_entry`, on the system stack, as `rt_trap` does.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context, from code a call with a handler is below.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_tx_throw(ctx: *const TaskContext) -> ! {
    std::arch::naked_asm!(
        "mov rsi, rsp",
        "mov rdx, rbp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {entry}",
        "ud2",
        worker = const std::mem::offset_of!(TaskContext, worker),
        entry = sym throw_entry,
    )
}

/// The Rust half of `rt_tx_throw`: releases what the frames hold up to the
/// first whose call has a handler, and continues that frame there.
///
/// # Safety
///
/// Called only by `rt_tx_throw`. `ret` is where the return address into the
/// throwing frame lies, and `fp` is that frame's frame pointer.
unsafe extern "C" fn throw_entry(
    ctx: *const TaskContext,
    mut ret: *const usize,
    mut fp: usize,
) -> ! {
    // SAFETY: as for `trap_entry`; a runtime call never has a handler, so
    // the throwing frame is released like the others.
    unsafe {
        let worker: *mut Worker = (*ctx).worker.load(Ordering::Relaxed);
        let code = Worker::code(worker);
        let (heap, types) = Worker::heap_and_types(worker);
        loop {
            let at = ret.read();
            if let Some((handler, offset)) = code.handler(at, HandlerKind::Transaction) {
                land(fp - offset as usize, fp, handler);
            }
            let sp = ret as usize + 8;
            for &offset in code.slots(at) {
                let ptr = ((sp + offset as usize) as *const *mut u8).read();
                if holds_box(ptr) {
                    drop_box(heap, types, ptr);
                }
            }
            if fp == 0 {
                die("a transaction's conflict reached no atomic block");
            }
            ret = (fp + 8) as *const usize;
            fp = (fp as *const usize).read();
        }
    }
}

/// `rt_trap_catch(ctx, kind, position)`: see
/// `crag_abi::RuntimeFn::TrapCatch`. Writes the trap into the context, the
/// return address of this call with it, and returns.
///
/// # Safety
///
/// Only generated code may call this, with the fiber's task context.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_trap_catch(ctx: *const TaskContext, kind: u64, position: u64) {
    std::arch::naked_asm!(
        "mov [rdi + {kind}], rsi",
        "mov [rdi + {position}], rdx",
        "mov rax, [rsp]",
        "mov [rdi + {ret}], rax",
        "ret",
        kind = const std::mem::offset_of!(TaskContext, caught_kind),
        position = const std::mem::offset_of!(TaskContext, caught_position),
        ret = const std::mem::offset_of!(TaskContext, caught_ret),
    )
}

/// `rt_trap_rethrow(ctx)`: see `crag_abi::RuntimeFn::TrapRethrow`. Raises
/// the trap the context holds, as `rt_trap` from the caller.
///
/// # Safety
///
/// As for `rt_trap`.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_trap_rethrow(ctx: *const TaskContext) -> ! {
    std::arch::naked_asm!(
        "mov rsi, [rdi + {kind}]",
        "bts rsi, 32",
        "mov rdx, [rdi + {position}]",
        "jmp {trap}",
        kind = const std::mem::offset_of!(TaskContext, caught_kind),
        position = const std::mem::offset_of!(TaskContext, caught_position),
        trap = sym rt_trap,
    )
}

system_stack_fn! {
    /// `rt_trap_caught(ctx, which) -> u64`: see
    /// `crag_abi::RuntimeFn::TrapCaught`.
    fn rt_trap_caught(ctx: *const TaskContext, which: u64) -> u64 => caught_entry
}

/// The Rust half of `rt_trap_caught`.
///
/// # Safety
///
/// Called only by `rt_trap_caught`.
unsafe extern "C" fn caught_entry(ctx: *const TaskContext, which: u64) -> u64 {
    // SAFETY: as the caller promises.
    let ctx = unsafe { &*ctx };
    match which {
        0 => ctx.caught_kind.load(Ordering::Relaxed),
        _ => {
            // SAFETY: as the caller promises.
            let origin = unsafe { caught_origin(ctx) };
            let (_, line, column, _) = origin.unwrap_or_default();
            u64::from(if which == 1 { line } else { column })
        }
    }
}

system_stack_fn! {
    /// `rt_trap_caught_text(ctx, which) -> (w0, w1)`: see
    /// `crag_abi::RuntimeFn::TrapCaughtText`.
    fn rt_trap_caught_text(ctx: *const TaskContext, which: u64) -> TextWords => caught_text_entry
}

/// The Rust half of `rt_trap_caught_text`.
///
/// # Safety
///
/// Called only by `rt_trap_caught_text`.
unsafe extern "C" fn caught_text_entry(ctx: *const TaskContext, which: u64) -> TextWords {
    // SAFETY: as the caller promises.
    let ctx = unsafe { &*ctx };
    // SAFETY: as the caller promises.
    let (module, _, _, detail) = unsafe { caught_origin(ctx) }.unwrap_or_default();
    let message =
        TrapKind::from_index(ctx.caught_kind.load(Ordering::Relaxed)).map_or("", TrapKind::message);
    let text = match which {
        0 => module.as_str(),
        1 => message,
        _ => detail.as_str(),
    };
    // SAFETY: called on the system stack by a runtime function.
    let (heap, _) = unsafe { crate::system::worker_of(ctx) };
    let [w0, w1] = make_text(heap, &[text.as_bytes()]);
    TextWords(w0, w1)
}

/// Where the trap the context holds lies: module, line, column, and what it
/// names.
///
/// # Safety
///
/// A worker runs the fiber of the context.
unsafe fn caught_origin(ctx: &TaskContext) -> Option<(String, u32, u32, String)> {
    // SAFETY: as the caller promises.
    let code = unsafe { Worker::code(ctx.worker.load(Ordering::Relaxed)) };
    let func = code.function_at(ctx.caught_ret.load(Ordering::Relaxed))?;
    code.origin(func, ctx.caught_position.load(Ordering::Relaxed))
}

/// Continues a frame at a handler: its stack and frame pointers, and where.
///
/// # Safety
///
/// `pc` is the handler of a call of the frame whose pointers these are,
/// which a throw left.
#[unsafe(naked)]
unsafe extern "C" fn land(sp: usize, fp: usize, pc: usize) -> ! {
    std::arch::naked_asm!("mov rsp, rdi", "mov rbp, rsi", "jmp rdx")
}

/// Continues the worker at the switch frame its `resume` left on the
/// system stack, abandoning the Rust frames below it, which own nothing.
///
/// # Safety
///
/// The worker is running a fiber, from whose `resume` it switched.
#[unsafe(naked)]
unsafe extern "C" fn leave(worker: *mut Worker) -> ! {
    std::arch::naked_asm!(
        "mov rsp, [rdi]",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
    )
}
