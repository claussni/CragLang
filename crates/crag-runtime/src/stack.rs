//! Stack memory with a guard page, the stack check and `morestack` (Plan §11.3.2).
//!
//! Generated code calls `rt_morestack` when a stack check fails. The routine
//! saves every register on the fiber stack, moves to the system stack and
//! calls `morestack_slow`, which handles stop requests and grows the stack by
//! copying it. Then it continues the fiber where the check failed, on the new
//! stack, or hands control to the worker if the fiber was asked to stop.

use std::io;
use std::mem::offset_of;
use std::sync::atomic::Ordering;

use crag_abi::{RUNTIME_RESERVE, STACK_MARGIN};

use crate::die;
use crate::fiber::{Fiber, FiberState, TaskContext};
use crate::sentinel::{StopReason, finish_check, take_pending};

/// A stack: a private mapping whose lowest page is inaccessible, so running
/// off the end faults instead of overwriting other memory.
pub(crate) struct StackMemory {
    /// Start of the mapping, which is the guard page.
    base: usize,
    /// Usable bytes above the guard page.
    size: usize,
    page: usize,
}

impl StackMemory {
    /// Maps a stack with at least `size` usable bytes, rounded up to pages.
    pub(crate) fn new(size: usize) -> io::Result<StackMemory> {
        // SAFETY: `sysconf` has no preconditions.
        let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
        let size = size.max(1).next_multiple_of(page);
        // SAFETY: a fresh anonymous mapping that aliases nothing; the guard
        // page is the lowest page of that same mapping.
        unsafe {
            let base = libc::mmap(
                std::ptr::null_mut(),
                page + size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_STACK,
                -1,
                0,
            );
            if base == libc::MAP_FAILED {
                return Err(io::Error::last_os_error());
            }
            if libc::mprotect(base, page, libc::PROT_NONE) != 0 {
                let error = io::Error::last_os_error();
                libc::munmap(base, page + size);
                return Err(error);
            }
            Ok(StackMemory {
                base: base as usize,
                size,
                page,
            })
        }
    }

    /// The lowest usable address.
    pub(crate) fn low(&self) -> usize {
        self.base + self.page
    }

    /// One past the highest usable address. Stacks grow down from here.
    pub(crate) fn top(&self) -> usize {
        self.low() + self.size
    }

    pub(crate) fn size(&self) -> usize {
        self.size
    }
}

impl Drop for StackMemory {
    fn drop(&mut self) {
        // SAFETY: unmaps exactly the mapping `new` created. The owner drops a
        // stack only when nothing runs on it.
        unsafe {
            libc::munmap(self.base as *mut libc::c_void, self.page + self.size);
        }
    }
}

/// Pushes all general registers and the sixteen vector registers: the save
/// area whose layout the constants below describe. The size of the vector
/// part appears as a literal because the text is shared between routines.
macro_rules! save_registers {
    () => {
        concat!(
            "push rax\n push rcx\n push rdx\n push rbx\n push rbp\n push rsi\n push rdi\n",
            "push r8\n push r9\n push r10\n push r11\n push r12\n push r13\n push r14\n push r15\n",
            "sub rsp, 256\n",
            "movdqu [rsp + 0x00], xmm0\n movdqu [rsp + 0x10], xmm1\n",
            "movdqu [rsp + 0x20], xmm2\n movdqu [rsp + 0x30], xmm3\n",
            "movdqu [rsp + 0x40], xmm4\n movdqu [rsp + 0x50], xmm5\n",
            "movdqu [rsp + 0x60], xmm6\n movdqu [rsp + 0x70], xmm7\n",
            "movdqu [rsp + 0x80], xmm8\n movdqu [rsp + 0x90], xmm9\n",
            "movdqu [rsp + 0xa0], xmm10\n movdqu [rsp + 0xb0], xmm11\n",
            "movdqu [rsp + 0xc0], xmm12\n movdqu [rsp + 0xd0], xmm13\n",
            "movdqu [rsp + 0xe0], xmm14\n movdqu [rsp + 0xf0], xmm15\n",
        )
    };
}

/// Undoes `save_registers!`, with the stack pointer at the save area.
macro_rules! restore_registers {
    () => {
        concat!(
            "movdqu xmm0, [rsp + 0x00]\n movdqu xmm1, [rsp + 0x10]\n",
            "movdqu xmm2, [rsp + 0x20]\n movdqu xmm3, [rsp + 0x30]\n",
            "movdqu xmm4, [rsp + 0x40]\n movdqu xmm5, [rsp + 0x50]\n",
            "movdqu xmm6, [rsp + 0x60]\n movdqu xmm7, [rsp + 0x70]\n",
            "movdqu xmm8, [rsp + 0x80]\n movdqu xmm9, [rsp + 0x90]\n",
            "movdqu xmm10, [rsp + 0xa0]\n movdqu xmm11, [rsp + 0xb0]\n",
            "movdqu xmm12, [rsp + 0xc0]\n movdqu xmm13, [rsp + 0xd0]\n",
            "movdqu xmm14, [rsp + 0xe0]\n movdqu xmm15, [rsp + 0xf0]\n",
            "add rsp, 256\n",
            "pop r15\n pop r14\n pop r13\n pop r12\n pop r11\n pop r10\n pop r9\n pop r8\n",
            "pop rdi\n pop rsi\n pop rbp\n pop rbx\n pop rdx\n pop rcx\n pop rax\n",
        )
    };
}
pub(crate) use {restore_registers, save_registers};

// The register save area of `rt_morestack`, from its lowest address:
// sixteen vector registers, fifteen general registers, the return address.
const XMM_BYTES: usize = 16 * 16;
const _: () = assert!(XMM_BYTES == 256); // the literal in the macros
/// Offset of the saved rdi, the task context.
const RDI_SLOT: usize = XMM_BYTES + 8 * 8;
/// Offset of the saved rbp, the head of the frame-pointer chain.
const RBP_SLOT: usize = XMM_BYTES + 10 * 8;
/// Size of the whole area: the stack pointer at the failed check was this
/// much higher.
pub(crate) const SAVE_BYTES: usize = XMM_BYTES + 15 * 8 + 8;
/// A switch frame, pushed below the save area when the fiber stops: six
/// registers and a return address.
const SWITCH_FRAME_BYTES: usize = 7 * 8;

// What the routine puts on the fiber stack must fit the reserve the stack
// check leaves for it.
const _: () = assert!(SAVE_BYTES + SWITCH_FRAME_BYTES <= RUNTIME_RESERVE as usize);

/// What `morestack_slow` tells the assembly routine, returned in rax and rdx.
#[repr(C)]
struct Resume {
    /// The save area's address, which changes when the stack moves.
    sp: usize,
    /// Not zero if the fiber must stop instead of continuing.
    stop: usize,
}

/// `rt_morestack(ctx, needed)`: see `crag_abi::RuntimeFn::Morestack`.
///
/// Preserves every register, because generated code calls it with the
/// preserve-all convention. The save area is also what makes the fiber
/// resumable: its complete state is on its own stack.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_morestack(ctx: *const TaskContext, needed: usize) {
    std::arch::naked_asm!(
        save_registers!(),
        // Third argument: the save area. Then continue on the system stack,
        // below the context the worker saved there when it switched to this
        // fiber.
        "mov rdx, rsp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {slow}",
        // Back to the fiber stack, which may be a new one.
        "mov rsp, rax",
        "test rdx, rdx",
        "jz 2f",
        // Stop: leave a switch frame that continues at label 2, record the
        // stack pointer and return into the worker's `switch` call.
        "mov rdi, [rsp + {rdi_slot}]",
        "lea rax, [rip + 2f]",
        "push rax",
        "sub rsp, 48",
        "mov [rdi + {saved_sp}], rsp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
        // Continue the fiber: restore everything and return to the check.
        "2:",
        restore_registers!(),
        "ret",
        rdi_slot = const RDI_SLOT,
        worker = const offset_of!(TaskContext, worker),
        saved_sp = const offset_of!(TaskContext, saved_sp),
        slow = sym morestack_slow,
    )
}

/// The Rust half of `rt_morestack`, running on the system stack. `sp` is the
/// address of the register save area on the fiber stack.
///
/// # Safety
///
/// Called only by `rt_morestack`, while a worker runs the fiber of `ctx`.
unsafe extern "C" fn morestack_slow(ctx: *const TaskContext, needed: usize, sp: usize) -> Resume {
    // SAFETY: `Worker::resume` stored the fiber's address in the context and
    // touches the fiber only through that pointer while it runs. The fiber is
    // suspended inside `rt_morestack`, so nothing else uses its stack.
    unsafe {
        let ctx = &*ctx;
        let fiber = &mut *ctx.fiber.load(Ordering::Relaxed);

        let pending = take_pending(ctx);

        // Redo the comparison against the real limit: the check may have
        // failed only because of the sentinel.
        let mut sp = sp;
        let check_sp = sp + SAVE_BYTES;
        if check_sp.wrapping_sub(needed) < fiber.limit || check_sp < needed {
            sp = grow_stack(fiber, needed, sp);
        }
        finish_check(ctx, fiber.limit);

        let stop = if pending & StopReason::Pause as usize != 0 {
            fiber.state = FiberState::Paused;
            1
        } else if pending & StopReason::Preempt as usize != 0 {
            fiber.state = FiberState::Runnable;
            1
        } else {
            0
        };
        Resume { sp, stop }
    }
}

/// Moves the fiber to a larger stack and returns the new address of the
/// save area at `sp`.
///
/// The used part of the old stack, from `sp` to the top, is copied to the
/// top of the new one, so every byte keeps its distance from the top. The
/// only pointers into the stack are the saved frame pointers, which form a
/// chain from the save area's rbp slot to the fiber's first frame; each is
/// moved by the distance between the two stacks.
///
/// # Safety
///
/// The fiber must be suspended in `rt_morestack` with its save area at `sp`,
/// and the caller must be running on another stack.
unsafe fn grow_stack(fiber: &mut Fiber, needed: usize, sp: usize) -> usize {
    let old_low = fiber.stack.low();
    let old_top = fiber.stack.top();
    if !(old_low..old_top).contains(&sp) {
        die("stack check failed outside the fiber's stack");
    }
    let used = old_top - sp;
    // After the move, the check must pass with the margin intact below the
    // limit: check_sp - needed >= low + STACK_MARGIN.
    let check_used = used - SAVE_BYTES;
    let required = check_used + needed + STACK_MARGIN as usize;
    let size = if fiber.config.torture {
        required
    } else {
        required.max(2 * fiber.stack.size())
    };
    if size > fiber.config.max_stack {
        die("stack overflow: a fiber's stack reached its maximum size");
    }
    let new = match StackMemory::new(size) {
        Ok(stack) => stack,
        Err(_) => die("out of memory while growing a fiber's stack"),
    };

    let new_sp = new.top() - used;
    let delta = new.top().wrapping_sub(old_top);
    // SAFETY: both ranges are `used` bytes inside their mappings, which are
    // distinct. The chain walk reads and writes only slots that lie inside
    // the copied range, which is checked for every link before it is used.
    unsafe {
        std::ptr::copy_nonoverlapping(sp as *const u8, new_sp as *mut u8, used);

        let mut slot = new_sp + RBP_SLOT;
        loop {
            let old_fp = (slot as *const usize).read();
            if old_fp == 0 {
                break; // The first frame: `Fiber::new` started the chain with zero.
            }
            let new_fp = old_fp.wrapping_add(delta);
            // Each link must point further up the stack and stay inside it.
            if new_fp <= slot || new_fp > new.top() - 8 || new_fp % 8 != 0 {
                die("corrupt frame-pointer chain while growing a stack");
            }
            (slot as *mut usize).write(new_fp);
            slot = new_fp;
        }
    }

    // In stress mode, set the limit so that the failed check just passes
    // and the next call fails again.
    fiber.limit = if fiber.config.torture {
        new.top() - check_used - needed
    } else {
        new.low() + STACK_MARGIN as usize
    };
    fiber.stack = new; // Unmaps the old stack.
    fiber.growths += 1;
    new_sp
}
