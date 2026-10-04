//! Per-fiber bump region that never moves, for address-taken values (Plan §11.3.3).
//!
//! The machine stack is copied when it grows, so nothing may point into it.
//! A value whose address is taken lives here instead. The side stack is a
//! list of chunks: when one is full another is added, and no chunk ever
//! moves, so an address stays valid until the function that pushed the value
//! returns.
//!
//! Pushing and popping are inline generated code working on two fields of
//! the task context (see `crag_abi`). The runtime is involved only when a
//! push does not fit the current chunk.

use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::mem::offset_of;
use std::sync::atomic::Ordering;

use crag_abi::RUNTIME_RESERVE;

use crate::fiber::TaskContext;
use crate::stack::{SAVE_BYTES, restore_registers, save_registers};

/// Alignment of every chunk's first byte.
const CHUNK_ALIGN: usize = 16;

struct Chunk {
    base: *mut u8,
    size: usize,
}

impl Chunk {
    fn new(size: usize) -> Chunk {
        let layout = Layout::from_size_align(size, CHUNK_ALIGN).expect("chunk size overflows");
        // SAFETY: the layout has a non-zero size; `SideStack::grow` never
        // asks for an empty chunk.
        let base = unsafe { alloc(layout) };
        if base.is_null() {
            handle_alloc_error(layout);
        }
        Chunk { base, size }
    }

    fn start(&self) -> usize {
        self.base as usize
    }

    fn end(&self) -> usize {
        self.base as usize + self.size
    }
}

impl Drop for Chunk {
    fn drop(&mut self) {
        // SAFETY: `base` came from `alloc` with this same layout.
        unsafe {
            dealloc(
                self.base,
                Layout::from_size_align_unchecked(self.size, CHUNK_ALIGN),
            )
        };
    }
}

/// The chunks of one fiber's side stack, in the order they were entered.
/// Which chunk is current, and how full it is, is in the task context.
pub(crate) struct SideStack {
    chunks: Vec<Chunk>,
    chunk_size: usize,
}

impl SideStack {
    pub(crate) fn new(chunk_size: usize) -> SideStack {
        SideStack {
            chunks: Vec::new(),
            chunk_size: chunk_size.max(CHUNK_ALIGN),
        }
    }

    pub(crate) fn chunks(&self) -> usize {
        self.chunks.len()
    }

    /// Whether a bump pointer of `ptr` means nothing is pushed: it is the
    /// initial null, or the start of the first chunk.
    pub(crate) fn is_empty_at(&self, ptr: usize) -> bool {
        ptr == 0 || self.chunks.first().is_some_and(|c| c.start() == ptr)
    }

    /// Finds room for `size` bytes at alignment `align` after the chunk that
    /// ends at `current_end`, and returns the start and end of that room's
    /// chunk.
    ///
    /// Chunks after the current one hold nothing live: they were entered by
    /// calls that have returned. The next one is reused if it is large
    /// enough; otherwise they are freed and a new chunk takes their place.
    fn grow(&mut self, current_end: usize, size: usize, align: usize) -> (usize, usize) {
        // Enough for the value wherever alignment puts it in the chunk.
        let needed = size + align.max(1);
        let next = match self.chunks.iter().position(|c| c.end() == current_end) {
            Some(current) => current + 1,
            None => 0, // No chunk is current yet.
        };
        if self.chunks.get(next).is_none_or(|c| c.size < needed) {
            self.chunks.truncate(next);
            self.chunks.push(Chunk::new(needed.max(self.chunk_size)));
        }
        let chunk = &self.chunks[next];
        (chunk.start(), chunk.end())
    }
}

// The routine's save area must fit the reserve below the stack limit.
const _: () = assert!(SAVE_BYTES <= RUNTIME_RESERVE as usize);

/// `rt_side_grow(ctx, size, align)`: see `crag_abi::RuntimeFn::SideGrow`.
///
/// Preserves every register, like `rt_morestack`, and runs its Rust half on
/// the system stack. The machine stack does not move here.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_side_grow(ctx: *const TaskContext, size: usize, align: usize) {
    std::arch::naked_asm!(
        save_registers!(),
        // The arguments are still in rdi, rsi and rdx. Keep the fiber's stack
        // pointer in a register the Rust function preserves.
        "mov rbx, rsp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {slow}",
        "mov rsp, rbx",
        restore_registers!(),
        "ret",
        worker = const offset_of!(TaskContext, worker),
        slow = sym side_grow_slow,
    )
}

/// The Rust half of `rt_side_grow`, running on the system stack.
///
/// # Safety
///
/// Called only by `rt_side_grow`, while a worker runs the fiber of `ctx`.
unsafe extern "C" fn side_grow_slow(ctx: *const TaskContext, size: usize, align: usize) {
    // SAFETY: `Worker::resume` stored the fiber's address in the context and
    // uses the fiber only through that pointer while it runs.
    unsafe {
        let ctx = &*ctx;
        let fiber = &mut *ctx.fiber.load(Ordering::Relaxed);
        let current_end = ctx.side_end.load(Ordering::Relaxed);
        let (start, end) = fiber.side.grow(current_end, size, align);
        ctx.side_ptr.store(start, Ordering::Relaxed);
        ctx.side_end.store(end, Ordering::Relaxed);
    }
}
