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

//! The boundary between generated code and the runtime (Compiler
//! Architecture §10): the constants both sides must agree on.
//!
//! The code generator bakes these values into machine code and the runtime
//! lays out its memory to match, so neither crate depends on the other. The
//! code object, which the host compiles and an image loads, is defined here
//! for the same reason.
//!
//! # The stack check
//!
//! Cranelift emits the prologue itself, so a function's frame is already
//! allocated when its first instruction runs. The check is therefore explicit
//! code at the start of the entry block, and it runs *after* the frame exists:
//!
//! ```text
//! if sp < ctx.stack_limit { rt_morestack(ctx, 0) }
//! ```
//!
//! That is sound because `stack_limit` is not the end of the stack. The
//! runtime keeps [`STACK_MARGIN`] usable bytes below it:
//!
//! ```text
//! high addresses
//!   | frames of callers                          |
//!   | ...                                        |  sp >= stack_limit after
//!   +--------------------------------------------+  every passed check
//!   | stack_limit                                |
//!   |   FRAME_BUDGET: one unchecked frame        |
//!   |   RUNTIME_RESERVE: entry into the runtime  |
//!   +--------------------------------------------+  stack_limit - STACK_MARGIN
//!   | guard page                                 |
//! low addresses
//! ```
//!
//! A function whose frame footprint is at most [`FRAME_BUDGET`] may allocate
//! its frame before checking: its caller passed a check, so the frame lands
//! inside the margin, and [`RUNTIME_RESERVE`] bytes remain for the call into
//! the runtime if the check fails.
//!
//! A function with a larger footprint is entered through a small wrapper that
//! checks the size first and then tail-calls the body:
//!
//! ```text
//! if sp - footprint < ctx.stack_limit { rt_morestack(ctx, footprint) }
//! ```
//!
//! Loop back-edges repeat the first form, which is what lets the runtime stop
//! a fiber by storing [`STACK_LIMIT_SENTINEL`] in `stack_limit`.
//!
//! # The side stack
//!
//! Values whose address is taken live on a per-fiber side stack that never
//! moves (Compiler Architecture §2.1). It is a chain of chunks; the task
//! context holds the bump pointer and the end of the current chunk. A push is
//! inline code:
//!
//! ```text
//! loop {
//!     p = align_up(ctx.side_ptr, align)
//!     if p + size <= ctx.side_end { ctx.side_ptr = p + size; break }
//!     rt_side_grow(ctx, size, align)
//! }
//! ```
//!
//! A function that pushes saves both fields on entry and stores them back
//! before it returns or tail-calls, which frees everything it pushed.

/// Offset of `stack_limit` in the task context, in bytes. It is the first
/// field, so the check loads it with no displacement.
pub const STACK_LIMIT_OFFSET: i32 = 0;

/// Offset of the side stack's bump pointer in the task context: the next free
/// byte of the current chunk.
pub const SIDE_PTR_OFFSET: i32 = 8;

/// Offset of the end of the side stack's current chunk in the task context.
pub const SIDE_END_OFFSET: i32 = 16;

/// Offset of the worker's heap in the task context, which generated code
/// allocates from inline (Implementation Plan §11.4.11).
pub const HEAP_OFFSET: i32 = 24;

/// The value the runtime stores in `stack_limit` to force the next check into
/// the runtime (Plan §11.3.4). The check compares unsigned, so no stack
/// pointer passes it.
pub const STACK_LIMIT_SENTINEL: usize = usize::MAX;

/// Largest frame footprint a function may allocate before its check has run.
/// The footprint counts everything a call adds below the caller's stack
/// pointer: the return address, the saved frame pointer, the frame itself and
/// any growth of the argument area for tail calls.
pub const FRAME_BUDGET: u32 = 512;

/// Bytes a runtime entry point may use on the fiber stack before it switches
/// to the system stack.
pub const RUNTIME_RESERVE: u32 = 512;

/// Usable bytes the runtime keeps below `stack_limit`.
pub const STACK_MARGIN: u32 = FRAME_BUDGET + RUNTIME_RESERVE;

/// Runtime functions that generated code calls. Code objects name them in
/// relocations; the loader resolves them to addresses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum RuntimeFn {
    /// `rt_morestack(ctx: *mut TaskContext, needed: usize)`.
    ///
    /// Called when a stack check fails. It takes its arguments in the first
    /// two argument registers of the C calling convention and preserves every
    /// register, vector registers included, so the call costs the passing
    /// path nothing. It is therefore an assembly routine, not a Rust function.
    /// The runtime handles a pending stop
    /// request if `stack_limit` holds the sentinel, then grows the stack
    /// until `sp - needed >= stack_limit`. `needed` is zero for the ordinary
    /// check and the body's footprint for the sized check. It returns into
    /// the same frame, which may have moved to a new stack.
    Morestack = 0,

    /// `rt_side_grow(ctx: *mut TaskContext, size: usize, align: usize)`.
    ///
    /// Called when a side-stack push does not fit the current chunk. The
    /// runtime makes the side-stack fields of the context describe a chunk
    /// with room for `size` bytes at alignment `align`, and generated code
    /// then repeats the push. It has the same convention as `rt_morestack`:
    /// C argument registers, every register preserved, no result.
    SideGrow = 1,

    /// `rt_trap(ctx: *mut TaskContext, kind: u64) -> !`, with `kind` a
    /// [`TrapKind`].
    ///
    /// Called where a check fails; it never returns (Implementation Plan
    /// §11.4.14). The functions from here on have the C calling convention,
    /// take the task context first, and run on the system stack.
    Trap = 2,

    /// `rt_alloc(ctx: *mut TaskContext, size: u64, type_index: u64) -> *mut u8`.
    ///
    /// A box of `size` bytes, header included, with a count of one and the
    /// type index in its header (Implementation Plan §11.4.11).
    Alloc = 3,

    /// `rt_retain(ctx: *mut TaskContext, ptr: *mut u8)`: adds a reference to
    /// a box (Implementation Plan §11.4.12).
    Retain = 4,

    /// `rt_release(ctx: *mut TaskContext, ptr: *mut u8)`: gives up a
    /// reference to a box, releasing its fields and freeing it with the last.
    Release = 5,
}

impl RuntimeFn {
    /// Every runtime function, indexed by its discriminant.
    pub const ALL: [RuntimeFn; 6] = [
        RuntimeFn::Morestack,
        RuntimeFn::SideGrow,
        RuntimeFn::Trap,
        RuntimeFn::Alloc,
        RuntimeFn::Retain,
        RuntimeFn::Release,
    ];

    /// The symbol the loader looks up.
    pub fn symbol(self) -> &'static str {
        match self {
            RuntimeFn::Morestack => "rt_morestack",
            RuntimeFn::SideGrow => "rt_side_grow",
            RuntimeFn::Trap => "rt_trap",
            RuntimeFn::Alloc => "rt_alloc",
            RuntimeFn::Retain => "rt_retain",
            RuntimeFn::Release => "rt_release",
        }
    }

    /// The function with this discriminant, if any.
    pub fn from_index(index: u32) -> Option<RuntimeFn> {
        Self::ALL.get(index as usize).copied()
    }
}

/// Why generated code stopped a computation (Specification §8.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum TrapKind {
    Overflow = 0,
    DivideByZero = 1,
    /// An index outside the list.
    Index = 2,
    /// `???` was reached.
    Hole = 3,
    /// No arm of a `case` matched.
    NoMatch = 4,
    /// The function had compile errors.
    Error = 5,
    /// The compiler does not support what was reached yet.
    Unsupported = 6,
}

/// Bytes of a box's header: the count with its flag bits, then the type
/// index (Compiler Architecture §11.1). Fields follow it.
pub const HEADER_SIZE: u32 = 16;

/// Offset of the reference count in a box.
pub const COUNT_OFFSET: i32 = 0;

/// Offset of the type index in a box, a word whose upper half is zero.
pub const TYPE_INDEX_OFFSET: i32 = 8;

/// Bytes of the largest block the heap allocates from pages of a size class.
/// A larger box is a mapping of its own, allocated by `rt_alloc` alone.
pub const SMALL_SIZE_MAX: u32 = 8192;

/// Number of size classes.
pub const SIZE_CLASSES: usize = 36;

/// The size class of a block of `size` bytes, if the heap has one: a class
/// per word up to 64 bytes, then four per doubling up to
/// [`SMALL_SIZE_MAX`]. Code generation and the heap must agree on it, so it
/// is here.
pub const fn size_class(size: u32) -> Option<u32> {
    if size == 0 || size > SMALL_SIZE_MAX {
        None
    } else if size <= 64 {
        Some(size.div_ceil(8) - 1)
    } else {
        let w = size - 1;
        let top = 31 - w.leading_zeros();
        Some(8 + (top - 6) * 4 + ((w >> (top - 2)) & 3))
    }
}

/// The bytes of a block of `class`, the largest size in it.
pub const fn class_size(class: u32) -> u32 {
    if class < 8 {
        (class + 1) * 8
    } else {
        let top = 6 + (class - 8) / 4;
        (1 << top) + ((class - 8) % 4 + 1) * (1 << (top - 2))
    }
}

// The heap: the page each size class currently allocates from, one word per
// class from the heap's first byte. A class without free blocks has a page
// whose free list is empty, never a null page, so the inline path needs one
// test only:
//
// ```text
// page = ctx.heap.pages[class]
// block = page.free
// if block == 0 { block = rt_alloc(ctx, size, type_index) }
// else { page.free = block.next; page.used += 1; initialize the header }
// ```

/// Offset of the free list in a page: the first free block, whose first
/// word links the next.
pub const PAGE_FREE_OFFSET: i32 = 0;

/// Offset of the count of a page's blocks in use.
pub const PAGE_USED_OFFSET: i32 = 8;

/// Another Crag function, as generated code refers to it. The loader resolves
/// it to an address.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FuncId(pub u32);

/// The machine code of one function plus what the loader needs to place it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodeObject {
    /// Machine code. It may hold more than one routine; execution starts at
    /// `entry`.
    pub code: Vec<u8>,
    /// Required alignment of `code` in bytes, a power of two.
    pub align: u32,
    /// Offset of the entry point in `code`.
    pub entry: u32,
    /// Places the loader patches with addresses.
    pub relocs: Vec<Reloc>,
    /// Bytes one call of this function adds below its caller's stack pointer:
    /// return address, saved frame pointer, frame, and growth of the argument
    /// area for tail calls. The last part is an upper bound.
    pub footprint: u32,
    /// Which stack check guards the entry.
    pub stack_check: StackCheck,
    /// Where the tracked values are at each call, ordered by offset.
    pub stack_maps: Vec<StackMap>,
}

/// The tracked values of one frame while it is suspended at a call.
///
/// Every call in generated code is a safepoint: the runtime may inspect the
/// stack while the frame waits for the call to return, and `rt_morestack` is
/// such a call. At a safepoint each live tracked value is in a stack slot,
/// not in a register.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackMap {
    /// Offset in `CodeObject::code` of the instruction after the call, which
    /// is the return address found on the stack.
    pub return_offset: u32,
    /// Offsets of the slots from the frame's stack pointer at the call.
    pub slots: Vec<u32>,
}

/// The form of the entry stack check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StackCheck {
    /// No check: the entry stub, which runs on the system stack.
    None,
    /// `sp < limit` after the frame is allocated. Used when the footprint
    /// fits [`FRAME_BUDGET`].
    Margin,
    /// `sp - needed < limit` in a wrapper, before the frame is allocated.
    Sized { needed: u32 },
}

/// One place in the code to patch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reloc {
    /// Offset in `CodeObject::code` of the bytes to patch.
    pub offset: u32,
    pub kind: RelocKind,
    pub target: RelocTarget,
    /// Added to the target's address.
    pub addend: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelocKind {
    /// Write the 64-bit absolute address, little-endian.
    Abs64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelocTarget {
    /// The entry point of another Crag function.
    Function(FuncId),
    /// A runtime function.
    Runtime(RuntimeFn),
    /// An offset into this code object's own `code`.
    Local(u32),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_classes_cover_each_size_with_the_smallest_class() {
        assert_eq!(size_class(SMALL_SIZE_MAX), Some(SIZE_CLASSES as u32 - 1));
        assert_eq!(class_size(SIZE_CLASSES as u32 - 1), SMALL_SIZE_MAX);
        assert_eq!(size_class(0), None);
        assert_eq!(size_class(SMALL_SIZE_MAX + 1), None);
        for size in 1..=SMALL_SIZE_MAX {
            let class = size_class(size).unwrap();
            assert!(class_size(class) >= size, "{size}");
            assert!(class == 0 || class_size(class - 1) < size, "{size}");
        }
        for class in 0..SIZE_CLASSES as u32 {
            assert!(class_size(class).is_multiple_of(8));
            assert_eq!(size_class(class_size(class)), Some(class));
        }
    }
}
