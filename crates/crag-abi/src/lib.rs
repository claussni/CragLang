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
}

impl RuntimeFn {
    /// Every runtime function, indexed by its discriminant.
    pub const ALL: [RuntimeFn; 2] = [RuntimeFn::Morestack, RuntimeFn::SideGrow];

    /// The symbol the loader looks up.
    pub fn symbol(self) -> &'static str {
        match self {
            RuntimeFn::Morestack => "rt_morestack",
            RuntimeFn::SideGrow => "rt_side_grow",
        }
    }

    /// The function with this discriminant, if any.
    pub fn from_index(index: u32) -> Option<RuntimeFn> {
        Self::ALL.get(index as usize).copied()
    }
}

/// Another Crag function, as generated code refers to it. The loader resolves
/// it to an address.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FuncId(pub u32);

/// The machine code of one function plus what the loader needs to place it.
#[derive(Clone, Debug)]
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
