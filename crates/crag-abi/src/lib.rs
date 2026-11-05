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
//! for the same reason, with the messages that carry it ([`protocol`]) and
//! the tables a release executable starts from ([`release`]).
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

pub mod protocol;
pub mod release;
pub mod wire;

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

/// Offset of the fuel of metered code in the task context (Implementation
/// Plan §11.6.6), a signed word. Metered code takes a step off it at each
/// function entry and loop back-edge:
///
/// ```text
/// ctx.fuel -= 1
/// if ctx.fuel < 0 { rt_refuel(ctx) }
/// ```
///
/// The runtime gives a task its steps a portion at a time, so a refill is
/// also where it notices that a budget is used up. Other code never reads
/// the fuel.
pub const FUEL_OFFSET: i32 = 32;

/// Offset of the conflict word in the task context, nonzero once a ref
/// function found that the running transaction's attempt must rerun
/// (Implementation Plan §11.7.14). Generated code reads it after each ref
/// function that reads a cell and leaves the attempt: to its block's handler
/// inside an `atomic` block, else by `TxThrow`. `TxRetry` clears it.
pub const TX_CONFLICT_OFFSET: i32 = 40;

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

/// Defines an enumeration whose variants are numbered from zero, each with
/// a value: the type, `ALL` of its variants in order, `from_index` for the
/// variant with a discriminant, and the function giving the values. The
/// numbers are checked to be the positions, so that one list keeps the
/// four in step.
macro_rules! table {
    (
        $(#[$meta:meta])*
        pub enum $name:ident {
            $($(#[$doc:meta])* $variant:ident = $index:literal => $value:expr,)*
        }
        $(#[$fn_doc:meta])*
        fn $value_fn:ident -> $ty:ty;
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        #[repr(u32)]
        pub enum $name {
            $($(#[$doc])* $variant = $index,)*
        }

        impl $name {
            /// Every one, indexed by its discriminant.
            pub const ALL: [$name; [$($index),*].len()] = [$($name::$variant),*];

            /// The one with this discriminant, if any.
            pub fn from_index(index: u64) -> Option<$name> {
                Self::ALL.get(usize::try_from(index).ok()?).copied()
            }

            $(#[$fn_doc])*
            pub fn $value_fn(self) -> $ty {
                match self {
                    $($name::$variant => $value,)*
                }
            }
        }

        const _: () = {
            let mut i = 0;
            while i < $name::ALL.len() {
                assert!($name::ALL[i] as usize == i, "a discriminant out of order");
                i += 1;
            }
        };
    };
}

mod runtime_fn;
mod shape;

pub use runtime_fn::*;
use shape::read_le;
pub use shape::*;

table! {
    /// Why generated code stopped a computation (Specification §8.3).
    pub enum TrapKind {
        Overflow = 0 => "arithmetic overflow",
        DivideByZero = 1 => "division by zero",
        /// An index outside the list.
        Index = 2 => "index out of range",
        /// `???` was reached.
        Hole = 3 => "reached `???`",
        /// No arm of a `case` matched.
        NoMatch = 4 => "no arm of `case` matched",
        /// The function had compile errors.
        Error = 5 => "reached code with errors",
        /// The compiler does not support what was reached yet.
        Unsupported = 6 => "reached code the compiler does not support yet",
        /// Metered code used up its steps.
        OutOfSteps = 7 => "ran out of steps",
        /// Metered code used up its memory budget.
        OutOfMemory = 8 => "ran out of memory",
        /// The task was cancelled (Specification §10.4), or the runtime's poll
        /// at a refill asked metered code to stop, as the host does when an
        /// edit cancels a compile-time evaluation.
        Cancelled = 9 => "was cancelled",
        /// A lazy value's computation read the value itself.
        Cycle = 10 => "a lazy value needed itself",
        /// The environment failed an operation that has no error value, such
        /// as writing to a closed standard output (Specification §8.3, §15.6).
        Fault = 11 => "the environment failed",
        /// Values without an order were compared: functions, maps or sets
        /// (Specification §19.11).
        Unordered = 12 => "compared values that have no order",
        /// `!!` met an error (Specification §8.4).
        Expectation = 13 => "`!!` met an error",
        /// A value failed a condition of its type (Specification §3.10.1).
        ConditionFailed = 14 => "a value failed a condition of its type",
        /// `number()` met a NaN or an infinity (Specification §3.1.4).
        NotFinite = 15 => "a number was not finite",
        /// A C function broke what its import declares (Specification §16.1).
        ForeignFault = 16 => "a C function broke what its import declares",
        /// A fiber's stack would grow past its maximum size.
        StackOverflow = 17 => "the stack overflowed",
    }
    /// What a trap of the kind tells the user.
    fn message -> &'static str;
}

impl TrapKind {
    /// Whether a trap handler may take a trap of the kind: cancellation
    /// is no trap (Specification §10.4), and code with errors or the
    /// compiler's gaps are not the program's.
    pub fn catchable(self) -> bool {
        !matches!(
            self,
            TrapKind::Cancelled | TrapKind::Error | TrapKind::Unsupported
        )
    }
}

/// The position `rt_trap` receives when the trap has no source expression.
pub const NO_POSITION: u64 = u64::MAX;

/// Bytes of a box's header: the count with its flag bits, then the type
/// index (Compiler Architecture §11.1). Fields follow it.
pub const HEADER_SIZE: u32 = 16;

/// Offset of the reference count in a box.
pub const COUNT_OFFSET: i32 = 0;

/// Offset of the type index in a box. The word's upper half is zero in
/// every box generated code sees; the nodes of a collection, which only the
/// runtime sees, carry their kind there.
pub const TYPE_INDEX_OFFSET: i32 = 8;

// Reference counts are atomic, because boxes are shared across threads. A
// count with its top bit set, [`STATIC_COUNT`], belongs to a value that is
// never freed, such as a literal in the image, and is never changed.
// Generated code counts inline:
//
// ```text
// retain(p):  if p.count >= 0 { atomic p.count += 1 }
// release(p): if p.count >= 0 and (atomic p.count -= 1) == 1 { rt_release(ctx, p) }
// ```
//
// Comparisons are signed, and the decrement yields the count before it.

/// The count of a static box, or any count with this bit set.
pub const STATIC_COUNT: u64 = 1 << 63;

/// What the runtime needs to know of a box's type to free it, and of a
/// collection's elements to store them. Code generation describes each type
/// it allocates, and the image indexes the descriptors by type index.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeDescriptor {
    /// A record: the fields that hold counted references, and for a type
    /// with a dispose handler the offset of the word that holds the
    /// address of its dispose code, zero once the handler has run.
    Record {
        counted: Vec<CountedField>,
        dispose: Option<u32>,
    },
    /// A list, whose elements each take `element.words` words, and how a
    /// lazy value, a stream, a hub or a signal whose values are of the
    /// element type holds one: in `cell`, its layout's words with a flat
    /// record in its box, where the list may store it flat (Compiler
    /// Architecture §A11.4). A ref holds one as `ref_cell` says: a flat
    /// record or union of at most 16 bytes in its storage form, anything
    /// else as in `cell`.
    List {
        element: ElementLayout,
        cell: ElementLayout,
        ref_cell: ElementLayout,
    },
    /// A map, or a set when the value has no words. Keys are equal when
    /// their words are, so a key holds no reference and no `Float`, or,
    /// with `text_keys`, each key is a string or bytes, equal to another
    /// when their bytes are.
    Map {
        key: ElementLayout,
        value: ElementLayout,
        text_keys: bool,
    },
}

/// A field of a box that may hold a reference.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CountedField {
    /// A box pointer at this offset, or a word that points at none: null,
    /// as the environment of a function value without one is, or a word
    /// with its lowest bit set, as the first word of an inline string is.
    Box(u32),
    /// A union at this offset: its type index, then its payload, which is a
    /// box pointer when the index is one of `boxed`, sorted.
    Union { offset: u32, boxed: Vec<u32> },
    /// A word at this offset as `Box` has it, there only when each guard
    /// holds: in a union stored flat, the member it belongs to is the one
    /// (Compiler Architecture §A11.4).
    Guarded {
        offset: u32,
        guards: Vec<FieldGuard>,
    },
    /// The lock of an `ext` binding at this offset, from `ExtNew`, which
    /// the runtime frees with the box (Implementation Plan §11.7.14). No
    /// reference: it is never counted.
    Ext(u32),
    /// The cell of a lazy value at this offset, from `LazyNew`, which the
    /// runtime frees with the box, giving up the value it holds.
    Lazy(u32),
    /// An end of a stream at this offset, which the runtime disposes of
    /// with the box: the other side reads `Abandoned` unless it was closed.
    Stream(u32),
    /// A hub at this offset, whose handle the runtime gives up with the
    /// box.
    Hub(u32),
    /// A socket's file descriptor at this offset, which the runtime closes
    /// with the box.
    Socket(u32),
}

/// What must hold for a guarded field to be there.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FieldGuard {
    /// The byte at `offset`, a union's local tag, is one of `tags`.
    Tag { offset: u32, tags: Vec<u8> },
    /// The `size` bytes at `offset`, little-endian, do not hold `value`,
    /// the niche that stands for the union's other member.
    NotValue { offset: u32, size: u8, value: u64 },
    /// The bit of the byte at `offset` is clear.
    BitClear { offset: u32, bit: u8 },
}

impl FieldGuard {
    /// The end of the bytes the guard reads.
    pub fn end(&self) -> u32 {
        match self {
            FieldGuard::Tag { offset, .. } | FieldGuard::BitClear { offset, .. } => offset + 1,
            FieldGuard::NotValue { offset, size, .. } => offset + u32::from(*size),
        }
    }

    /// Whether the guard holds for the bytes of a box.
    pub fn holds(&self, bytes: &[u8]) -> bool {
        match self {
            FieldGuard::Tag { offset, tags } => tags.contains(&bytes[*offset as usize]),
            FieldGuard::NotValue {
                offset,
                size,
                value,
            } => read_le(bytes, *offset, u32::from(*size)) != *value,
            FieldGuard::BitClear { offset, bit } => bytes[*offset as usize] >> bit & 1 == 0,
        }
    }
}

/// How a value lies inside a collection or a cell: its bytes, at most 32,
/// aligned to `align`, with the fields that hold references at their
/// offsets from its first byte. A collection holds a flat record or union,
/// a sized integer or a union of tags in its storage form (Compiler
/// Architecture §A11.3, §A11.4), so its bytes may be fewer than a word,
/// and a ref cell a flat record or union of at most 16 bytes; anything
/// else, and every value in another cell, takes the words of its layout. Generated code passes a value to the runtime in the words its
/// bytes fill, or, when they are more than two, by the address of those
/// words, in the first word of the two it takes otherwise.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ElementLayout {
    pub size: u32,
    pub align: u32,
    pub counted: Vec<CountedField>,
}

impl ElementLayout {
    /// A value of `words` words, as one not stored flat takes.
    pub fn of_words(words: u32, counted: Vec<CountedField>) -> ElementLayout {
        ElementLayout {
            size: 8 * words,
            align: if words == 0 { 1 } else { 8 },
            counted,
        }
    }

    /// The words a value's bytes fill, as generated code passes it.
    pub fn words(&self) -> u32 {
        self.size.div_ceil(8)
    }
}

// A list or a map is a box that generated code allocates inline when it is
// empty, and the runtime then grows: the header, the number of elements,
// and then what only the runtime reads, zero in an empty one. Its nodes
// are boxes too, with the type index of the collection.

/// Offset of the number of elements, an `Int`, in a list or a map.
pub const LEN_OFFSET: i32 = 16;

/// Bytes of a list's box: the header, the length, the height of its tree
/// and the tree.
pub const LIST_SIZE: u32 = 40;

/// Bytes of a map's box: the header, the length, the root of its hash
/// index, the tree of its entries, the tree's height and its slots.
pub const MAP_SIZE: u32 = 56;

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

// Strings and bytes take two words (Compiler Architecture §11). A value
// of at most [`INLINE_TEXT_MAX`] bytes is inline: the lowest byte of the
// first word is its length shifted left by one, plus one, its bytes follow,
// and the bytes after them are zero:
//
// ```text
// inline:  w0 = len << 1 | 1 | b0 << 8 | ... | b6 << 56   w1 = b7 | ... | b14 << 56
// buffer:  w0 = buffer box                                w1 = start << 32 | len
// ```
//
// A longer value is in a buffer, a box of its bytes after the header with
// [`BUFFER_HEADER`] in place of a type index: the first word points at the
// buffer, the second holds where its bytes start in the buffer's bytes and
// how many it has. Boxes are aligned, so the lowest bit of the first word
// tells the forms apart, and counting a value counts its buffer when it has
// one. A value of at most 15 bytes is never in a buffer, so two values are
// equal when their words are, and otherwise when both are in buffers that
// hold the same bytes. A literal's buffer is static data of its code.

/// The most bytes a string or bytes value holds inline.
pub const INLINE_TEXT_MAX: usize = 15;

/// The type index word of a buffer of a string or bytes. It names no type
/// and no node kind, and the runtime frees such a box without a descriptor.
pub const BUFFER_HEADER: u64 = u64::MAX;

// A union is two words at most, a type index and a payload word, so a
// member of two words, a string, bytes or a function value, is kept in a
// member box: the header, with [`TEXT_BOX_HEADER`] or [`FUNCTION_BOX_HEADER`]
// in place of a type index, then the member's two words. The payload points
// at the box, which owns the member's references. The union's type index
// says which member it holds, so the box needs none; the runtime frees it
// without a descriptor, releasing the one word of the member that may hold
// a box.

/// The type index word of a member box holding a string or bytes value,
/// whose first word may be a buffer.
pub const TEXT_BOX_HEADER: u64 = u64::MAX - 1;

/// The type index word of a member box holding a function value, whose
/// second word may be an environment.
pub const FUNCTION_BOX_HEADER: u64 = u64::MAX - 2;

/// The size of a member box: the header and two words.
pub const MEMBER_BOX_SIZE: u32 = HEADER_SIZE + 16;

/// The offset of the word of a member box that may point at a box, by the
/// box's type index word; none for a box that is no member box.
pub fn member_box_field(header: u64) -> Option<u32> {
    match header {
        TEXT_BOX_HEADER => Some(HEADER_SIZE),
        FUNCTION_BOX_HEADER => Some(HEADER_SIZE + 8),
        _ => None,
    }
}

/// The most bytes a string or bytes value holds: its length is the lower
/// half of a word.
pub const TEXT_LEN_MAX: u64 = u32::MAX as u64;

/// The two words of an inline string or bytes value, which has at most
/// [`INLINE_TEXT_MAX`] bytes.
pub fn inline_text(bytes: &[u8]) -> [u64; 2] {
    assert!(
        bytes.len() <= INLINE_TEXT_MAX,
        "{} bytes inline",
        bytes.len()
    );
    let mut raw = [0u8; 16];
    raw[0] = (bytes.len() as u8) << 1 | 1;
    raw[1..=bytes.len()].copy_from_slice(bytes);
    let word = |k: usize| u64::from_le_bytes(raw[8 * k..8 * k + 8].try_into().unwrap());
    [word(0), word(1)]
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

/// A frame of a stack as traps and the debugger report it: a function,
/// and whether its code was inlined into the frame after it, so that it
/// had no frame of its own (Implementation Plan §11.10.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Frame {
    pub func: FuncId,
    pub inlined: bool,
}

impl Frame {
    /// A function's own frame.
    pub fn of(func: FuncId) -> Frame {
        Frame {
            func,
            inlined: false,
        }
    }
}

/// A slot of the slot table that development images call through
/// (Implementation Plan §11.6.4): a function with one signature. The host
/// numbers signatures; code compiled against one signature only reaches
/// code of that signature, so a definition that changes its signature
/// gets a new slot and the callers of the old one keep the old code.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SlotKey {
    pub func: FuncId,
    pub signature: u32,
}

/// The bytes of a module-level value's cell: a state word, then the value's
/// words, at most two (Implementation Plan §11.6.2). The code that computes
/// the value keeps it there, with a reference of its own.
pub const CELL_SIZE: usize = 32;
pub const CELL_STATE_OFFSET: i32 = 0;
pub const CELL_VALUE_OFFSET: i32 = 8;

/// The cells of a function's steps: the function's id with this bit and
/// the step's index as the signature. A slot's signature never has the
/// bit. A step's cell holds its flag in the state word: zero while the
/// debugger needs nothing there.
pub const STEP_CELL: u32 = 1 << 31;

/// The key of the cell of a step of `func`.
pub fn step_cell(func: FuncId, step: u32) -> SlotKey {
    SlotKey {
        func,
        signature: STEP_CELL | step,
    }
}

/// What the loader writes into the second word of a step's cell: the
/// function and the step it belongs to.
pub fn step_cell_word(key: SlotKey) -> u64 {
    (u64::from(key.func.0) << 32) | u64::from(key.signature & !STEP_CELL)
}

/// The function and step a step cell's second word names.
pub fn step_of_cell_word(word: u64) -> (FuncId, u32) {
    (FuncId((word >> 32) as u32), word as u32)
}

/// The cell baseline code counts its calls and loop back-edges in, for the
/// optimizing tier (Implementation Plan §11.10.2): the function's id with
/// signature zero, which no slot has. The state word counts calls, the
/// next word back-edges. Workers add without synchronizing, so a count
/// may miss some.
pub fn profile_cell(func: FuncId) -> SlotKey {
    SlotKey { func, signature: 0 }
}

pub const PROFILE_CALLS_OFFSET: i32 = CELL_STATE_OFFSET;
pub const PROFILE_LOOPS_OFFSET: i32 = CELL_VALUE_OFFSET;

/// The states of a cell: no value yet, or holding the value. A value that
/// needs itself is a compile error, so a value is never read while it is
/// computed.
pub const CELL_EMPTY: u64 = 0;
pub const CELL_FULL: u64 = 1;

/// The machine code of one function plus what the loader needs to place it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    /// The calls with a handler, which `TxThrow` or a trap continues at,
    /// ordered by offset.
    pub handlers: Vec<CallHandler>,
    /// The module of the code, which origins name.
    pub module: String,
    /// Where each position a trap of this code may name lies, ordered by
    /// position.
    pub origins: Vec<TrapOrigin>,
    /// The calls whose callee's code the optimizer copied into this code
    /// (Implementation Plan §11.10.1), which origins and `inlined_at`
    /// index from one.
    pub inlined: Vec<InlinedCode>,
    /// Where the code of inlined calls lies, ordered by offset, so that a
    /// return address in it is known to be in the callee.
    pub inlined_at: Vec<InlinedRange>,
    /// What traps of this code name beyond their kind, such as the type of
    /// the error `!!` met: the upper half of a trap's position word, from
    /// one, indexes it.
    pub details: Vec<String>,
    /// The C functions the code calls, which `RelocTarget::Native` and
    /// `RelocTarget::NativeLibrary` index.
    pub natives: Vec<NativeSymbol>,
}

/// The line and column, from one, of a position a trap of the code names:
/// the byte offset in the source of the code's module, or, in the code of
/// an inlined call, [`INLINED_POSITION`] with a number of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TrapOrigin {
    pub position: u32,
    pub line: u32,
    pub column: u32,
    /// The inlined call whose code it is in, from one; zero for the
    /// code's own.
    pub inlined: u32,
    /// The byte offset in the source of the module the position is in.
    pub offset: u32,
}

/// The bit of a trap's position that marks it as one in the code of an
/// inlined call: source offsets stay below it.
pub const INLINED_POSITION: u32 = 1 << 31;

/// A call whose callee's code is part of another function's code.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InlinedCode {
    /// The callee, then the inlined calls whose code made the call in
    /// turn, innermost first; the function the code belongs to is not
    /// among them.
    pub frames: Vec<FuncId>,
    /// The callee's module, where the positions of its code lie.
    pub module: String,
}

/// A run of an inlined call's code, as offsets in `CodeObject::code`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InlinedRange {
    pub start: u32,
    pub end: u32,
    /// The call, from one, in `CodeObject::inlined`.
    pub inlined: u32,
}

/// What a call's handler takes over from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HandlerKind {
    /// Leaving a transaction's attempt (Implementation Plan §11.7.14).
    Transaction,
    /// A trap (Specification §8.3.1).
    Trap,
}

/// A call whose frame takes over when the code it called leaves a
/// transaction's attempt (Implementation Plan §11.7.14). The handler
/// expects the frame pointer the frame had and the stack pointer
/// `frame_offset` below it, and nothing else in registers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CallHandler {
    /// Offset in `CodeObject::code` of the return address of the call.
    pub return_offset: u32,
    /// Offset in `CodeObject::code` of the handler.
    pub handler_offset: u32,
    /// From the frame pointer down to the stack pointer at the call.
    pub frame_offset: u32,
    pub kind: HandlerKind,
}

/// The tracked values of one frame while it is suspended at a call.
///
/// Every call in generated code is a safepoint: the runtime may inspect the
/// stack while the frame waits for the call to return, and `rt_morestack` is
/// such a call. At a safepoint each live tracked value is in a stack slot,
/// not in a register.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StackMap {
    /// Offset in `CodeObject::code` of the instruction after the call, which
    /// is the return address found on the stack.
    pub return_offset: u32,
    /// Offsets of the slots from the frame's stack pointer at the call.
    pub slots: Vec<u32>,
}

/// The form of the entry stack check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Reloc {
    /// Offset in `CodeObject::code` of the bytes to patch.
    pub offset: u32,
    pub kind: RelocKind,
    pub target: RelocTarget,
    /// Added to the target's address.
    pub addend: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelocKind {
    /// Write the 64-bit absolute address, little-endian.
    Abs64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelocTarget {
    /// The entry point of another Crag function.
    Function(FuncId),
    /// A runtime function.
    Runtime(RuntimeFn),
    /// An offset into this code object's own `code`.
    Local(u32),
    /// The slot of a function, which holds its entry point.
    Slot(SlotKey),
    /// The cell of a module-level value, by the slot key of the code that
    /// computes it.
    Cell(SlotKey),
    /// The address of a C function, by its index in the code object's
    /// `natives`.
    Native(u32),
    /// The [`NativeLibrary`] of the C function at that index.
    NativeLibrary(u32),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inline_text_keeps_its_length_and_bytes() {
        assert_eq!(inline_text(b""), [1, 0]);
        assert_eq!(inline_text(b"a"), [3 | u64::from(b'a') << 8, 0]);
        let full = inline_text(b"abcdefghijklmno");
        assert_eq!(full[0] & 0xff, 31);
        assert_eq!(full[1] >> 56, u64::from(b'o'));
        for n in [
            Number::Signed,
            Number::Unsigned,
            Number::Float,
            Number::CodePoint,
        ] {
            assert_eq!(Number::from_code(n.code()), Some(n));
        }
        assert_eq!(
            Number::from_code(Number::Fixed(3).code()),
            Some(Number::Fixed(3))
        );
    }

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
