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

    /// `rt_trap(ctx: *mut TaskContext, kind: u64, position: u64) -> !`, with
    /// `kind` a [`TrapKind`] and `position` the byte offset of the
    /// expression that trapped in its module's source, or [`NO_POSITION`].
    ///
    /// Called where a check fails, after the frame has released what it
    /// holds; it never returns. It releases what the frames below hold, as
    /// their stack maps list it, and ends the fiber (Implementation Plan
    /// §11.4.14). The functions from here on have the C calling convention,
    /// take the task context first, and run on the system stack.
    Trap = 2,

    /// `rt_alloc(ctx: *mut TaskContext, size: u64, type_index: u64) -> *mut u8`.
    ///
    /// A box of `size` bytes, header included, with a count of one and the
    /// type index in its header (Implementation Plan §11.4.11).
    Alloc = 3,

    /// `rt_release(ctx: *mut TaskContext, ptr: *mut u8)`.
    ///
    /// Called when the inline decrement has taken a box's count from one to
    /// zero: releases the box's fields, using its type's descriptor, and
    /// frees it, and so on for every field whose count reaches zero
    /// (Implementation Plan §11.4.12). Retaining is inline code only.
    Release = 4,

    /// `rt_list_push(ctx, list, w0, w1) -> list`.
    ///
    /// The list with the element appended, whose words are `w0` and `w1`
    /// as far as its layout has words. It takes the list's reference and the
    /// element's, and updates in place what only that reference holds
    /// (Implementation Plan §11.4.13).
    ListPush = 5,

    /// `rt_list_elem(ctx, list, index) -> *const u64`.
    ///
    /// The address of the element's words, for an index inside the list. It
    /// borrows the list, and the address is valid while the list is.
    ListElem = 6,

    /// `rt_list_slice(ctx, list, front, back) -> list`.
    ///
    /// A new list of the elements without the first `front` and the last
    /// `back`, which together are at most the length. It borrows the list.
    ListSlice = 7,

    /// `rt_map_insert(ctx, map, k0, k1, v0, v1) -> map`.
    ///
    /// The map with the key bound to the value, words as for
    /// `rt_list_push`; a set is a map whose values have no words. It takes
    /// the references of the map, the key and the value.
    MapInsert = 8,

    /// `rt_map_get(ctx, map, k0, k1) -> *const u64`.
    ///
    /// The address of the words of the key's value, or null when the map
    /// has none. It borrows the map, and the address is valid while the map
    /// is.
    MapGet = 9,

    /// `rt_refuel(ctx: *mut TaskContext)`.
    ///
    /// Called by metered code when its fuel went negative. It has the
    /// convention of `rt_morestack`: every register preserved, no result.
    /// The runtime refills the fuel and returns, or, when the task's steps
    /// or its memory budget are used up, or the fiber's poll asks it to
    /// stop, traps with `OutOfSteps`, `OutOfMemory` or `Cancelled` as
    /// `rt_trap` would at this call, releasing what the
    /// frames hold as the call's stack map lists it.
    Refuel = 10,

    /// `rt_text_concat(ctx, a0, a1, b0, b1) -> (w0, w1)`.
    ///
    /// The string or bytes `a` followed by `b`, both borrowed, as a new
    /// value with a reference of its own (see [`INLINE_TEXT_MAX`]). Its
    /// two words come back in the first two result registers.
    TextConcat = 11,

    /// `rt_text_equals(ctx, a0, a1, b0, b1) -> u64`.
    ///
    /// 1 when the strings or bytes `a` and `b`, both borrowed, hold the
    /// same bytes, else 0.
    TextEquals = 12,

    /// `rt_text_show(ctx, word, number) -> (w0, w1)`.
    ///
    /// A number as a string, as interpolation writes it: the word, of the
    /// [`Number`] whose [`Number::code`] is `number`. A code point is its
    /// character.
    TextShow = 13,
}

impl RuntimeFn {
    /// Every runtime function, indexed by its discriminant.
    pub const ALL: [RuntimeFn; 14] = [
        RuntimeFn::Morestack,
        RuntimeFn::SideGrow,
        RuntimeFn::Trap,
        RuntimeFn::Alloc,
        RuntimeFn::Release,
        RuntimeFn::ListPush,
        RuntimeFn::ListElem,
        RuntimeFn::ListSlice,
        RuntimeFn::MapInsert,
        RuntimeFn::MapGet,
        RuntimeFn::Refuel,
        RuntimeFn::TextConcat,
        RuntimeFn::TextEquals,
        RuntimeFn::TextShow,
    ];

    /// The symbol the loader looks up.
    pub fn symbol(self) -> &'static str {
        match self {
            RuntimeFn::Morestack => "rt_morestack",
            RuntimeFn::SideGrow => "rt_side_grow",
            RuntimeFn::Trap => "rt_trap",
            RuntimeFn::Alloc => "rt_alloc",
            RuntimeFn::Release => "rt_release",
            RuntimeFn::ListPush => "rt_list_push",
            RuntimeFn::ListElem => "rt_list_elem",
            RuntimeFn::ListSlice => "rt_list_slice",
            RuntimeFn::MapInsert => "rt_map_insert",
            RuntimeFn::MapGet => "rt_map_get",
            RuntimeFn::Refuel => "rt_refuel",
            RuntimeFn::TextConcat => "rt_text_concat",
            RuntimeFn::TextEquals => "rt_text_equals",
            RuntimeFn::TextShow => "rt_text_show",
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
    /// Metered code used up its steps.
    OutOfSteps = 7,
    /// Metered code used up its memory budget.
    OutOfMemory = 8,
    /// The runtime's poll at a refill asked metered code to stop, as the
    /// host does when an edit cancels a compile-time evaluation.
    Cancelled = 9,
}

impl TrapKind {
    pub const ALL: [TrapKind; 10] = [
        TrapKind::Overflow,
        TrapKind::DivideByZero,
        TrapKind::Index,
        TrapKind::Hole,
        TrapKind::NoMatch,
        TrapKind::Error,
        TrapKind::Unsupported,
        TrapKind::OutOfSteps,
        TrapKind::OutOfMemory,
        TrapKind::Cancelled,
    ];

    /// The kind with this discriminant, if any.
    pub fn from_index(index: u64) -> Option<TrapKind> {
        Self::ALL.get(usize::try_from(index).ok()?).copied()
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
    /// A record: the fields that hold counted references.
    Record { counted: Vec<CountedField> },
    /// A list, whose elements each take `element.words` words.
    List { element: ElementLayout },
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
}

/// The words of a value inside a collection: at most two, with the fields
/// that hold references at their offsets from the value's first word.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ElementLayout {
    pub words: u32,
    pub counted: Vec<CountedField>,
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

/// Bytes of a map's box: the header, the length and the root node.
pub const MAP_SIZE: u32 = 32;

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
}

/// How a value of a type is printed (Implementation Plan §11.6.5): what
/// its words are and what they point to. The host describes the type; the
/// image walks the value. A type that contains itself refers back to its
/// shape by index, so a shape is a table.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Shapes {
    pub shapes: Vec<Shape>,
    /// The shapes of the record types a box may have, by the type index
    /// in its header: a value of a record type may be one of a subtype.
    pub records: Vec<(u32, u32)>,
    /// For each shape of a box, a record, a list, a set or a map: the
    /// shape, the type index in the box's header and the box's bytes, so
    /// a value can be built from its encoding (§11.6.8).
    pub boxes: Vec<(u32, u32, u32)>,
}

impl Shapes {
    /// The shape of a record by the type index of its box, if known.
    pub fn record(&self, index: u32) -> Option<u32> {
        self.records.iter().find(|r| r.0 == index).map(|r| r.1)
    }

    /// The type index and the bytes of the boxes of a shape, if known.
    pub fn boxed(&self, shape: u32) -> Option<(u32, u32)> {
        self.boxes
            .iter()
            .find(|b| b.0 == shape)
            .map(|&(_, index, size)| (index, size))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// `()`: no words.
    Unit,
    /// A tag, by its name: no words.
    Tag(String),
    /// A word.
    Number(Number),
    /// A union: the type index of the member, then in a two-word union the
    /// member's word. Each member by its type index.
    Union {
        members: Vec<(u32, u32)>,
        words: u32,
    },
    /// A box of a record type, named or anonymous, whose fields are at
    /// their offsets in it, in the order they are shown.
    Record {
        name: Option<String>,
        fields: Vec<ShapeField>,
    },
    /// A box of a list or a set: the element's shape.
    List(u32),
    Set(u32),
    /// A box of a map: the shapes of key and value.
    Map(u32, u32),
    /// A function value: two words.
    Function,
    /// A string or bytes value: two words.
    Str,
    Bytes,
    /// What cannot be shown yet, by its type, and its words.
    Opaque {
        name: String,
        words: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ShapeField {
    pub name: String,
    pub offset: u32,
    pub shape: u32,
}

/// How a word holds a number.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Number {
    /// A signed integer, sign-extended.
    Signed,
    /// An unsigned integer, zero-extended.
    Unsigned,
    /// The bits of a `Float`.
    Float,
    /// A `Fixed` with this many digits after the point, scaled.
    Fixed(u32),
    CodePoint,
}

impl Number {
    /// The number as one word, for `rt_text_show`.
    pub fn code(self) -> u64 {
        match self {
            Number::Signed => 0,
            Number::Unsigned => 1,
            Number::Float => 2,
            Number::CodePoint => 3,
            Number::Fixed(digits) => 4 + u64::from(digits),
        }
    }

    /// The number of a code, if any.
    pub fn from_code(code: u64) -> Option<Number> {
        Some(match code {
            0 => Number::Signed,
            1 => Number::Unsigned,
            2 => Number::Float,
            3 => Number::CodePoint,
            _ => Number::Fixed(u32::try_from(code.checked_sub(4)?).ok()?),
        })
    }
}

impl Shape {
    /// The words of a value of the shape.
    pub fn words(&self) -> u32 {
        match self {
            Shape::Unit | Shape::Tag(_) => 0,
            Shape::Number(_)
            | Shape::Record { .. }
            | Shape::List(_)
            | Shape::Set(_)
            | Shape::Map(..) => 1,
            Shape::Union { words, .. } | Shape::Opaque { words, .. } => *words,
            Shape::Function | Shape::Str | Shape::Bytes => 2,
        }
    }
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
