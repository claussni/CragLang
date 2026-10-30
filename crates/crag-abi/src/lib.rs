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
    /// as far as its layout has words, or of more than two words at the
    /// address in `w0` (`ElementLayout`). It takes the list's reference and the
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

    /// `rt_disposal(ctx) -> (ptr, code)`.
    ///
    /// The next box whose dispose handler must run, and the address of its
    /// dispose code, or two zeros when none waits (Implementation Plan
    /// §11.6.11). Freeing a box of a type with a handler does not free it:
    /// the runtime gives it a count of one again and queues it, since it
    /// never runs Crag code itself. Generated code calls this after every
    /// release that may free boxes, and calls each `code(ctx, ptr)`, which
    /// takes the reference. The runtime clears the box's word of the code
    /// first, so the next time its count reaches zero it is freed.
    Disposal = 14,

    /// `rt_yield(ctx)`.
    ///
    /// Gives the other fibers a turn: the fiber suspends, goes to the back
    /// of a run queue and continues when a worker picks it again
    /// (Implementation Plan §11.7.1). Like every runtime function that may
    /// suspend, it returns on the fiber stack it was called on, possibly
    /// on another thread, and it is a point where a cancelled task traps
    /// with `Cancelled` instead of returning (§11.7.4).
    Yield = 15,

    /// `rt_sleep(ctx, nanos)`.
    ///
    /// Suspends the fiber for at least `nanos` nanoseconds (Implementation
    /// Plan §11.7.2). The other fibers run meanwhile; a fiber that no
    /// scheduler runs blocks its thread.
    Sleep = 16,

    /// `rt_io_read(ctx, fd, buf, len) -> (n, errno)`.
    ///
    /// Reads at most `len` bytes from the non-blocking file descriptor `fd`
    /// into `buf`, suspending the fiber until some are there. Gives the
    /// count and zero, zero at the end of the input, or zero and the
    /// error number (Implementation Plan §11.7.2). `buf` must stay where it
    /// is until the call returns.
    IoRead = 17,

    /// `rt_io_write(ctx, fd, buf, len) -> (n, errno)`.
    ///
    /// Writes at most `len` bytes of `buf` to `fd`, suspending the fiber
    /// until some can go; gives the count written, or zero and the error
    /// number, as `IoRead` does.
    IoWrite = 18,

    /// `rt_io_accept(ctx, fd) -> (fd, errno)`.
    ///
    /// Accepts a connection on the listening socket `fd`, suspending the
    /// fiber until one comes. The new socket is non-blocking and closed on
    /// exec.
    IoAccept = 19,

    /// `rt_io_connect(ctx, fd, addr, len) -> (0, errno)`.
    ///
    /// Connects the non-blocking socket `fd` to the socket address of
    /// `len` bytes at `addr`, suspending the fiber until the connection is
    /// made or fails.
    IoConnect = 20,

    /// `rt_scope_new(ctx, limit) -> scope`.
    ///
    /// A scope for the tasks a combinator or group starts (Implementation
    /// Plan §11.7.3): at most `limit` of them run at once, any number for
    /// zero. The fiber that creates it is its parent; cancellation waits
    /// until the scope ends (`ScopeEnd`). Traps with `Unsupported` on a
    /// fiber that no scheduler runs.
    ScopeNew = 21,

    /// `rt_scope_start(ctx, scope, code, env, flags) -> index`.
    ///
    /// Starts a task of the scope that calls `code(ctx, env)`, the code and
    /// environment of a function value, which it takes. The low two bits of
    /// `flags` are the code's number of results; with [`START_EXEMPT`] the
    /// task does not count towards the limit. Suspends while the limit is
    /// reached. Gives the task's index, from zero in the order of starts.
    /// The parent and the scope's own tasks may start tasks.
    ScopeStart = 22,

    /// `rt_scope_next(ctx, scope) -> (index, status)`.
    ///
    /// The next task of the scope to finish, as [`TASK_RETURNED`],
    /// [`TASK_CANCELLED`] or [`TASK_TRAPPED`], suspending until one does;
    /// [`SCOPE_DONE`] when every task has been given. A task that traps
    /// cancels the others, and once all are given the scope ends and the
    /// parent traps with its kind. Only the parent calls it; a cancelled
    /// parent cancels the tasks and goes on giving them.
    ScopeNext = 23,

    /// `rt_scope_result(ctx, scope, index) -> (w0, w1)`.
    ///
    /// The results of a task that returned, taken once, with their
    /// references.
    ScopeResult = 24,

    /// `rt_scope_cancel(ctx, scope)`.
    ///
    /// Cancels every task of the scope that has not finished, and the tasks
    /// started later (Implementation Plan §11.7.4).
    ScopeCancel = 25,

    /// `rt_scope_end(ctx, scope)`.
    ///
    /// Frees a scope whose tasks have all been given. Traps with
    /// `Cancelled` if the parent was cancelled meanwhile.
    ScopeEnd = 26,

    /// `rt_enter_no_cancel(ctx)`.
    ///
    /// Opens a region where cancellation waits (Specification §10.4):
    /// atomic blocks, update and `ext` closures, foreign calls, drop and
    /// dispose handlers. Regions nest.
    EnterNoCancel = 27,

    /// `rt_exit_no_cancel(ctx)`.
    ///
    /// Closes the innermost such region; when it was the last and the task
    /// was cancelled meanwhile, traps with `Cancelled`.
    ExitNoCancel = 28,

    /// `rt_stream_new(ctx, capacity, list) -> (sink, source)`.
    ///
    /// A stream with a buffer of `capacity` values, zero for a hand-off
    /// (Specification §10.5), and its two ends. Its values are laid out as
    /// the elements of the list type with index `list`, which the runtime
    /// needs to release those left in the buffer (Implementation Plan
    /// §11.7.5). Each end is closed at most once and disposed exactly once.
    StreamNew = 29,

    /// `rt_stream_put(ctx, sink, w0, w1) -> status`.
    ///
    /// Puts a value, suspending while the buffer is full: [`STREAM_OK`]
    /// once it is sent, else [`STREAM_CLOSED`] or [`STREAM_ABANDONED`].
    /// The value's references go with it only when it is sent. Cancellation
    /// takes effect here (§11.7.4).
    StreamPut = 30,

    /// `rt_stream_try_put(ctx, sink, w0, w1) -> status`.
    ///
    /// As `StreamPut`, but [`STREAM_FULL`] instead of waiting.
    StreamTryPut = 31,

    /// `rt_stream_next(ctx, source, out) -> status`.
    ///
    /// Takes the next value, suspending while there is none: [`STREAM_OK`]
    /// with the value's words, and references, at `out`, else
    /// [`STREAM_CLOSED`] or [`STREAM_ABANDONED`] once the producers are
    /// gone and the buffer is empty. `out` must stay where it is until the
    /// call returns. Cancellation takes effect here.
    StreamNext = 32,

    /// `rt_stream_close(ctx, end)`.
    ///
    /// Ends a stream deliberately from either end, or leaves a hub: the
    /// other side reads `Closed` (Specification §10.5.2).
    StreamClose = 33,

    /// `rt_stream_dispose(ctx, end)`.
    ///
    /// Frees an end. One that was not closed is abandoned: the other side
    /// reads `Abandoned`.
    StreamDispose = 34,

    /// `rt_hub_new(ctx, capacity, list, kind) -> hub`.
    ///
    /// A hub of [`HUB_FAN_OUT`] or [`HUB_BROADCAST`], with values laid out
    /// as for `StreamNew` (Specification §10.6). Its ends are those of
    /// streams.
    HubNew = 35,

    /// `rt_hub_sink(ctx, hub) -> sink`.
    ///
    /// Joins as a producer; after `HubSeal` the sink starts closed.
    HubSink = 36,

    /// `rt_hub_source(ctx, hub) -> source`.
    ///
    /// Joins as a consumer, from the values put from now on.
    HubSource = 37,

    /// `rt_hub_seal(ctx, hub)`.
    ///
    /// Admits no further producers: once every producer has left, the
    /// consumers read `Closed`, or `Abandoned` if one left without closing.
    HubSeal = 38,

    /// `rt_hub_release(ctx, hub, n)`.
    ///
    /// Makes `n` consumers of a fan-out read `Closed`: those waiting now,
    /// and the rest at their next `StreamNext`.
    HubRelease = 39,

    /// `rt_hub_drop(ctx, hub)`.
    ///
    /// Gives up the hub's handle, which seals it.
    HubDrop = 40,

    /// `rt_ref_read(ctx, cell, out) -> version`.
    ///
    /// While the task runs a transaction, this and the other ref functions
    /// act on its log as `TxRead` and `TxWrite` do: an update writes to the
    /// log and commits, and a read that conflicts sets the conflict word
    /// ([`TX_CONFLICT_OFFSET`]) and gives zero words (Implementation Plan
    /// §11.7.14).
    ///
    /// Reads the ref cell at `cell` (see [`REF_CELL_SIZE`]): its value's
    /// two words to `out`, borrowed, and the version they belong to. The
    /// task stays pinned until `RefCommit` or `RefDone`, so a value a
    /// write replaces meanwhile is not released (Implementation Plan
    /// §11.7.6). Nothing between may suspend.
    RefRead = 41,

    /// `rt_ref_commit(ctx, cell, version, list, w0, w1) -> status`.
    ///
    /// Ends an update begun by `RefRead`: [`REF_COMMITTED`] when the cell
    /// still holds `version`, else [`REF_CONFLICT`] and the update must
    /// rerun. The value is laid out as the `ref_cell` of the list type
    /// with index `list` says (`TypeDescriptor::List`). A committed value's references go to the cell; one
    /// identical to the value read is not written and its references are
    /// given up (Specification §9.3), and so are those of a value that
    /// conflicted. Unpins the task.
    RefCommit = 42,

    /// `rt_ref_done(ctx)`.
    ///
    /// Ends a read that writes nothing, as `use` or an update whose closure
    /// gave an error: unpins the task.
    RefDone = 43,

    /// `rt_ref_swap(ctx, cell, list, w0, w1) -> (w0, w1)`.
    ///
    /// Places a value, laid out as for `RefCommit`, with its references,
    /// and gives the old one with references of its own.
    RefSwap = 44,

    /// `rt_tx_begin(ctx) -> depth`.
    ///
    /// Opens an `atomic` block (Specification §9.5): the outermost starts
    /// an attempt of a transaction, an inner one takes a savepoint
    /// (Implementation Plan §11.7.7). Gives the number of blocks open, 1
    /// for the outermost. The block is a region where cancellation waits,
    /// and nothing in it may suspend.
    TxBegin = 45,

    /// `rt_tx_read(ctx, cell, out) -> status`.
    ///
    /// Reads a ref cell in the block: [`TX_OK`] with the value's two words
    /// at `out`, borrowed, which is what the block wrote to it if it did,
    /// else [`TX_CONFLICT`], and the outermost block must rerun.
    TxRead = 46,

    /// `rt_tx_write(ctx, cell, list, w0, w1)`.
    ///
    /// Writes a value, laid out as for `RefCommit`, with its references, to
    /// a ref cell at the commit. One identical to what the block sees is
    /// not written, and its references are given up.
    TxWrite = 47,

    /// `rt_tx_commit(ctx) -> status`.
    ///
    /// Closes the block: an inner one keeps its writes for the outermost,
    /// which writes them all at once, [`TX_OK`], or [`TX_CONFLICT`] and it
    /// must rerun.
    TxCommit = 48,

    /// `rt_tx_abort(ctx)`.
    ///
    /// Closes a block whose value is an error: its writes are dropped, and
    /// those of the blocks around it stay (Specification §9.5.1).
    TxAbort = 49,

    /// `rt_tx_retry(ctx)`.
    ///
    /// After a conflict, drops the attempt's reads and writes, backs off
    /// and starts the outermost block's next attempt, after which the
    /// block's code runs again from its start.
    TxRetry = 50,

    /// `rt_ref_apply(ctx, cell, op, ty, k, list) -> status`.
    ///
    /// Applies `v ⊕ k` to the integer in a ref cell under the cell's lock,
    /// as the compiler lowers an update whose closure has that shape, so
    /// it never reruns (Implementation Plan §11.7.8). `op` is one of
    /// [`REF_ADD`] to [`REF_MAX`]; `ty` is the integer's width in bits, 8,
    /// 16, 32 or 64, with [`REF_UNSIGNED`] for an unsigned one. Gives
    /// [`REF_COMMITTED`], or [`REF_OVERFLOW`] when the result is outside
    /// the type, and then the cell is unchanged and the caller traps.
    /// `list` is the type index of a list of the integers, which a
    /// transaction's log keeps the write with.
    RefApply = 51,

    /// `rt_ext_new(ctx) -> ext`.
    ///
    /// Makes the lock of an `ext` binding (Specification §9.6), whose value
    /// generated code keeps and touches only while it holds the lock.
    ExtNew = 52,

    /// `rt_ext_lock(ctx, ext)`.
    ///
    /// Takes the lock before an access closure runs, suspending while
    /// another task holds it; a point where a cancelled task traps. A task
    /// holds at most one lock, and one that stops gives it up.
    ExtLock = 53,

    /// `rt_ext_unlock(ctx, ext)`.
    ///
    /// Gives the lock up after the closure, to the task that waited
    /// longest.
    ExtUnlock = 54,

    /// `rt_ext_free(ctx, ext)`.
    ///
    /// Frees the lock when the binding's scope ends, which no task holds
    /// or waits for any more (§10.1).
    ExtFree = 55,

    /// `rt_signal_emit(ctx, qualifier, list, w0, w1, info) -> status`.
    ///
    /// Emits a signal (Specification §11.2), laid out as the elements of
    /// the list type with index `list`. `qualifier` is one of
    /// [`SIGNAL_PLAIN`], [`SIGNAL_OK`], [`SIGNAL_FAIL`] and
    /// [`SIGNAL_RETRY`]. In an `atomic` block or an update closure the
    /// signal is held, with its references, until the block's outcome
    /// decides whether it is delivered (Implementation Plan §11.7.10):
    /// [`SIGNAL_HELD`]. Elsewhere generated code delivers it itself, and
    /// keeps its references: [`SIGNAL_DELIVER`]. `info` points at what
    /// generated code knows of the signal's type, in its static data:
    /// the type index, 1 if the value is a box whose header has the
    /// index, the length of the type's name and the name.
    SignalEmit = 56,

    /// `rt_signal_next(ctx, out) -> list`.
    ///
    /// Takes the next signal an outcome made deliverable: its list type,
    /// with its two words and its `info` at `out`, or [`SIGNAL_NONE`].
    /// The signal is borrowed until the next call, which gives it up.
    /// Generated code calls it after `TxCommit`, `TxAbort`, `TxRetry`,
    /// `RefCommit` and `RefDone` until there is none, and delivers each.
    SignalNext = 57,

    /// `rt_lazy_new(ctx, list) -> lazy`.
    ///
    /// Makes a lazy cell (Specification §6.10) for a value laid out as the
    /// elements of the list type with index `list`.
    LazyNew = 58,

    /// `rt_lazy_get(ctx, lazy, out) -> status`.
    ///
    /// Reads a lazy cell (Implementation Plan §11.7.11): [`LAZY_DONE`] with
    /// the value's two words at `out` and references of its own;
    /// [`LAZY_RUN`] when the caller must compute the value and store it
    /// with `LazySet`; or [`LAZY_TRAPPED`] with the kind of the trap at
    /// `out`, at which the caller traps. Suspends while another task
    /// computes the value; a point where a cancelled task traps.
    LazyGet = 59,

    /// `rt_lazy_set(ctx, lazy, w0, w1)`.
    ///
    /// Stores the value the caller computed, with its references, and
    /// hands it to the reads that wait.
    LazySet = 60,

    /// `rt_lazy_free(ctx, lazy)`.
    ///
    /// Frees the cell, which no task reads any more, with its value.
    LazyFree = 61,

    /// `rt_release_deferred(ctx, ptr)`.
    ///
    /// As `Release`, for a box of a type that is not `Immediate`
    /// (Specification §13.3): frees a bounded part of the structure and
    /// leaves the rest to the scheduler, which frees it between fibers and
    /// runs the `Deferred` dispose handlers in it as tasks of their own
    /// (Implementation Plan §11.7.12). The handlers of the part freed at
    /// once are queued for `Disposal`, as `Release` queues them.
    ReleaseDeferred = 62,

    /// `rt_tx_throw(ctx) -> !`.
    ///
    /// Leaves the attempt of a transaction from code an `atomic` block
    /// called: releases what the frames hold, as a trap does, up to the
    /// first frame whose call has a handler, and continues at the handler
    /// (Implementation Plan §11.7.14).
    TxThrow = 63,

    /// `rt_io_listen(ctx, port) -> (fd, errno)`.
    ///
    /// A non-blocking TCP socket listening on the loopback interface at
    /// `port`, any free one for zero (Implementation Plan §11.7.14).
    IoListen = 64,

    /// `rt_io_port(ctx, fd) -> port`.
    ///
    /// The port a socket is bound to.
    IoPort = 65,

    /// `rt_io_socket(ctx) -> (fd, errno)`.
    ///
    /// A new non-blocking TCP socket, for `IoConnectLocal`.
    IoSocket = 66,

    /// `rt_io_connect_local(ctx, fd, port) -> (0, errno)`.
    ///
    /// Connects a socket to `port` on the loopback interface, suspending
    /// until the connection is made, as `IoConnect` does.
    IoConnectLocal = 67,

    /// `rt_io_buffer(ctx, len) -> buffer`.
    ///
    /// A buffer of a string or bytes with room for `len` bytes, for a read
    /// into it after its header.
    IoBuffer = 68,

    /// `rt_io_bytes(ctx, buffer, n) -> (w0, w1)`.
    ///
    /// The bytes value of the first `n` bytes of a buffer from `IoBuffer`,
    /// whose reference it takes: inline when they fit, and the buffer is
    /// freed.
    IoBytes = 69,

    /// `rt_io_write_bytes(ctx, fd, w0, w1, left) -> (left, errno)`.
    ///
    /// Writes the last `left` bytes of a bytes value, all of them for
    /// `u64::MAX`, suspending until some can go: how many are left
    /// afterwards, or the error number. The caller holds the value until
    /// the call returns.
    IoWriteBytes = 70,

    /// `rt_signal_mark(ctx) -> mark`.
    ///
    /// How many signal handlers the task has registered: the base of a
    /// block's handlers, which `SignalReset` returns to when the block
    /// ends (Implementation Plan §11.7.14).
    SignalMark = 71,

    /// `rt_signal_reset(ctx, mark)`.
    ///
    /// Forgets the handlers registered since the mark.
    SignalReset = 72,

    /// `rt_signal_on(ctx, code, env, types, packed, base)`.
    ///
    /// Registers a handler (Specification §11.3) of the block whose mark is
    /// `base`: its function value, which the caller keeps until the block
    /// ends, and a sorted array of the `u32` type indices of the signal
    /// types it takes, in static data. `packed` holds the array's length
    /// in its upper half, then how many parent types the handler's type
    /// has, shifted by 8, then the words of its parameter, zero or one.
    SignalOn = 73,

    /// `rt_signal_find(ctx, index, out) -> found`.
    ///
    /// Finds the handler of a signal of type index `index`: the innermost
    /// block's that takes it, and of those the most specific. Gives 1 with
    /// its code, its environment and the words of its parameter at `out`,
    /// and hides its block and those above while it runs, until
    /// `SignalLeave`; else 0.
    SignalFind = 74,

    /// `rt_signal_leave(ctx)`.
    ///
    /// Shows what `SignalFind` hid, once the handler returned.
    SignalLeave = 75,

    /// `rt_signal_default(ctx, name, len)`.
    ///
    /// The root's handler of a signal no handler takes: writes the name of
    /// its type to standard error.
    SignalDefault = 76,

    /// `rt_step(ctx, cell, words, count, fp)`.
    ///
    /// A statement's step, called while its flag is set (Implementation
    /// Plan §11.8.6): `cell` is the step's cell, whose second word names
    /// it (`step_cell_word`), so code holds no function id outside its
    /// relocations and can be kept across programs; the `count` words at
    /// `words` are those of its locals, and `fp` is the frame pointer of
    /// the calling frame. The debugger may stop the task here; it returns
    /// once the task is resumed.
    Step = 77,

    /// `rt_io_print(ctx, w0, w1, newline) -> errno`.
    ///
    /// Writes a string to standard output, with a newline when `newline`
    /// is 1, as one write that other prints do not interleave with: 0, or
    /// the error number (Specification §15.6).
    IoPrint = 78,

    /// `rt_io_read_file(ctx, w0, w1, out) -> errno`.
    ///
    /// Reads the whole file the string names into a bytes value, whose
    /// two words it writes at `out`: 0, or the error number.
    IoReadFile = 79,

    /// `rt_io_socket_any(ctx) -> (fd, errno)`.
    ///
    /// A new non-blocking TCP socket for `IoConnectHost`, which reaches
    /// IPv6 and IPv4 addresses alike where the system has IPv6.
    IoSocketAny = 80,

    /// `rt_io_connect_host(ctx, fd, w0, w1, port) -> (0, errno)`.
    ///
    /// Looks up the host the string names and connects a socket from
    /// `IoSocketAny` to `port` there, suspending until the connection is
    /// made: 0, the error number, or [`UNKNOWN_HOST`] when the name has no
    /// address.
    IoConnectHost = 81,

    /// `rt_text_utf8(ctx, w0, w1) -> 1 | 0`.
    ///
    /// Whether the bytes of a value are valid UTF-8.
    TextUtf8 = 82,

    /// `rt_text_measure(ctx, op, w0, w1) -> n`.
    ///
    /// A count of a string or bytes value, by the operation of
    /// [`text_op`]: `BYTE_COUNT` or `CODE_POINT_COUNT`.
    TextMeasure = 83,

    /// `rt_text_at(ctx, op, w0, w1, at) -> n`.
    ///
    /// What is at a byte offset: `IS_BOUNDARY`, `NEXT`, `PREVIOUS`,
    /// `CODE_POINT_AT` or `BYTE_AT` of [`text_op`]; -1 where there is
    /// nothing.
    TextAt = 84,

    /// `rt_text_find(ctx, a0, a1, b0, b1, packed) -> n`.
    ///
    /// Looks for the second value in the first. `packed` holds the
    /// operation of [`text_op`] in its low 3 bits and the offset to
    /// search from above them: `INDEX_OF` and `LAST_INDEX_OF` give a byte
    /// offset or -1, `STARTS_WITH` and `ENDS_WITH` 1 or 0, and `COMPARE`
    /// 0, 1 or 2 for less, equal and greater, by the bytes.
    TextFind = 85,

    /// `rt_text_map(ctx, op, w0, w1) -> (w0, w1)`.
    ///
    /// A new string from one: `TRIM`, `TRIM_START`, `TRIM_END`,
    /// `TO_UPPER`, `TO_LOWER` or `HEX` of [`text_op`].
    TextMap = 86,

    /// `rt_text_slice(ctx, w0, w1, from, to) -> (w0, w1)`.
    ///
    /// The bytes from `from` up to `to`, both clamped to the value.
    TextSlice = 87,

    /// `rt_code_point(ctx, op, value) -> n`.
    ///
    /// A property or mapping of a code point, by the `CP_…` operations of
    /// [`text_op`].
    CodePointOp = 88,

    /// `rt_text_parse(ctx, op, w0, w1, base) -> (value, ok)`.
    ///
    /// A number from text: `PARSE_INT` in the base, or `PARSE_FLOAT` as
    /// its bits; `ok` is 0 when the text is no such number.
    TextParse = 89,

    /// `rt_value_shapes(ctx, w0, w1) -> handle`.
    ///
    /// The runtime's handle of a type's shapes: the bytes of
    /// `Shapes::encode` after the root shape's index, four bytes little
    /// endian, decoded once for each distinct table.
    ValueShapes = 90,

    /// `rt_value_op(ctx, packed, a0, a1, b0, b1) -> n`.
    ///
    /// Equality, order or the hash of values by their shape (Specification
    /// §19.11): `packed` holds the operation of [`value_op`] in its low 8
    /// bits and a handle of `ValueShapes` above them. `EQUALS` gives 1 or
    /// 0, `COMPARE` 0, 1 or 2 for less, equal and greater, or `UNORDERED`,
    /// and `HASH` the hash of the first value.
    ValueOp = 91,

    /// `rt_value_show(ctx, handle, w0, w1) -> (w0, w1)`.
    ///
    /// A value written as source, as the REPL shows it.
    ValueShow = 92,

    /// `rt_list_set(ctx, list, at, w0, w1) -> list`.
    ///
    /// The list with element `at` replaced. It takes the list's reference
    /// and the value's; `at` is inside the list.
    ListSet = 93,

    /// `rt_list_concat(ctx, a, b) -> list`.
    ///
    /// A new list of the elements of `a`, then those of `b`. It borrows
    /// both.
    ListConcat = 94,

    /// `rt_map_remove(ctx, map, k0, k1) -> map`.
    ///
    /// The map or set without the key. It takes the map's reference and
    /// borrows the key.
    MapRemove = 95,

    /// `rt_map_list(ctx, map, list, values) -> list`.
    ///
    /// The list with the keys of the map or set after its elements, or
    /// with the values for `values` 1, in the map's order, each with a
    /// reference of its own. It borrows the map and takes the list's
    /// reference.
    MapList = 96,

    /// `rt_test_record(ctx, w0, w1, position)`.
    ///
    /// Records a failed assertion of a test, its message and the byte
    /// offset of the assertion in its module (Specification §19.12).
    TestRecord = 97,

    /// `rt_env_args(ctx, list) -> list`.
    ///
    /// The list of bytes values with the program's arguments after its
    /// elements, without the program's name (Specification §19.7). It takes
    /// the list's reference.
    EnvArgs = 98,

    /// `rt_env_var(ctx, w0, w1, out) -> found`.
    ///
    /// Whether the environment has the variable the string names: 1, with
    /// its value's bytes written at `out`, or 0.
    EnvVar = 99,

    /// `rt_env_vars(ctx, map) -> map`.
    ///
    /// The map of strings with the environment's variables bound, those
    /// whose name or value is not UTF-8 left out. It takes the map's
    /// reference.
    EnvVars = 100,

    /// `rt_env_platform(ctx, which) -> code`.
    ///
    /// The system for `which` 0, by the order of `Os` in `std.env`, or the
    /// processor for 1, by the order of `Arch`.
    EnvPlatform = 101,

    /// `rt_bytes_read(ctx, packed, w0, w1, at) -> (value, ok)`.
    ///
    /// The number of the kind of [`bytes_kind`] in the low 8 bits of
    /// `packed`, big-endian when bit 8 is set, at the byte offset: an
    /// integer sign- or zero-extended, a float as the bits of a `Float`;
    /// `ok` is 0 when it does not fit before the end, or a float is not
    /// finite.
    BytesRead = 102,

    /// `rt_bytes_write(ctx, packed, w0, w1, at, value) -> (w0, w1)`.
    ///
    /// New bytes with the number written at the offset, as `BytesRead`
    /// reads it; the offset is inside the bytes.
    BytesWrite = 103,

    /// `rt_bytes_of_list(ctx, list) -> (w0, w1)`.
    ///
    /// The bytes of a list of `UInt8` values. It borrows the list.
    BytesOfList = 104,

    /// `rt_trap_catch(ctx, kind, position)`.
    ///
    /// A trap that a handler of its own frame takes (Specification
    /// §8.3.1): records it, as `rt_trap` records one it unwinds to a
    /// handler, and returns, so the frame goes on at the handler.
    TrapCatch = 105,

    /// `rt_trap_rethrow(ctx) -> !`.
    ///
    /// Raises the trap a handler took again, for the handlers around it.
    TrapRethrow = 106,

    /// `rt_trap_caught(ctx, which) -> u64`.
    ///
    /// Of the trap a handler took: its kind (0), the line (1) and the
    /// column (2) of its origin, from one.
    TrapCaught = 107,

    /// `rt_trap_caught_text(ctx, which) -> (w0, w1)`.
    ///
    /// Of the trap a handler took, as a string: the module of its origin
    /// (0), its message (1), and what it names (2), such as the type of
    /// the error `!!` met.
    TrapCaughtText = 108,

    /// `rt_tx_depth(ctx) -> depth`.
    ///
    /// How many `atomic` blocks the task is in.
    TxDepth = 109,

    /// `rt_tx_unwind(ctx, depth)`.
    ///
    /// Abandons the transactions begun inside `depth`, as a trap leaves
    /// them for a handler outside (Specification §8.3.1).
    TxUnwind = 110,

    /// `rt_c_call(ctx, library, func, desc, buf) -> (result, class)`.
    ///
    /// Calls the C function at `func` of the [`NativeLibrary`] with the C
    /// calling convention, on the system stack, as the library's thread
    /// safety allows (Specification §16.4). `desc` is a [`c_kind`]
    /// descriptor: the number of parameters, the result's kind, then each
    /// parameter's. `buf` holds a word per parameter: a value, a `CStr`'s
    /// box or null, or, for an out parameter, room for what the function
    /// writes there, which the call leaves extended to a word; the word
    /// after them gets `errno` as read right after the call. The result
    /// comes back extended to a word, a `CF32` as its bits, with the class
    /// of a float: 0 finite, 1 NaN, 2 positive, 3 negative infinity.
    CCall = 111,

    /// `rt_c_str_of(ctx, address, nul) -> (w0, w1)`.
    ///
    /// A copy of the NUL-terminated bytes at the address, which is not
    /// null, as `Bytes`: with the NUL when `nul` is not zero.
    CStrOf = 112,
}

/// The kinds of C values of a [`RuntimeFn::CCall`] descriptor.
pub mod c_kind {
    pub const I8: u8 = 0;
    pub const I16: u8 = 1;
    pub const I32: u8 = 2;
    pub const I64: u8 = 3;
    pub const U8: u8 = 4;
    pub const U16: u8 = 5;
    pub const U32: u8 = 6;
    pub const U64: u8 = 7;
    pub const F64: u8 = 8;
    pub const F32: u8 = 9;
    /// A pointer, which a `CStr` result is too.
    pub const PTR: u8 = 10;
    /// A `CStr` argument: the box of its bytes, passed as their address.
    pub const CSTR: u8 = 11;
    /// No value: a `()` result.
    pub const VOID: u8 = 12;
    /// An `Option[CStr]` argument: a `CStr`'s box, or null for `Empty`.
    pub const OPT_CSTR: u8 = 13;
    /// Set on an out parameter's kind, the kind of what it points to.
    pub const OUT: u8 = 0x80;
}

/// How calls of a C library run (Specification §16.4), as a
/// [`NativeSymbol`] carries it.
pub mod threading {
    pub const UNSAFE: u8 = 0;
    pub const SAFE: u8 = 1;
    pub const BOUND: u8 = 2;
}

/// A C function a code object calls: the files of its library, tried in
/// order, its symbol, and the library's thread safety.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NativeSymbol {
    pub files: Vec<String>,
    pub symbol: String,
    pub threading: u8,
}

/// A native library as the loader opened it, which lives as long as the
/// process: its handle, its thread safety, the lock its calls take when it
/// is not thread-safe, and the thread of its own when it is bound to one.
pub struct NativeLibrary {
    pub handle: usize,
    pub threading: u8,
    pub lock: std::sync::Mutex<()>,
    pub thread: std::sync::OnceLock<std::sync::Mutex<std::sync::mpsc::Sender<NativeJob>>>,
}

/// A call a library's own thread makes.
pub type NativeJob = Box<dyn FnOnce() + Send>;

/// The kinds of numbers of `BytesRead` and `BytesWrite`.
pub mod bytes_kind {
    pub const INT8: u8 = 0;
    pub const INT16: u8 = 1;
    pub const INT32: u8 = 2;
    pub const INT64: u8 = 3;
    pub const UINT8: u8 = 4;
    pub const UINT16: u8 = 5;
    pub const UINT32: u8 = 6;
    pub const UINT64: u8 = 7;
    pub const FLOAT32: u8 = 8;
    pub const FLOAT64: u8 = 9;

    /// Set in `packed` for big-endian.
    pub const BIG: u64 = 1 << 8;
}

/// The operations of `RuntimeFn::ValueOp`.
pub mod value_op {
    pub const EQUALS: u8 = 0;
    pub const COMPARE: u8 = 1;
    pub const HASH: u8 = 2;

    /// What `COMPARE` gives for values without an order: functions, maps
    /// and sets.
    pub const UNORDERED: u64 = 3;
}

/// The operations of the text runtime functions.
pub mod text_op {
    pub const BYTE_COUNT: u8 = 0;
    pub const CODE_POINT_COUNT: u8 = 1;

    pub const IS_BOUNDARY: u8 = 0;
    pub const NEXT: u8 = 1;
    pub const PREVIOUS: u8 = 2;
    pub const CODE_POINT_AT: u8 = 3;
    pub const BYTE_AT: u8 = 4;

    pub const INDEX_OF: u8 = 0;
    pub const LAST_INDEX_OF: u8 = 1;
    pub const STARTS_WITH: u8 = 2;
    pub const ENDS_WITH: u8 = 3;
    pub const COMPARE: u8 = 4;

    pub const TRIM: u8 = 0;
    pub const TRIM_START: u8 = 1;
    pub const TRIM_END: u8 = 2;
    pub const TO_UPPER: u8 = 3;
    pub const TO_LOWER: u8 = 4;
    pub const HEX: u8 = 5;

    pub const CP_IS_LETTER: u8 = 0;
    pub const CP_IS_DIGIT: u8 = 1;
    pub const CP_IS_WHITESPACE: u8 = 2;
    pub const CP_IS_UPPER: u8 = 3;
    pub const CP_IS_LOWER: u8 = 4;
    pub const CP_TO_UPPER: u8 = 5;
    pub const CP_TO_LOWER: u8 = 6;
    pub const CP_IS_VALID: u8 = 7;
    pub const CP_IS_NUMERIC: u8 = 8;

    pub const PARSE_INT: u8 = 0;
    pub const PARSE_FLOAT: u8 = 1;
    /// An unsigned 64-bit integer, as the word's bits.
    pub const PARSE_UINT: u8 = 2;
}

/// The error of `IoConnectHost` for a host name without an address, above
/// every error number.
pub const UNKNOWN_HOST: u64 = 1 << 16;

/// A status of the stream functions: sent, or a value taken.
pub const STREAM_OK: u64 = 0;

/// `rt_stream_try_put` found the buffer full.
pub const STREAM_FULL: u64 = 1;

/// The other side closed the stream, or this end was closed.
pub const STREAM_CLOSED: u64 = 2;

/// The other side went without closing.
pub const STREAM_ABANDONED: u64 = 3;

/// A hub that hands each value to one consumer.
pub const HUB_FAN_OUT: u64 = 0;

/// A hub that hands each value to every consumer.
pub const HUB_BROADCAST: u64 = 1;

/// The size of a ref cell, which generated code places on the side stack:
/// a version word at offset 0, whose lowest bit is the lock, and the two
/// words of the value at offsets 8 and 16, a value stored flat there in
/// its storage form with zeros past its bytes. A new cell has version 0.
pub const REF_CELL_SIZE: u64 = 24;

/// A status of `rt_ref_commit`: the value was written, or was the one read.
pub const REF_COMMITTED: u64 = 0;

/// The cell changed since the read: the update reruns.
pub const REF_CONFLICT: u64 = 1;

/// The result of `rt_ref_apply` is outside the integer type.
pub const REF_OVERFLOW: u64 = 2;

/// The operations of `rt_ref_apply`.
pub const REF_ADD: u64 = 0;
pub const REF_SUB: u64 = 1;
pub const REF_MUL: u64 = 2;
pub const REF_AND: u64 = 3;
pub const REF_OR: u64 = 4;
pub const REF_XOR: u64 = 5;
pub const REF_MIN: u64 = 6;
pub const REF_MAX: u64 = 7;

/// The flag of `rt_ref_apply`'s type for an unsigned integer.
pub const REF_UNSIGNED: u64 = 1 << 8;

/// A status of the transaction functions: the read gave a value, or the
/// block committed.
pub const TX_OK: u64 = 0;

/// The transaction saw a change by another: its outermost block reruns.
pub const TX_CONFLICT: u64 = 1;

/// The qualifiers of `rt_signal_emit`: delivered when the block commits,
/// as `emit` and `emit ok` are, when it fails, or when its attempt is
/// rerun.
pub const SIGNAL_PLAIN: u64 = 0;
pub const SIGNAL_OK: u64 = 1;
pub const SIGNAL_FAIL: u64 = 2;
pub const SIGNAL_RETRY: u64 = 3;

/// What `rt_signal_next` gives when no signal is left to deliver.
pub const SIGNAL_NONE: u64 = u64::MAX;

/// What `rt_signal_emit` gives: the signal is held, or the caller delivers
/// it.
pub const SIGNAL_HELD: u64 = 0;
pub const SIGNAL_DELIVER: u64 = 1;

/// The statuses of `rt_lazy_get`: the value is there, the caller computes
/// it, or its computation trapped.
pub const LAZY_DONE: u64 = 0;
pub const LAZY_RUN: u64 = 1;
pub const LAZY_TRAPPED: u64 = 2;

/// The flag of `rt_scope_start` for a task outside the scope's limit, such
/// as the body of a group.
pub const START_EXEMPT: u64 = 1 << 2;

/// The index `rt_scope_next` gives once every task has been given.
pub const SCOPE_DONE: u64 = u64::MAX;

/// A task that returned: its results wait in the scope.
pub const TASK_RETURNED: u64 = 0;

/// A task that was cancelled.
pub const TASK_CANCELLED: u64 = 1;

/// A task that trapped.
pub const TASK_TRAPPED: u64 = 2;

impl RuntimeFn {
    /// Every runtime function, indexed by its discriminant.
    pub const ALL: [RuntimeFn; 113] = [
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
        RuntimeFn::Disposal,
        RuntimeFn::Yield,
        RuntimeFn::Sleep,
        RuntimeFn::IoRead,
        RuntimeFn::IoWrite,
        RuntimeFn::IoAccept,
        RuntimeFn::IoConnect,
        RuntimeFn::ScopeNew,
        RuntimeFn::ScopeStart,
        RuntimeFn::ScopeNext,
        RuntimeFn::ScopeResult,
        RuntimeFn::ScopeCancel,
        RuntimeFn::ScopeEnd,
        RuntimeFn::EnterNoCancel,
        RuntimeFn::ExitNoCancel,
        RuntimeFn::StreamNew,
        RuntimeFn::StreamPut,
        RuntimeFn::StreamTryPut,
        RuntimeFn::StreamNext,
        RuntimeFn::StreamClose,
        RuntimeFn::StreamDispose,
        RuntimeFn::HubNew,
        RuntimeFn::HubSink,
        RuntimeFn::HubSource,
        RuntimeFn::HubSeal,
        RuntimeFn::HubRelease,
        RuntimeFn::HubDrop,
        RuntimeFn::RefRead,
        RuntimeFn::RefCommit,
        RuntimeFn::RefDone,
        RuntimeFn::RefSwap,
        RuntimeFn::TxBegin,
        RuntimeFn::TxRead,
        RuntimeFn::TxWrite,
        RuntimeFn::TxCommit,
        RuntimeFn::TxAbort,
        RuntimeFn::TxRetry,
        RuntimeFn::RefApply,
        RuntimeFn::ExtNew,
        RuntimeFn::ExtLock,
        RuntimeFn::ExtUnlock,
        RuntimeFn::ExtFree,
        RuntimeFn::SignalEmit,
        RuntimeFn::SignalNext,
        RuntimeFn::LazyNew,
        RuntimeFn::LazyGet,
        RuntimeFn::LazySet,
        RuntimeFn::LazyFree,
        RuntimeFn::ReleaseDeferred,
        RuntimeFn::TxThrow,
        RuntimeFn::IoListen,
        RuntimeFn::IoPort,
        RuntimeFn::IoSocket,
        RuntimeFn::IoConnectLocal,
        RuntimeFn::IoBuffer,
        RuntimeFn::IoBytes,
        RuntimeFn::IoWriteBytes,
        RuntimeFn::SignalMark,
        RuntimeFn::SignalReset,
        RuntimeFn::SignalOn,
        RuntimeFn::SignalFind,
        RuntimeFn::SignalLeave,
        RuntimeFn::SignalDefault,
        RuntimeFn::Step,
        RuntimeFn::IoPrint,
        RuntimeFn::IoReadFile,
        RuntimeFn::IoSocketAny,
        RuntimeFn::IoConnectHost,
        RuntimeFn::TextUtf8,
        RuntimeFn::TextMeasure,
        RuntimeFn::TextAt,
        RuntimeFn::TextFind,
        RuntimeFn::TextMap,
        RuntimeFn::TextSlice,
        RuntimeFn::CodePointOp,
        RuntimeFn::TextParse,
        RuntimeFn::ValueShapes,
        RuntimeFn::ValueOp,
        RuntimeFn::ValueShow,
        RuntimeFn::ListSet,
        RuntimeFn::ListConcat,
        RuntimeFn::MapRemove,
        RuntimeFn::MapList,
        RuntimeFn::TestRecord,
        RuntimeFn::EnvArgs,
        RuntimeFn::EnvVar,
        RuntimeFn::EnvVars,
        RuntimeFn::EnvPlatform,
        RuntimeFn::BytesRead,
        RuntimeFn::BytesWrite,
        RuntimeFn::BytesOfList,
        RuntimeFn::TrapCatch,
        RuntimeFn::TrapRethrow,
        RuntimeFn::TrapCaught,
        RuntimeFn::TrapCaughtText,
        RuntimeFn::TxDepth,
        RuntimeFn::TxUnwind,
        RuntimeFn::CCall,
        RuntimeFn::CStrOf,
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
            RuntimeFn::Disposal => "rt_disposal",
            RuntimeFn::Yield => "rt_yield",
            RuntimeFn::Sleep => "rt_sleep",
            RuntimeFn::IoRead => "rt_io_read",
            RuntimeFn::IoWrite => "rt_io_write",
            RuntimeFn::IoAccept => "rt_io_accept",
            RuntimeFn::IoConnect => "rt_io_connect",
            RuntimeFn::ScopeNew => "rt_scope_new",
            RuntimeFn::ScopeStart => "rt_scope_start",
            RuntimeFn::ScopeNext => "rt_scope_next",
            RuntimeFn::ScopeResult => "rt_scope_result",
            RuntimeFn::ScopeCancel => "rt_scope_cancel",
            RuntimeFn::ScopeEnd => "rt_scope_end",
            RuntimeFn::EnterNoCancel => "rt_enter_no_cancel",
            RuntimeFn::ExitNoCancel => "rt_exit_no_cancel",
            RuntimeFn::StreamNew => "rt_stream_new",
            RuntimeFn::StreamPut => "rt_stream_put",
            RuntimeFn::StreamTryPut => "rt_stream_try_put",
            RuntimeFn::StreamNext => "rt_stream_next",
            RuntimeFn::StreamClose => "rt_stream_close",
            RuntimeFn::StreamDispose => "rt_stream_dispose",
            RuntimeFn::HubNew => "rt_hub_new",
            RuntimeFn::HubSink => "rt_hub_sink",
            RuntimeFn::HubSource => "rt_hub_source",
            RuntimeFn::HubSeal => "rt_hub_seal",
            RuntimeFn::HubRelease => "rt_hub_release",
            RuntimeFn::HubDrop => "rt_hub_drop",
            RuntimeFn::RefRead => "rt_ref_read",
            RuntimeFn::RefCommit => "rt_ref_commit",
            RuntimeFn::RefDone => "rt_ref_done",
            RuntimeFn::RefSwap => "rt_ref_swap",
            RuntimeFn::TxBegin => "rt_tx_begin",
            RuntimeFn::TxRead => "rt_tx_read",
            RuntimeFn::TxWrite => "rt_tx_write",
            RuntimeFn::TxCommit => "rt_tx_commit",
            RuntimeFn::TxAbort => "rt_tx_abort",
            RuntimeFn::TxRetry => "rt_tx_retry",
            RuntimeFn::RefApply => "rt_ref_apply",
            RuntimeFn::ExtNew => "rt_ext_new",
            RuntimeFn::ExtLock => "rt_ext_lock",
            RuntimeFn::ExtUnlock => "rt_ext_unlock",
            RuntimeFn::ExtFree => "rt_ext_free",
            RuntimeFn::SignalEmit => "rt_signal_emit",
            RuntimeFn::SignalNext => "rt_signal_next",
            RuntimeFn::LazyNew => "rt_lazy_new",
            RuntimeFn::LazyGet => "rt_lazy_get",
            RuntimeFn::LazySet => "rt_lazy_set",
            RuntimeFn::LazyFree => "rt_lazy_free",
            RuntimeFn::ReleaseDeferred => "rt_release_deferred",
            RuntimeFn::TxThrow => "rt_tx_throw",
            RuntimeFn::IoListen => "rt_io_listen",
            RuntimeFn::IoPort => "rt_io_port",
            RuntimeFn::IoSocket => "rt_io_socket",
            RuntimeFn::IoConnectLocal => "rt_io_connect_local",
            RuntimeFn::IoBuffer => "rt_io_buffer",
            RuntimeFn::IoBytes => "rt_io_bytes",
            RuntimeFn::IoWriteBytes => "rt_io_write_bytes",
            RuntimeFn::SignalMark => "rt_signal_mark",
            RuntimeFn::SignalReset => "rt_signal_reset",
            RuntimeFn::SignalOn => "rt_signal_on",
            RuntimeFn::SignalFind => "rt_signal_find",
            RuntimeFn::SignalLeave => "rt_signal_leave",
            RuntimeFn::SignalDefault => "rt_signal_default",
            RuntimeFn::Step => "rt_step",
            RuntimeFn::IoPrint => "rt_io_print",
            RuntimeFn::IoReadFile => "rt_io_read_file",
            RuntimeFn::IoSocketAny => "rt_io_socket_any",
            RuntimeFn::IoConnectHost => "rt_io_connect_host",
            RuntimeFn::TextUtf8 => "rt_text_utf8",
            RuntimeFn::TextMeasure => "rt_text_measure",
            RuntimeFn::TextAt => "rt_text_at",
            RuntimeFn::TextFind => "rt_text_find",
            RuntimeFn::TextMap => "rt_text_map",
            RuntimeFn::TextSlice => "rt_text_slice",
            RuntimeFn::CodePointOp => "rt_code_point",
            RuntimeFn::TextParse => "rt_text_parse",
            RuntimeFn::ValueShapes => "rt_value_shapes",
            RuntimeFn::ValueOp => "rt_value_op",
            RuntimeFn::ValueShow => "rt_value_show",
            RuntimeFn::ListSet => "rt_list_set",
            RuntimeFn::ListConcat => "rt_list_concat",
            RuntimeFn::MapRemove => "rt_map_remove",
            RuntimeFn::MapList => "rt_map_list",
            RuntimeFn::TestRecord => "rt_test_record",
            RuntimeFn::EnvArgs => "rt_env_args",
            RuntimeFn::EnvVar => "rt_env_var",
            RuntimeFn::EnvVars => "rt_env_vars",
            RuntimeFn::EnvPlatform => "rt_env_platform",
            RuntimeFn::BytesRead => "rt_bytes_read",
            RuntimeFn::BytesWrite => "rt_bytes_write",
            RuntimeFn::BytesOfList => "rt_bytes_of_list",
            RuntimeFn::TrapCatch => "rt_trap_catch",
            RuntimeFn::TrapRethrow => "rt_trap_rethrow",
            RuntimeFn::TrapCaught => "rt_trap_caught",
            RuntimeFn::TrapCaughtText => "rt_trap_caught_text",
            RuntimeFn::TxDepth => "rt_tx_depth",
            RuntimeFn::TxUnwind => "rt_tx_unwind",
            RuntimeFn::CCall => "rt_c_call",
            RuntimeFn::CStrOf => "rt_c_str_of",
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
    /// The task was cancelled (Specification §10.4), or the runtime's poll
    /// at a refill asked metered code to stop, as the host does when an
    /// edit cancels a compile-time evaluation.
    Cancelled = 9,
    /// A lazy value's computation read the value itself.
    Cycle = 10,
    /// The environment failed an operation that has no error value, such
    /// as writing to a closed standard output (Specification §8.3, §15.6).
    Fault = 11,
    /// Values without an order were compared: functions, maps or sets
    /// (Specification §19.11).
    Unordered = 12,
    /// `!!` met an error (Specification §8.4).
    Expectation = 13,
    /// A value failed a condition of its type (Specification §3.10.1).
    ConditionFailed = 14,
    /// `number()` met a NaN or an infinity (Specification §3.1.4).
    NotFinite = 15,
    /// A C function broke what its import declares (Specification §16.1).
    ForeignFault = 16,
    /// A fiber's stack would grow past its maximum size.
    StackOverflow = 17,
}

impl TrapKind {
    /// What a trap of the kind tells the user.
    pub fn message(self) -> &'static str {
        match self {
            TrapKind::Overflow => "arithmetic overflow",
            TrapKind::DivideByZero => "division by zero",
            TrapKind::Index => "index out of range",
            TrapKind::Hole => "reached `???`",
            TrapKind::NoMatch => "no arm of `case` matched",
            TrapKind::Error => "reached code with errors",
            TrapKind::Unsupported => "reached code the compiler does not support yet",
            TrapKind::OutOfSteps => "ran out of steps",
            TrapKind::OutOfMemory => "ran out of memory",
            TrapKind::Cancelled => "was cancelled",
            TrapKind::Cycle => "a lazy value needed itself",
            TrapKind::Fault => "the environment failed",
            TrapKind::Unordered => "compared values that have no order",
            TrapKind::Expectation => "`!!` met an error",
            TrapKind::ConditionFailed => "a value failed a condition of its type",
            TrapKind::NotFinite => "a number was not finite",
            TrapKind::ForeignFault => "a C function broke what its import declares",
            TrapKind::StackOverflow => "the stack overflowed",
        }
    }

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

impl TrapKind {
    pub const ALL: [TrapKind; 18] = [
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
        TrapKind::Cycle,
        TrapKind::Fault,
        TrapKind::Unordered,
        TrapKind::Expectation,
        TrapKind::ConditionFailed,
        TrapKind::NotFinite,
        TrapKind::ForeignFault,
        TrapKind::StackOverflow,
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
    /// What traps of this code name beyond their kind, such as the type of
    /// the error `!!` met: the upper half of a trap's position word, from
    /// one, indexes it.
    pub details: Vec<String>,
    /// The C functions the code calls, which `RelocTarget::Native` and
    /// `RelocTarget::NativeLibrary` index.
    pub natives: Vec<NativeSymbol>,
}

/// The line and column, from one, of a byte offset in a module's source.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TrapOrigin {
    pub position: u32,
    pub line: u32,
    pub column: u32,
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
    /// For each shape of a Plain type, in a box or split, the `Stored`
    /// shape of its storage form, which the codec writes it in (Compiler
    /// Architecture §A11.4).
    pub plain: Vec<(u32, u32)>,
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

    /// The `Stored` shape of the storage form of a shape of a Plain type,
    /// if it is one.
    pub fn plain(&self, shape: u32) -> Option<u32> {
        self.plain.iter().find(|p| p.0 == shape).map(|p| p.1)
    }

    /// The table as bytes, as the session protocol sends it and generated
    /// code keeps it for the runtime's value functions.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let u32 = |out: &mut Vec<u8>, n: u32| out.extend_from_slice(&n.to_le_bytes());
        let text = |out: &mut Vec<u8>, t: &str| {
            u32(out, t.len() as u32);
            out.extend_from_slice(t.as_bytes());
        };
        u32(&mut out, self.shapes.len() as u32);
        for shape in &self.shapes {
            match shape {
                Shape::Unit => out.push(0),
                Shape::Tag(name) => {
                    out.push(1);
                    text(&mut out, name);
                }
                Shape::Number(n) => {
                    out.push(2);
                    match n {
                        Number::Signed => out.push(0),
                        Number::Unsigned => out.push(1),
                        Number::Float => out.push(2),
                        Number::Fixed(digits) => {
                            out.push(3);
                            u32(&mut out, *digits);
                        }
                        Number::CodePoint => out.push(4),
                    }
                }
                Shape::Union { members, words } | Shape::Variant { members, words } => {
                    out.push(match shape {
                        Shape::Union { .. } => 3,
                        _ => 13,
                    });
                    u32(&mut out, members.len() as u32);
                    for &(index, shape) in members {
                        u32(&mut out, index);
                        u32(&mut out, shape);
                    }
                    u32(&mut out, *words);
                }
                Shape::Record { name, fields } | Shape::Inline { name, fields, .. } => {
                    out.push(match shape {
                        Shape::Record { .. } => 4,
                        _ => 12,
                    });
                    match name {
                        None => out.push(0),
                        Some(name) => {
                            out.push(1);
                            text(&mut out, name);
                        }
                    }
                    u32(&mut out, fields.len() as u32);
                    for f in fields {
                        text(&mut out, &f.name);
                        u32(&mut out, f.offset);
                        u32(&mut out, f.shape);
                    }
                    if let Shape::Inline { words, .. } = shape {
                        u32(&mut out, *words);
                    }
                }
                Shape::List(element) => {
                    out.push(5);
                    u32(&mut out, *element);
                }
                Shape::Set(element) => {
                    out.push(6);
                    u32(&mut out, *element);
                }
                Shape::Map(key, value) => {
                    out.push(7);
                    u32(&mut out, *key);
                    u32(&mut out, *value);
                }
                Shape::Function => out.push(8),
                Shape::Opaque { name, words } => {
                    out.push(9);
                    text(&mut out, name);
                    u32(&mut out, *words);
                }
                Shape::Str => out.push(10),
                Shape::Bytes => out.push(11),
                Shape::Stored {
                    form,
                    size,
                    slots,
                    words,
                } => {
                    out.push(14);
                    u32(&mut out, *form);
                    u32(&mut out, *size);
                    stored_slots(&mut out, slots);
                    u32(&mut out, *words);
                }
            }
        }
        u32(&mut out, self.records.len() as u32);
        for &(index, shape) in &self.records {
            u32(&mut out, index);
            u32(&mut out, shape);
        }
        u32(&mut out, self.boxes.len() as u32);
        for &(shape, index, size) in &self.boxes {
            u32(&mut out, shape);
            u32(&mut out, index);
            u32(&mut out, size);
        }
        u32(&mut out, self.plain.len() as u32);
        for &(shape, stored) in &self.plain {
            u32(&mut out, shape);
            u32(&mut out, stored);
        }
        out
    }

    /// The table `encode` wrote, checked: every shape a shape names is in
    /// it.
    pub fn decode(bytes: &[u8]) -> Result<Shapes, String> {
        let mut r = ShapeReader { bytes, at: 0 };
        let shapes = Shapes {
            shapes: r.seq(ShapeReader::shape)?,
            records: r.seq(|r| Ok((r.u32()?, r.u32()?)))?,
            boxes: r.seq(|r| Ok((r.u32()?, r.u32()?, r.u32()?)))?,
            plain: r.seq(|r| Ok((r.u32()?, r.u32()?)))?,
        };
        if r.at != bytes.len() {
            return Err("bytes after the shapes".into());
        }
        let n = shapes.shapes.len() as u32;
        let inside = |i: &u32| *i < n;
        let named = shapes.shapes.iter().all(|s| match s {
            Shape::Union { members, .. } | Shape::Variant { members, .. } => {
                members.iter().map(|m| &m.1).all(inside)
            }
            Shape::Record { fields, .. } | Shape::Inline { fields, .. } => {
                fields.iter().map(|f| &f.shape).all(inside)
            }
            Shape::List(e) | Shape::Set(e) | Shape::Stored { form: e, .. } => inside(e),
            Shape::Map(k, v) => inside(k) && inside(v),
            _ => true,
        });
        if !named
            || !shapes.records.iter().map(|r| &r.1).all(inside)
            || !shapes.boxes.iter().map(|b| &b.0).all(inside)
            || !shapes.plain.iter().all(|p| {
                inside(&p.0)
                    && matches!(shapes.shapes.get(p.1 as usize), Some(Shape::Stored { .. }))
            })
        {
            return Err("a shape that names no shape of its table".into());
        }
        Ok(shapes)
    }
}

/// Reads what `Shapes::encode` wrote.
struct ShapeReader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl ShapeReader<'_> {
    fn u8(&mut self) -> Result<u8, String> {
        let b = *self.bytes.get(self.at).ok_or("the shapes end early")?;
        self.at += 1;
        Ok(b)
    }

    fn u32(&mut self) -> Result<u32, String> {
        let end = self.at + 4;
        let b = self.bytes.get(self.at..end).ok_or("the shapes end early")?;
        self.at = end;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn seq<T>(
        &mut self,
        mut item: impl FnMut(&mut Self) -> Result<T, String>,
    ) -> Result<Vec<T>, String> {
        let n = self.u32()? as usize;
        // Each item takes a byte at least.
        if n > self.bytes.len() - self.at {
            return Err("the shapes end early".into());
        }
        (0..n).map(|_| item(self)).collect()
    }

    fn text(&mut self) -> Result<String, String> {
        let bytes = self.seq(ShapeReader::u8)?;
        String::from_utf8(bytes).map_err(|_| "text that is not UTF-8".to_string())
    }

    fn shape(&mut self) -> Result<Shape, String> {
        Ok(match self.u8()? {
            0 => Shape::Unit,
            1 => Shape::Tag(self.text()?),
            2 => Shape::Number(match self.u8()? {
                0 => Number::Signed,
                1 => Number::Unsigned,
                2 => Number::Float,
                3 => Number::Fixed(self.u32()?),
                4 => Number::CodePoint,
                tag => return Err(format!("a number with the tag {tag}")),
            }),
            3 => Shape::Union {
                members: self.seq(|r| Ok((r.u32()?, r.u32()?)))?,
                words: self.u32()?,
            },
            13 => Shape::Variant {
                members: self.seq(|r| Ok((r.u32()?, r.u32()?)))?,
                words: self.u32()?,
            },
            4 => Shape::Record {
                name: match self.u8()? {
                    0 => None,
                    1 => Some(self.text()?),
                    tag => return Err(format!("an option with the tag {tag}")),
                },
                fields: self.seq(|r| {
                    Ok(ShapeField {
                        name: r.text()?,
                        offset: r.u32()?,
                        shape: r.u32()?,
                    })
                })?,
            },
            5 => Shape::List(self.u32()?),
            6 => Shape::Set(self.u32()?),
            7 => Shape::Map(self.u32()?, self.u32()?),
            8 => Shape::Function,
            9 => Shape::Opaque {
                name: self.text()?,
                words: self.u32()?,
            },
            10 => Shape::Str,
            11 => Shape::Bytes,
            12 => Shape::Inline {
                name: match self.u8()? {
                    0 => None,
                    1 => Some(self.text()?),
                    tag => return Err(format!("an option with the tag {tag}")),
                },
                fields: self.seq(|r| {
                    Ok(ShapeField {
                        name: r.text()?,
                        offset: r.u32()?,
                        shape: r.u32()?,
                    })
                })?,
                words: self.u32()?,
            },
            14 => Shape::Stored {
                form: self.u32()?,
                size: self.u32()?,
                slots: self.slots()?,
                words: self.u32()?,
            },
            tag => return Err(format!("a shape with the tag {tag}")),
        })
    }

    fn slots(&mut self) -> Result<Vec<StoredSlot>, String> {
        self.seq(|r| {
            Ok(StoredSlot {
                at: r.u32()?,
                offset: r.u32()?,
                size: r.u32()?,
                bits: match r.u8()? {
                    0 => None,
                    _ => Some((r.u8()?, r.u8()?)),
                },
                kind: match r.u8()? {
                    0 => StoredKind::Int {
                        signed: r.u8()? != 0,
                    },
                    1 => StoredKind::Words,
                    2 => StoredKind::Tag(r.seq(ShapeReader::u32)?),
                    3 => StoredKind::Union {
                        tag: match r.u8()? {
                            0 => StoredTag::Bytes {
                                offset: r.u32()?,
                                size: r.u32()?,
                            },
                            1 => StoredTag::Niche {
                                empty: r.u32()?,
                                offset: r.u32()?,
                                size: r.u8()?,
                                value: r.u64()?,
                            },
                            tag => return Err(format!("a union tag with the tag {tag}")),
                        },
                        members: r.seq(|r| Ok((r.u32()?, r.slots()?)))?,
                    },
                    tag => return Err(format!("a stored slot with the tag {tag}")),
                },
            })
        })
    }

    fn u64(&mut self) -> Result<u64, String> {
        let end = self.at + 8;
        let b = self.bytes.get(self.at..end).ok_or("the shapes end early")?;
        self.at = end;
        Ok(u64::from_le_bytes(b.try_into().expect("eight bytes")))
    }
}

/// Writes the slots of a stored shape, as `ShapeReader::slots` reads them.
fn stored_slots(out: &mut Vec<u8>, slots: &[StoredSlot]) {
    let u32 = |out: &mut Vec<u8>, n: u32| out.extend_from_slice(&n.to_le_bytes());
    u32(out, slots.len() as u32);
    for slot in slots {
        u32(out, slot.at);
        u32(out, slot.offset);
        u32(out, slot.size);
        match slot.bits {
            None => out.push(0),
            Some((bit, width)) => out.extend([1, bit, width]),
        }
        match &slot.kind {
            StoredKind::Int { signed } => out.extend([0, u8::from(*signed)]),
            StoredKind::Words => out.push(1),
            StoredKind::Tag(members) => {
                out.push(2);
                u32(out, members.len() as u32);
                for &m in members {
                    u32(out, m);
                }
            }
            StoredKind::Union { tag, members } => {
                out.push(3);
                match *tag {
                    StoredTag::Bytes { offset, size } => {
                        out.push(0);
                        u32(out, offset);
                        u32(out, size);
                    }
                    StoredTag::Niche {
                        empty,
                        offset,
                        size,
                        value,
                    } => {
                        out.push(1);
                        u32(out, empty);
                        u32(out, offset);
                        out.push(size);
                        out.extend_from_slice(&value.to_le_bytes());
                    }
                }
                u32(out, members.len() as u32);
                for (index, member) in members {
                    u32(out, *index);
                    stored_slots(out, member);
                }
            }
        }
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
    /// member's word, which for a member of two words points at the member
    /// box that holds them. Each member by its type index.
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
    /// A record split into registers (Implementation Plan §11.10.10): its
    /// fields' words one after another, each field's offset the index of
    /// its first word, in the order they are shown.
    Inline {
        name: Option<String>,
        fields: Vec<ShapeField>,
        words: u32,
    },
    /// A union split into registers: the type index of the member, then
    /// the member's own words, a record's inline. Each member by its type
    /// index.
    Variant {
        members: Vec<(u32, u32)>,
        words: u32,
    },
    /// A field of a box, or an element of a collection, stored flat
    /// (Compiler Architecture §A11.4): the `size` bytes at its offset, or
    /// the element's, hold, as `slots` say, the words of a value of the
    /// shape `form`.
    Stored {
        form: u32,
        size: u32,
        slots: Vec<StoredSlot>,
        words: u32,
    },
}

/// Where a value of a register form is in a storage form (Compiler
/// Architecture §A11.4): the word it starts at, and how bytes or bits hold
/// it from `offset` on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StoredSlot {
    pub at: u32,
    pub offset: u32,
    pub size: u32,
    /// Its first bit and width in the byte at `offset`.
    pub bits: Option<(u8, u8)>,
    pub kind: StoredKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StoredKind {
    /// An integer of `size` bytes, extended with its sign or with zeros.
    Int { signed: bool },
    /// Words as they are.
    Words,
    /// A union of tags: its local tag, which numbers the members whose
    /// type indices these are.
    Tag(Vec<u32>),
    /// A union whose word at `at` holds its member's type index: how
    /// storage tells the member, and each member's type index and slots.
    Union {
        tag: StoredTag,
        members: Vec<(u32, Vec<StoredSlot>)>,
    },
}

/// How the storage form of a union tells its member.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StoredTag {
    /// The member's local tag in `size` bytes at `offset`.
    Bytes { offset: u32, size: u32 },
    /// The member `empty`, of no words, is the other's niche: `size` bytes
    /// at `offset` that hold `value`, or with `size` zero, the bit `value`
    /// of the byte there set.
    Niche {
        empty: u32,
        offset: u32,
        size: u8,
        value: u64,
    },
}

/// The `size` bytes at `offset`, little-endian.
fn read_le(bytes: &[u8], offset: u32, size: u32) -> u64 {
    let mut out = [0u8; 8];
    let (from, n) = (offset as usize, size as usize);
    out[..n].copy_from_slice(&bytes[from..from + n]);
    u64::from_le_bytes(out)
}

/// The low `width` bits of `value` put at bit `bit` of the bytes from
/// `offset` on, which hold zeros there.
fn or_le(bytes: &mut [u8], offset: u32, bit: u32, width: u32, value: u64) {
    let value = match width {
        64 => value,
        w => value & ((1u64 << w) - 1),
    };
    let wide = u128::from(value) << bit;
    let n = (bit + width).div_ceil(8) as usize;
    for (k, b) in wide.to_le_bytes()[..n].iter().enumerate() {
        bytes[offset as usize + k] |= b;
    }
}

impl StoredTag {
    /// The index of the member the bytes hold.
    fn member(&self, bytes: &[u8]) -> usize {
        match *self {
            StoredTag::Bytes { offset, size } => read_le(bytes, offset, size) as usize,
            StoredTag::Niche {
                empty,
                offset,
                size,
                value,
            } => {
                let niche = match size {
                    0 => u64::from(bytes[offset as usize] >> value & 1) == 1,
                    size => read_le(bytes, offset, u32::from(size)) == value,
                };
                match niche {
                    true => empty as usize,
                    false => 1 - empty as usize,
                }
            }
        }
    }
}

/// Puts the register form of a value stored as `slots` in `bytes` into
/// `out`, as generated code loads it.
pub fn widen(slots: &[StoredSlot], bytes: &[u8], out: &mut [u64]) {
    for slot in slots {
        let at = slot.at as usize;
        match &slot.kind {
            StoredKind::Words => {
                for k in 0..(slot.size / 8) {
                    out[at + k as usize] = read_le(bytes, slot.offset + 8 * k, 8);
                }
            }
            StoredKind::Int { signed } => {
                let raw = read_le(bytes, slot.offset, slot.size);
                let unused = 64 - 8 * slot.size;
                out[at] = match (signed, unused) {
                    (_, 0) | (false, _) => raw,
                    (true, _) => ((raw << unused) as i64 >> unused) as u64,
                };
            }
            StoredKind::Tag(members) => {
                let tag = match slot.bits {
                    Some((bit, width)) => {
                        u64::from(bytes[slot.offset as usize] >> bit) & ((1 << width) - 1)
                    }
                    None => read_le(bytes, slot.offset, slot.size),
                };
                out[at] = members.get(tag as usize).copied().map_or(0, u64::from);
            }
            StoredKind::Union { tag, members } => {
                let Some((index, member)) = members.get(tag.member(bytes)) else {
                    continue;
                };
                out[at] = u64::from(*index);
                widen(member, bytes, out);
            }
        }
    }
}

/// Puts the register form of a value in `words` into `bytes` as `slots`
/// store it, as generated code stores it. The bytes the slots take hold
/// zeros before.
pub fn narrow(slots: &[StoredSlot], words: &[u64], bytes: &mut [u8]) {
    for slot in slots {
        let at = slot.at as usize;
        match &slot.kind {
            StoredKind::Words => {
                for k in 0..(slot.size / 8) {
                    or_le(bytes, slot.offset + 8 * k, 0, 64, words[at + k as usize]);
                }
            }
            StoredKind::Int { .. } => or_le(bytes, slot.offset, 0, 8 * slot.size, words[at]),
            StoredKind::Tag(members) => {
                let tag = members
                    .iter()
                    .position(|&m| u64::from(m) == words[at])
                    .unwrap_or(0) as u64;
                match slot.bits {
                    Some((bit, width)) => or_le(bytes, slot.offset, bit.into(), width.into(), tag),
                    None => or_le(bytes, slot.offset, 0, 8 * slot.size, tag),
                }
            }
            StoredKind::Union { tag, members } => {
                let Some(k) = members.iter().position(|m| u64::from(m.0) == words[at]) else {
                    continue;
                };
                match *tag {
                    StoredTag::Bytes { offset, size } => {
                        or_le(bytes, offset, 0, 8 * size, k as u64)
                    }
                    StoredTag::Niche {
                        empty,
                        offset,
                        size: 0,
                        value,
                    } if empty as usize == k => or_le(bytes, offset, value as u32, 1, 1),
                    StoredTag::Niche {
                        empty,
                        offset,
                        size,
                        value,
                    } if empty as usize == k => or_le(bytes, offset, 0, 8 * u32::from(size), value),
                    StoredTag::Niche { .. } => {}
                }
                narrow(&members[k].1, words, bytes);
            }
        }
    }
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
            Shape::Union { words, .. }
            | Shape::Opaque { words, .. }
            | Shape::Inline { words, .. }
            | Shape::Variant { words, .. }
            | Shape::Stored { words, .. } => *words,
            Shape::Function | Shape::Str | Shape::Bytes => 2,
        }
    }

    /// The words a value of the shape takes in a collection: a stored
    /// one's storage form, which `widen` turns into its `words`.
    pub fn element_words(&self) -> u32 {
        match self {
            Shape::Stored { size, .. } => size.div_ceil(8),
            shape => shape.words(),
        }
    }

    /// The type index word of the member box that holds a value of the
    /// shape in a union; none for a shape of fewer than two words, which
    /// a union holds as it is.
    pub fn member_box(&self) -> Option<u64> {
        match self {
            Shape::Str | Shape::Bytes => Some(TEXT_BOX_HEADER),
            Shape::Function => Some(FUNCTION_BOX_HEADER),
            _ => None,
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
    fn stored_values_widen_to_what_they_narrowed_from() {
        let slot = |at, offset, size, bits, kind| StoredSlot {
            at,
            offset,
            size,
            bits,
            kind,
        };
        let slots = vec![
            slot(0, 0, 1, None, StoredKind::Int { signed: false }),
            slot(1, 1, 1, Some((0, 1)), StoredKind::Tag(vec![7, 8])),
            slot(2, 1, 1, Some((1, 2)), StoredKind::Tag(vec![9, 10, 11])),
            slot(3, 2, 2, None, StoredKind::Int { signed: true }),
            slot(
                4,
                4,
                12,
                None,
                StoredKind::Union {
                    tag: StoredTag::Bytes { offset: 4, size: 1 },
                    members: vec![
                        (20, vec![slot(5, 8, 8, None, StoredKind::Words)]),
                        (21, vec![]),
                    ],
                },
            ),
            slot(
                6,
                16,
                2,
                None,
                StoredKind::Union {
                    tag: StoredTag::Niche {
                        empty: 1,
                        offset: 16,
                        size: 2,
                        value: 0,
                    },
                    members: vec![
                        (
                            30,
                            vec![slot(7, 16, 2, None, StoredKind::Int { signed: true })],
                        ),
                        (31, vec![]),
                    ],
                },
            ),
        ];
        for words in [
            [
                200,
                8,
                11,
                -5i64 as u64,
                20,
                0xdead_beef,
                30,
                -1234i64 as u64,
            ],
            [0, 7, 9, 5, 21, 0, 31, 0],
        ] {
            let mut bytes = [0u8; 24];
            narrow(&slots, &words, &mut bytes);
            let mut out = [0u64; 8];
            widen(&slots, &bytes, &mut out);
            assert_eq!(out, words);
        }
        let mut bytes = [0u8; 24];
        narrow(&slots, &[0, 7, 9, 0, 20, 0, 31, 0], &mut bytes);
        assert!(
            FieldGuard::Tag {
                offset: 4,
                tags: vec![0]
            }
            .holds(&bytes)
        );
        assert!(
            !FieldGuard::NotValue {
                offset: 16,
                size: 2,
                value: 0
            }
            .holds(&bytes)
        );
        assert!(FieldGuard::BitClear { offset: 1, bit: 0 }.holds(&bytes));
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
