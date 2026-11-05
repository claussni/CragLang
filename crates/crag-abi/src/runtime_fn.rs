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

//! The runtime's functions, which generated code calls (Compiler
//! Architecture §10), and the codes their operations and answers take.

table! {
    /// Runtime functions that generated code calls. Code objects name them in
    /// relocations; the loader resolves them to addresses.
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
        Morestack = 0 => "rt_morestack",

        /// `rt_side_grow(ctx: *mut TaskContext, size: usize, align: usize)`.
        ///
        /// Called when a side-stack push does not fit the current chunk. The
        /// runtime makes the side-stack fields of the context describe a chunk
        /// with room for `size` bytes at alignment `align`, and generated code
        /// then repeats the push. It has the same convention as `rt_morestack`:
        /// C argument registers, every register preserved, no result.
        SideGrow = 1 => "rt_side_grow",

        /// `rt_trap(ctx: *mut TaskContext, kind: u64, position: u64) -> !`, with
        /// `kind` a [`TrapKind`] and `position` the byte offset of the
        /// expression that trapped in its module's source, or [`NO_POSITION`].
        ///
        /// Called where a check fails, after the frame has released what it
        /// holds; it never returns. It releases what the frames below hold, as
        /// their stack maps list it, and ends the fiber (Implementation Plan
        /// §11.4.14). The functions from here on have the C calling convention,
        /// take the task context first, and run on the system stack.
        Trap = 2 => "rt_trap",

        /// `rt_alloc(ctx: *mut TaskContext, size: u64, type_index: u64) -> *mut u8`.
        ///
        /// A box of `size` bytes, header included, with a count of one and the
        /// type index in its header (Implementation Plan §11.4.11).
        Alloc = 3 => "rt_alloc",

        /// `rt_release(ctx: *mut TaskContext, ptr: *mut u8)`.
        ///
        /// Called when the inline decrement has taken a box's count from one to
        /// zero: releases the box's fields, using its type's descriptor, and
        /// frees it, and so on for every field whose count reaches zero
        /// (Implementation Plan §11.4.12). Retaining is inline code only.
        Release = 4 => "rt_release",

        /// `rt_list_push(ctx, list, w0, w1) -> list`.
        ///
        /// The list with the element appended, whose words are `w0` and `w1`
        /// as far as its layout has words, or of more than two words at the
        /// address in `w0` (`ElementLayout`). It takes the list's reference and the
        /// element's, and updates in place what only that reference holds
        /// (Implementation Plan §11.4.13).
        ListPush = 5 => "rt_list_push",

        /// `rt_list_elem(ctx, list, index) -> *const u64`.
        ///
        /// The address of the element's words, for an index inside the list. It
        /// borrows the list, and the address is valid while the list is.
        ListElem = 6 => "rt_list_elem",

        /// `rt_list_slice(ctx, list, front, back) -> list`.
        ///
        /// A new list of the elements without the first `front` and the last
        /// `back`, which together are at most the length. It borrows the list.
        ListSlice = 7 => "rt_list_slice",

        /// `rt_map_insert(ctx, map, k0, k1, v0, v1) -> map`.
        ///
        /// The map with the key bound to the value, words as for
        /// `rt_list_push`; a set is a map whose values have no words. It takes
        /// the references of the map, the key and the value.
        MapInsert = 8 => "rt_map_insert",

        /// `rt_map_get(ctx, map, k0, k1) -> *const u64`.
        ///
        /// The address of the words of the key's value, or null when the map
        /// has none. It borrows the map, and the address is valid while the map
        /// is.
        MapGet = 9 => "rt_map_get",

        /// `rt_refuel(ctx: *mut TaskContext)`.
        ///
        /// Called by metered code when its fuel went negative. It has the
        /// convention of `rt_morestack`: every register preserved, no result.
        /// The runtime refills the fuel and returns, or, when the task's steps
        /// or its memory budget are used up, or the fiber's poll asks it to
        /// stop, traps with `OutOfSteps`, `OutOfMemory` or `Cancelled` as
        /// `rt_trap` would at this call, releasing what the
        /// frames hold as the call's stack map lists it.
        Refuel = 10 => "rt_refuel",

        /// `rt_text_concat(ctx, a0, a1, b0, b1) -> (w0, w1)`.
        ///
        /// The string or bytes `a` followed by `b`, both borrowed, as a new
        /// value with a reference of its own (see [`INLINE_TEXT_MAX`]). Its
        /// two words come back in the first two result registers.
        TextConcat = 11 => "rt_text_concat",

        /// `rt_text_equals(ctx, a0, a1, b0, b1) -> u64`.
        ///
        /// 1 when the strings or bytes `a` and `b`, both borrowed, hold the
        /// same bytes, else 0.
        TextEquals = 12 => "rt_text_equals",

        /// `rt_text_show(ctx, word, number) -> (w0, w1)`.
        ///
        /// A number as a string, as interpolation writes it: the word, of the
        /// [`Number`] whose [`Number::code`] is `number`. A code point is its
        /// character.
        TextShow = 13 => "rt_text_show",

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
        Disposal = 14 => "rt_disposal",

        /// `rt_yield(ctx)`.
        ///
        /// Gives the other fibers a turn: the fiber suspends, goes to the back
        /// of a run queue and continues when a worker picks it again
        /// (Implementation Plan §11.7.1). Like every runtime function that may
        /// suspend, it returns on the fiber stack it was called on, possibly
        /// on another thread, and it is a point where a cancelled task traps
        /// with `Cancelled` instead of returning (§11.7.4).
        Yield = 15 => "rt_yield",

        /// `rt_sleep(ctx, nanos)`.
        ///
        /// Suspends the fiber for at least `nanos` nanoseconds (Implementation
        /// Plan §11.7.2). The other fibers run meanwhile; a fiber that no
        /// scheduler runs blocks its thread.
        Sleep = 16 => "rt_sleep",

        /// `rt_io_read(ctx, fd, buf, len) -> (n, errno)`.
        ///
        /// Reads at most `len` bytes from the non-blocking file descriptor `fd`
        /// into `buf`, suspending the fiber until some are there. Gives the
        /// count and zero, zero at the end of the input, or zero and the
        /// error number (Implementation Plan §11.7.2). `buf` must stay where it
        /// is until the call returns.
        IoRead = 17 => "rt_io_read",

        /// `rt_io_write(ctx, fd, buf, len) -> (n, errno)`.
        ///
        /// Writes at most `len` bytes of `buf` to `fd`, suspending the fiber
        /// until some can go; gives the count written, or zero and the error
        /// number, as `IoRead` does.
        IoWrite = 18 => "rt_io_write",

        /// `rt_io_accept(ctx, fd) -> (fd, errno)`.
        ///
        /// Accepts a connection on the listening socket `fd`, suspending the
        /// fiber until one comes. The new socket is non-blocking and closed on
        /// exec.
        IoAccept = 19 => "rt_io_accept",

        /// `rt_io_connect(ctx, fd, addr, len) -> (0, errno)`.
        ///
        /// Connects the non-blocking socket `fd` to the socket address of
        /// `len` bytes at `addr`, suspending the fiber until the connection is
        /// made or fails.
        IoConnect = 20 => "rt_io_connect",

        /// `rt_scope_new(ctx, limit) -> scope`.
        ///
        /// A scope for the tasks a combinator or group starts (Implementation
        /// Plan §11.7.3): at most `limit` of them run at once, any number for
        /// zero. The fiber that creates it is its parent; cancellation waits
        /// until the scope ends (`ScopeEnd`). Traps with `Unsupported` on a
        /// fiber that no scheduler runs.
        ScopeNew = 21 => "rt_scope_new",

        /// `rt_scope_start(ctx, scope, code, env, flags) -> index`.
        ///
        /// Starts a task of the scope that calls `code(ctx, env)`, the code and
        /// environment of a function value, which it takes. The low two bits of
        /// `flags` are the code's number of results; with [`START_EXEMPT`] the
        /// task does not count towards the limit. Suspends while the limit is
        /// reached. Gives the task's index, from zero in the order of starts.
        /// The parent and the scope's own tasks may start tasks.
        ScopeStart = 22 => "rt_scope_start",

        /// `rt_scope_next(ctx, scope) -> (index, status)`.
        ///
        /// The next task of the scope to finish, as [`TASK_RETURNED`],
        /// [`TASK_CANCELLED`] or [`TASK_TRAPPED`], suspending until one does;
        /// [`SCOPE_DONE`] when every task has been given. A task that traps
        /// cancels the others, and once all are given the scope ends and the
        /// parent traps with its kind. Only the parent calls it; a cancelled
        /// parent cancels the tasks and goes on giving them.
        ScopeNext = 23 => "rt_scope_next",

        /// `rt_scope_result(ctx, scope, index) -> (w0, w1)`.
        ///
        /// The results of a task that returned, taken once, with their
        /// references.
        ScopeResult = 24 => "rt_scope_result",

        /// `rt_scope_cancel(ctx, scope)`.
        ///
        /// Cancels every task of the scope that has not finished, and the tasks
        /// started later (Implementation Plan §11.7.4).
        ScopeCancel = 25 => "rt_scope_cancel",

        /// `rt_scope_end(ctx, scope)`.
        ///
        /// Frees a scope whose tasks have all been given. Traps with
        /// `Cancelled` if the parent was cancelled meanwhile.
        ScopeEnd = 26 => "rt_scope_end",

        /// `rt_enter_no_cancel(ctx)`.
        ///
        /// Opens a region where cancellation waits (Specification §10.4):
        /// atomic blocks, update and `ext` closures, foreign calls, drop and
        /// dispose handlers. Regions nest.
        EnterNoCancel = 27 => "rt_enter_no_cancel",

        /// `rt_exit_no_cancel(ctx)`.
        ///
        /// Closes the innermost such region; when it was the last and the task
        /// was cancelled meanwhile, traps with `Cancelled`.
        ExitNoCancel = 28 => "rt_exit_no_cancel",

        /// `rt_stream_new(ctx, capacity, list) -> (sink, source)`.
        ///
        /// A stream with a buffer of `capacity` values, zero for a hand-off
        /// (Specification §10.5), and its two ends. Its values are laid out as
        /// the elements of the list type with index `list`, which the runtime
        /// needs to release those left in the buffer (Implementation Plan
        /// §11.7.5). Each end is closed at most once and disposed exactly once.
        StreamNew = 29 => "rt_stream_new",

        /// `rt_stream_put(ctx, sink, w0, w1) -> status`.
        ///
        /// Puts a value, suspending while the buffer is full: [`STREAM_OK`]
        /// once it is sent, else [`STREAM_CLOSED`] or [`STREAM_ABANDONED`].
        /// The value's references go with it only when it is sent. Cancellation
        /// takes effect here (§11.7.4).
        StreamPut = 30 => "rt_stream_put",

        /// `rt_stream_try_put(ctx, sink, w0, w1) -> status`.
        ///
        /// As `StreamPut`, but [`STREAM_FULL`] instead of waiting.
        StreamTryPut = 31 => "rt_stream_try_put",

        /// `rt_stream_next(ctx, source, out) -> status`.
        ///
        /// Takes the next value, suspending while there is none: [`STREAM_OK`]
        /// with the value's words, and references, at `out`, else
        /// [`STREAM_CLOSED`] or [`STREAM_ABANDONED`] once the producers are
        /// gone and the buffer is empty. `out` must stay where it is until the
        /// call returns. Cancellation takes effect here.
        StreamNext = 32 => "rt_stream_next",

        /// `rt_stream_close(ctx, end)`.
        ///
        /// Ends a stream deliberately from either end, or leaves a hub: the
        /// other side reads `Closed` (Specification §10.5.2).
        StreamClose = 33 => "rt_stream_close",

        /// `rt_stream_dispose(ctx, end)`.
        ///
        /// Frees an end. One that was not closed is abandoned: the other side
        /// reads `Abandoned`.
        StreamDispose = 34 => "rt_stream_dispose",

        /// `rt_hub_new(ctx, capacity, list, kind) -> hub`.
        ///
        /// A hub of [`HUB_FAN_OUT`] or [`HUB_BROADCAST`], with values laid out
        /// as for `StreamNew` (Specification §10.6). Its ends are those of
        /// streams.
        HubNew = 35 => "rt_hub_new",

        /// `rt_hub_sink(ctx, hub) -> sink`.
        ///
        /// Joins as a producer; after `HubSeal` the sink starts closed.
        HubSink = 36 => "rt_hub_sink",

        /// `rt_hub_source(ctx, hub) -> source`.
        ///
        /// Joins as a consumer, from the values put from now on.
        HubSource = 37 => "rt_hub_source",

        /// `rt_hub_seal(ctx, hub)`.
        ///
        /// Admits no further producers: once every producer has left, the
        /// consumers read `Closed`, or `Abandoned` if one left without closing.
        HubSeal = 38 => "rt_hub_seal",

        /// `rt_hub_release(ctx, hub, n)`.
        ///
        /// Makes `n` consumers of a fan-out read `Closed`: those waiting now,
        /// and the rest at their next `StreamNext`.
        HubRelease = 39 => "rt_hub_release",

        /// `rt_hub_drop(ctx, hub)`.
        ///
        /// Gives up the hub's handle, which seals it.
        HubDrop = 40 => "rt_hub_drop",

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
        RefRead = 41 => "rt_ref_read",

        /// `rt_ref_commit(ctx, cell, version, list, w0, w1) -> status`.
        ///
        /// Ends an update begun by `RefRead`: [`REF_COMMITTED`] when the cell
        /// still holds `version`, else [`REF_CONFLICT`] and the update must
        /// rerun. The value is laid out as the `ref_cell` of the list type
        /// with index `list` says (`TypeDescriptor::List`). A committed value's references go to the cell; one
        /// identical to the value read is not written and its references are
        /// given up (Specification §9.3), and so are those of a value that
        /// conflicted. Unpins the task.
        RefCommit = 42 => "rt_ref_commit",

        /// `rt_ref_done(ctx)`.
        ///
        /// Ends a read that writes nothing, as `use` or an update whose closure
        /// gave an error: unpins the task.
        RefDone = 43 => "rt_ref_done",

        /// `rt_ref_swap(ctx, cell, list, w0, w1) -> (w0, w1)`.
        ///
        /// Places a value, laid out as for `RefCommit`, with its references,
        /// and gives the old one with references of its own.
        RefSwap = 44 => "rt_ref_swap",

        /// `rt_tx_begin(ctx) -> depth`.
        ///
        /// Opens an `atomic` block (Specification §9.5): the outermost starts
        /// an attempt of a transaction, an inner one takes a savepoint
        /// (Implementation Plan §11.7.7). Gives the number of blocks open, 1
        /// for the outermost. The block is a region where cancellation waits,
        /// and nothing in it may suspend.
        TxBegin = 45 => "rt_tx_begin",

        /// `rt_tx_read(ctx, cell, out) -> status`.
        ///
        /// Reads a ref cell in the block: [`TX_OK`] with the value's two words
        /// at `out`, borrowed, which is what the block wrote to it if it did,
        /// else [`TX_CONFLICT`], and the outermost block must rerun.
        TxRead = 46 => "rt_tx_read",

        /// `rt_tx_write(ctx, cell, list, w0, w1)`.
        ///
        /// Writes a value, laid out as for `RefCommit`, with its references, to
        /// a ref cell at the commit. One identical to what the block sees is
        /// not written, and its references are given up.
        TxWrite = 47 => "rt_tx_write",

        /// `rt_tx_commit(ctx) -> status`.
        ///
        /// Closes the block: an inner one keeps its writes for the outermost,
        /// which writes them all at once, [`TX_OK`], or [`TX_CONFLICT`] and it
        /// must rerun.
        TxCommit = 48 => "rt_tx_commit",

        /// `rt_tx_abort(ctx)`.
        ///
        /// Closes a block whose value is an error: its writes are dropped, and
        /// those of the blocks around it stay (Specification §9.5.1).
        TxAbort = 49 => "rt_tx_abort",

        /// `rt_tx_retry(ctx)`.
        ///
        /// After a conflict, drops the attempt's reads and writes, backs off
        /// and starts the outermost block's next attempt, after which the
        /// block's code runs again from its start.
        TxRetry = 50 => "rt_tx_retry",

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
        RefApply = 51 => "rt_ref_apply",

        /// `rt_ext_new(ctx) -> ext`.
        ///
        /// Makes the lock of an `ext` binding (Specification §9.6), whose value
        /// generated code keeps and touches only while it holds the lock.
        ExtNew = 52 => "rt_ext_new",

        /// `rt_ext_lock(ctx, ext)`.
        ///
        /// Takes the lock before an access closure runs, suspending while
        /// another task holds it; a point where a cancelled task traps. A task
        /// holds at most one lock, and one that stops gives it up.
        ExtLock = 53 => "rt_ext_lock",

        /// `rt_ext_unlock(ctx, ext)`.
        ///
        /// Gives the lock up after the closure, to the task that waited
        /// longest.
        ExtUnlock = 54 => "rt_ext_unlock",

        /// `rt_ext_free(ctx, ext)`.
        ///
        /// Frees the lock when the binding's scope ends, which no task holds
        /// or waits for any more (§10.1).
        ExtFree = 55 => "rt_ext_free",

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
        SignalEmit = 56 => "rt_signal_emit",

        /// `rt_signal_next(ctx, out) -> list`.
        ///
        /// Takes the next signal an outcome made deliverable: its list type,
        /// with its two words and its `info` at `out`, or [`SIGNAL_NONE`].
        /// The signal is borrowed until the next call, which gives it up.
        /// Generated code calls it after `TxCommit`, `TxAbort`, `TxRetry`,
        /// `RefCommit` and `RefDone` until there is none, and delivers each.
        SignalNext = 57 => "rt_signal_next",

        /// `rt_lazy_new(ctx, list) -> lazy`.
        ///
        /// Makes a lazy cell (Specification §6.10) for a value laid out as the
        /// elements of the list type with index `list`.
        LazyNew = 58 => "rt_lazy_new",

        /// `rt_lazy_get(ctx, lazy, out) -> status`.
        ///
        /// Reads a lazy cell (Implementation Plan §11.7.11): [`LAZY_DONE`] with
        /// the value's two words at `out` and references of its own;
        /// [`LAZY_RUN`] when the caller must compute the value and store it
        /// with `LazySet`; or [`LAZY_TRAPPED`] with the kind of the trap at
        /// `out`, at which the caller traps. Suspends while another task
        /// computes the value; a point where a cancelled task traps.
        LazyGet = 59 => "rt_lazy_get",

        /// `rt_lazy_set(ctx, lazy, w0, w1)`.
        ///
        /// Stores the value the caller computed, with its references, and
        /// hands it to the reads that wait.
        LazySet = 60 => "rt_lazy_set",

        /// `rt_lazy_free(ctx, lazy)`.
        ///
        /// Frees the cell, which no task reads any more, with its value.
        LazyFree = 61 => "rt_lazy_free",

        /// `rt_release_deferred(ctx, ptr)`.
        ///
        /// As `Release`, for a box of a type that is not `Immediate`
        /// (Specification §13.3): frees a bounded part of the structure and
        /// leaves the rest to the scheduler, which frees it between fibers and
        /// runs the `Deferred` dispose handlers in it as tasks of their own
        /// (Implementation Plan §11.7.12). The handlers of the part freed at
        /// once are queued for `Disposal`, as `Release` queues them.
        ReleaseDeferred = 62 => "rt_release_deferred",

        /// `rt_tx_throw(ctx) -> !`.
        ///
        /// Leaves the attempt of a transaction from code an `atomic` block
        /// called: releases what the frames hold, as a trap does, up to the
        /// first frame whose call has a handler, and continues at the handler
        /// (Implementation Plan §11.7.14).
        TxThrow = 63 => "rt_tx_throw",

        /// `rt_io_listen(ctx, port) -> (fd, errno)`.
        ///
        /// A non-blocking TCP socket listening on the loopback interface at
        /// `port`, any free one for zero (Implementation Plan §11.7.14).
        IoListen = 64 => "rt_io_listen",

        /// `rt_io_port(ctx, fd) -> port`.
        ///
        /// The port a socket is bound to.
        IoPort = 65 => "rt_io_port",

        /// `rt_io_socket(ctx) -> (fd, errno)`.
        ///
        /// A new non-blocking TCP socket, for `IoConnectLocal`.
        IoSocket = 66 => "rt_io_socket",

        /// `rt_io_connect_local(ctx, fd, port) -> (0, errno)`.
        ///
        /// Connects a socket to `port` on the loopback interface, suspending
        /// until the connection is made, as `IoConnect` does.
        IoConnectLocal = 67 => "rt_io_connect_local",

        /// `rt_io_buffer(ctx, len) -> buffer`.
        ///
        /// A buffer of a string or bytes with room for `len` bytes, for a read
        /// into it after its header.
        IoBuffer = 68 => "rt_io_buffer",

        /// `rt_io_bytes(ctx, buffer, n) -> (w0, w1)`.
        ///
        /// The bytes value of the first `n` bytes of a buffer from `IoBuffer`,
        /// whose reference it takes: inline when they fit, and the buffer is
        /// freed.
        IoBytes = 69 => "rt_io_bytes",

        /// `rt_io_write_bytes(ctx, fd, w0, w1, left) -> (left, errno)`.
        ///
        /// Writes the last `left` bytes of a bytes value, all of them for
        /// `u64::MAX`, suspending until some can go: how many are left
        /// afterwards, or the error number. The caller holds the value until
        /// the call returns.
        IoWriteBytes = 70 => "rt_io_write_bytes",

        /// `rt_signal_mark(ctx) -> mark`.
        ///
        /// How many signal handlers the task has registered: the base of a
        /// block's handlers, which `SignalReset` returns to when the block
        /// ends (Implementation Plan §11.7.14).
        SignalMark = 71 => "rt_signal_mark",

        /// `rt_signal_reset(ctx, mark)`.
        ///
        /// Forgets the handlers registered since the mark.
        SignalReset = 72 => "rt_signal_reset",

        /// `rt_signal_on(ctx, code, env, types, packed, base)`.
        ///
        /// Registers a handler (Specification §11.3) of the block whose mark is
        /// `base`: its function value, which the caller keeps until the block
        /// ends, and a sorted array of the `u32` type indices of the signal
        /// types it takes, in static data. `packed` holds the array's length
        /// in its upper half, then how many parent types the handler's type
        /// has, shifted by 8, then the words of its parameter, zero or one.
        SignalOn = 73 => "rt_signal_on",

        /// `rt_signal_find(ctx, index, out) -> found`.
        ///
        /// Finds the handler of a signal of type index `index`: the innermost
        /// block's that takes it, and of those the most specific. Gives 1 with
        /// its code, its environment and the words of its parameter at `out`,
        /// and hides its block and those above while it runs, until
        /// `SignalLeave`; else 0.
        SignalFind = 74 => "rt_signal_find",

        /// `rt_signal_leave(ctx)`.
        ///
        /// Shows what `SignalFind` hid, once the handler returned.
        SignalLeave = 75 => "rt_signal_leave",

        /// `rt_signal_default(ctx, name, len)`.
        ///
        /// The root's handler of a signal no handler takes: writes the name of
        /// its type to standard error.
        SignalDefault = 76 => "rt_signal_default",

        /// `rt_step(ctx, cell, words, count, fp, inlined)`.
        ///
        /// A statement's step, called while its flag is set (Implementation
        /// Plan §11.8.6): `cell` is the step's cell, whose second word names
        /// it (`step_cell_word`), so code holds no function id outside its
        /// relocations and can be kept across programs; the `count` words at
        /// `words` are those of its locals, `fp` is the frame pointer of the
        /// calling frame, and `inlined` how many inlined calls deep in the
        /// frame's code the step is (Implementation Plan §11.10.1). The
        /// debugger may stop the task here; it returns once the task is
        /// resumed.
        Step = 77 => "rt_step",

        /// `rt_io_print(ctx, w0, w1, newline) -> errno`.
        ///
        /// Writes a string to standard output, with a newline when `newline`
        /// is 1, as one write that other prints do not interleave with: 0, or
        /// the error number (Specification §15.6).
        IoPrint = 78 => "rt_io_print",

        /// `rt_io_read_file(ctx, w0, w1, out) -> errno`.
        ///
        /// Reads the whole file the string names into a bytes value, whose
        /// two words it writes at `out`: 0, or the error number.
        IoReadFile = 79 => "rt_io_read_file",

        /// `rt_io_socket_any(ctx) -> (fd, errno)`.
        ///
        /// A new non-blocking TCP socket for `IoConnectHost`, which reaches
        /// IPv6 and IPv4 addresses alike where the system has IPv6.
        IoSocketAny = 80 => "rt_io_socket_any",

        /// `rt_io_connect_host(ctx, fd, w0, w1, port) -> (0, errno)`.
        ///
        /// Looks up the host the string names and connects a socket from
        /// `IoSocketAny` to `port` there, suspending until the connection is
        /// made: 0, the error number, or [`UNKNOWN_HOST`] when the name has no
        /// address.
        IoConnectHost = 81 => "rt_io_connect_host",

        /// `rt_text_utf8(ctx, w0, w1) -> 1 | 0`.
        ///
        /// Whether the bytes of a value are valid UTF-8.
        TextUtf8 = 82 => "rt_text_utf8",

        /// `rt_text_measure(ctx, op, w0, w1) -> n`.
        ///
        /// A count of a string or bytes value, by the operation of
        /// [`text_op`]: `BYTE_COUNT` or `CODE_POINT_COUNT`.
        TextMeasure = 83 => "rt_text_measure",

        /// `rt_text_at(ctx, op, w0, w1, at) -> n`.
        ///
        /// What is at a byte offset: `IS_BOUNDARY`, `NEXT`, `PREVIOUS`,
        /// `CODE_POINT_AT` or `BYTE_AT` of [`text_op`]; -1 where there is
        /// nothing.
        TextAt = 84 => "rt_text_at",

        /// `rt_text_find(ctx, a0, a1, b0, b1, packed) -> n`.
        ///
        /// Looks for the second value in the first. `packed` holds the
        /// operation of [`text_op`] in its low 3 bits and the offset to
        /// search from above them: `INDEX_OF` and `LAST_INDEX_OF` give a byte
        /// offset or -1, `STARTS_WITH` and `ENDS_WITH` 1 or 0, and `COMPARE`
        /// 0, 1 or 2 for less, equal and greater, by the bytes.
        TextFind = 85 => "rt_text_find",

        /// `rt_text_map(ctx, op, w0, w1) -> (w0, w1)`.
        ///
        /// A new string from one: `TRIM`, `TRIM_START`, `TRIM_END`,
        /// `TO_UPPER`, `TO_LOWER` or `HEX` of [`text_op`].
        TextMap = 86 => "rt_text_map",

        /// `rt_text_slice(ctx, w0, w1, from, to) -> (w0, w1)`.
        ///
        /// The bytes from `from` up to `to`, both clamped to the value.
        TextSlice = 87 => "rt_text_slice",

        /// `rt_code_point(ctx, op, value) -> n`.
        ///
        /// A property or mapping of a code point, by the `CP_…` operations of
        /// [`text_op`].
        CodePointOp = 88 => "rt_code_point",

        /// `rt_text_parse(ctx, op, w0, w1, base) -> (value, ok)`.
        ///
        /// A number from text: `PARSE_INT` in the base, or `PARSE_FLOAT` as
        /// its bits; `ok` is 0 when the text is no such number.
        TextParse = 89 => "rt_text_parse",

        /// `rt_value_shapes(ctx, w0, w1) -> handle`.
        ///
        /// The runtime's handle of a type's shapes: the bytes of
        /// `Shapes::encode` after the root shape's index, four bytes little
        /// endian, decoded once for each distinct table.
        ValueShapes = 90 => "rt_value_shapes",

        /// `rt_value_op(ctx, packed, a0, a1, b0, b1) -> n`.
        ///
        /// Equality, order or the hash of values by their shape (Specification
        /// §19.11): `packed` holds the operation of [`value_op`] in its low 8
        /// bits and a handle of `ValueShapes` above them. `EQUALS` gives 1 or
        /// 0, `COMPARE` 0, 1 or 2 for less, equal and greater, or `UNORDERED`,
        /// and `HASH` the hash of the first value.
        ValueOp = 91 => "rt_value_op",

        /// `rt_value_show(ctx, handle, w0, w1) -> (w0, w1)`.
        ///
        /// A value written as source, as the REPL shows it.
        ValueShow = 92 => "rt_value_show",

        /// `rt_list_set(ctx, list, at, w0, w1) -> list`.
        ///
        /// The list with element `at` replaced. It takes the list's reference
        /// and the value's; `at` is inside the list.
        ListSet = 93 => "rt_list_set",

        /// `rt_list_concat(ctx, a, b) -> list`.
        ///
        /// A new list of the elements of `a`, then those of `b`. It borrows
        /// both.
        ListConcat = 94 => "rt_list_concat",

        /// `rt_map_remove(ctx, map, k0, k1) -> map`.
        ///
        /// The map or set without the key. It takes the map's reference and
        /// borrows the key.
        MapRemove = 95 => "rt_map_remove",

        /// `rt_map_list(ctx, map, list, values) -> list`.
        ///
        /// The list with the keys of the map or set after its elements, or
        /// with the values for `values` 1, in the map's order, each with a
        /// reference of its own. It borrows the map and takes the list's
        /// reference.
        MapList = 96 => "rt_map_list",

        /// `rt_test_record(ctx, w0, w1, position)`.
        ///
        /// Records a failed assertion of a test, its message and the byte
        /// offset of the assertion in its module (Specification §19.12).
        TestRecord = 97 => "rt_test_record",

        /// `rt_env_args(ctx, list) -> list`.
        ///
        /// The list of bytes values with the program's arguments after its
        /// elements, without the program's name (Specification §19.7). It takes
        /// the list's reference.
        EnvArgs = 98 => "rt_env_args",

        /// `rt_env_var(ctx, w0, w1, out) -> found`.
        ///
        /// Whether the environment has the variable the string names: 1, with
        /// its value's bytes written at `out`, or 0.
        EnvVar = 99 => "rt_env_var",

        /// `rt_env_vars(ctx, map) -> map`.
        ///
        /// The map of strings with the environment's variables bound, those
        /// whose name or value is not UTF-8 left out. It takes the map's
        /// reference.
        EnvVars = 100 => "rt_env_vars",

        /// `rt_env_platform(ctx, which) -> code`.
        ///
        /// The system for `which` 0, by the order of `Os` in `std.env`, or the
        /// processor for 1, by the order of `Arch`.
        EnvPlatform = 101 => "rt_env_platform",

        /// `rt_bytes_read(ctx, packed, w0, w1, at) -> (value, ok)`.
        ///
        /// The number of the kind of [`bytes_kind`] in the low 8 bits of
        /// `packed`, big-endian when bit 8 is set, at the byte offset: an
        /// integer sign- or zero-extended, a float as the bits of a `Float`;
        /// `ok` is 0 when it does not fit before the end, or a float is not
        /// finite.
        BytesRead = 102 => "rt_bytes_read",

        /// `rt_bytes_write(ctx, packed, w0, w1, at, value) -> (w0, w1)`.
        ///
        /// New bytes with the number written at the offset, as `BytesRead`
        /// reads it; the offset is inside the bytes.
        BytesWrite = 103 => "rt_bytes_write",

        /// `rt_bytes_of_list(ctx, list) -> (w0, w1)`.
        ///
        /// The bytes of a list of `UInt8` values. It borrows the list.
        BytesOfList = 104 => "rt_bytes_of_list",

        /// `rt_trap_catch(ctx, kind, position)`.
        ///
        /// A trap that a handler of its own frame takes (Specification
        /// §8.3.1): records it, as `rt_trap` records one it unwinds to a
        /// handler, and returns, so the frame goes on at the handler.
        TrapCatch = 105 => "rt_trap_catch",

        /// `rt_trap_rethrow(ctx) -> !`.
        ///
        /// Raises the trap a handler took again, for the handlers around it.
        TrapRethrow = 106 => "rt_trap_rethrow",

        /// `rt_trap_caught(ctx, which) -> u64`.
        ///
        /// Of the trap a handler took: its kind (0), the line (1) and the
        /// column (2) of its origin, from one.
        TrapCaught = 107 => "rt_trap_caught",

        /// `rt_trap_caught_text(ctx, which) -> (w0, w1)`.
        ///
        /// Of the trap a handler took, as a string: the module of its origin
        /// (0), its message (1), and what it names (2), such as the type of
        /// the error `!!` met.
        TrapCaughtText = 108 => "rt_trap_caught_text",

        /// `rt_tx_depth(ctx) -> depth`.
        ///
        /// How many `atomic` blocks the task is in.
        TxDepth = 109 => "rt_tx_depth",

        /// `rt_tx_unwind(ctx, depth)`.
        ///
        /// Abandons the transactions begun inside `depth`, as a trap leaves
        /// them for a handler outside (Specification §8.3.1).
        TxUnwind = 110 => "rt_tx_unwind",

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
        CCall = 111 => "rt_c_call",

        /// `rt_c_str_of(ctx, address, nul) -> (w0, w1)`.
        ///
        /// A copy of the NUL-terminated bytes at the address, which is not
        /// null, as `Bytes`: with the NUL when `nul` is not zero.
        CStrOf = 112 => "rt_c_str_of",

        /// `rt_value_decode(ctx, handle, b0, b1) -> word`.
        ///
        /// The value whose encoding the bytes `b0`, `b1` are, of a type of one
        /// word and a handle of `ValueShapes`, built on the heap: the tree of
        /// an `Expr`, which the compiler wrote (Plan §11.10.11).
        ValueDecode = 113 => "rt_value_decode",

        /// `rt_transport_run(ctx, scratch, x0, x1, i0, i1) -> status`.
        ///
        /// Runs the code of an `Expr` as received code (Plan §11.10.9): the
        /// program checks and compiles its tree again, then runs it as a
        /// metered task of its own on the input `i0`, `i1`, which the call
        /// takes, and waits for it. `scratch[3]` is the `Expr`'s environment,
        /// which it borrows; `scratch[0..3]` the policy: `Accept` as 0
        /// `Exact`, 1 `SameMajor` or 2 `Signature`, the steps and the bytes of
        /// memory; 256 added to `scratch[0]` says that the caller signalled
        /// the callees accepted with another body. `x0`, `x1` are the bytes of
        /// the function type the code is expected to have, an `FnType` (Plan
        /// §11.10.11). The status is 0 when it ran, with its result in
        /// `scratch[0..2]`; 1 to 3 when it was not accepted, as `Unresolved`,
        /// `IllTyped` or `Impure`, with the reason as a `Str` there; 4 or 5
        /// when it ran out of steps or memory, with nothing there; 6 when the
        /// caller has not signalled such callees yet, which did not run the
        /// code, with a `Str` there of one `module name` a line. A trap of the
        /// code is the call's. 7 when the `Expr` arrived under a budget that
        /// cannot run it, or 8 when the budget ran out while it ran, with the
        /// budget's index in `scratch[0]` (Specification §18.7).
        TransportRun = 114 => "rt_transport_run",
        /// `rt_transport_encode(ctx, scratch, env, stamp) -> status`: the bytes
        /// that send the `Expr` of the environment `env` (Plan §11.10.9),
        /// stamped with the process's sending budget `stamp`, or none when it
        /// is negative. The status is 0 with the `Bytes` in `scratch[0..2]`,
        /// or 1 with why it cannot be sent, a `Str`, there.
        TransportEncode = 115 => "rt_transport_encode",
        /// `rt_transport_decode(ctx, scratch, x0, x1, b0, b1) -> status`: the
        /// `Expr` that the bytes `b0`, `b1` send, checked against the function
        /// type `x0`, `x1` as `TransportRun` checks code, under the policy in
        /// `scratch[0..3]` as there. The status is 0 with the `Expr` in
        /// `scratch[0..2]`; 1 to 5 as for `TransportRun`; 7 when its stamp is
        /// missing or not valid, with why as a `Str` there; 8 when its budget
        /// is used up, with the budget's index there; 9 when the bytes are not
        /// code, with why as a `Str` there.
        TransportDecode = 116 => "rt_transport_decode",
        /// `rt_budget_op(ctx, scratch, op, side, index) -> value`: an
        /// operation on the process's budgets (`budget_op`), on side 0, those
        /// it enforces, or 1, those it sends under.
        BudgetOp = 117 => "rt_budget_op",
    }
    /// The symbol the loader looks up.
    fn symbol -> &'static str;
}

/// The operations of [`RuntimeFn::BudgetOp`]. Counts and numbers come
/// back as the value, -1 for a limit that is not set; text comes in the
/// scratch words, with 0 for done and -1 for no such budget.
pub mod budget_op {
    /// The budgets of the side.
    pub const COUNT: u64 = 0;
    /// The document's name, date and issuer, and the budget's name.
    pub const DOCUMENT: u64 = 1;
    pub const DATE: u64 = 2;
    pub const ISSUER: u64 = 3;
    pub const NAME: u64 = 4;
    /// The limits.
    pub const LIMIT_STEPS: u64 = 5;
    pub const LIMIT_MEMORY: u64 = 6;
    pub const LIMIT_RUNS: u64 = 7;
    /// What it has taken: steps, memory held, runs.
    pub const USED_STEPS: u64 = 8;
    pub const USED_MEMORY: u64 = 9;
    pub const USED_RUNS: u64 = 10;
    /// 0 when it read its files again, else 1 with why as a `Str`.
    pub const RENEW: u64 = 11;
    /// 0 when it gave back what it had taken.
    pub const RESET: u64 = 12;
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
