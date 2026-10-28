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

//! The MIR: a control-flow graph of basic blocks over typed locals.
//!
//! Locals are not in SSA form: a block may assign any local. A local holds
//! one value of its type; when that type is counted, the local owns one
//! reference while it is live. An operand that is a local gives that
//! reference away, and a place only borrows the local it starts at.

use crag_db::Db;
use crag_hir::{BindingId, ExprId, Name, Owner};
use crag_types::{Builtin, Step, Ty, TyKind};

use crate::{Entry, InstanceKey};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, crag_db::SalsaValue)]
pub struct Local(pub u32);

/// Index into `MirBody::blocks`. Block 0 is where execution starts, and
/// no terminator goes back to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, crag_db::SalsaValue)]
pub struct BlockId(pub u32);

impl Local {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl BlockId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct MirBody<'db> {
    /// Locals `0..params` hold the parameters on entry.
    pub params: usize,
    /// Whether the code is called as a function value, so that local 0 is
    /// its environment: one word, a box or null (§11.5.9).
    pub env: bool,
    pub locals: Vec<LocalDecl<'db>>,
    pub blocks: Vec<Block<'db>>,
    pub result: Ty<'db>,
    /// `Bool`, the type of the flags checks compute.
    pub bool_ty: Ty<'db>,
    /// What the builder does not lower yet; each traps where it is
    /// reached.
    pub unsupported: Vec<(ExprId, &'static str)>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct LocalDecl<'db> {
    pub ty: Ty<'db>,
    /// The binding it holds; none for a temporary.
    pub binding: Option<(BindingId, Name<'db>)>,
    /// Whether its values are reference-counted.
    pub counted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Block<'db> {
    pub statements: Vec<Statement<'db>>,
    pub terminator: Terminator<'db>,
    /// The handler of the trap handler around the block's code, which the
    /// checks of its arithmetic go to (§8.3.1).
    pub catch: Option<BlockId>,
}

/// A local, or a part of the value in it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct Place<'db> {
    pub local: Local,
    /// Never a `Slice`, which makes a new list.
    pub path: Vec<Step<'db>>,
}

impl<'db> Place<'db> {
    pub fn local(local: Local) -> Place<'db> {
        Place {
            local,
            path: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Operand<'db> {
    Local(Local),
    Const(Constant<'db>),
}

/// A constant, typed by where it goes.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Constant<'db> {
    /// A value of an integer type or a `CodePoint`, or of a `Fixed` in
    /// units of its scale.
    Int(i128),
    /// By its bits.
    Float(u64),
    Str(String),
    Bytes(Vec<u8>),
    /// The value of a tag type.
    Tag(Ty<'db>),
    Unit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// What a `Cast` does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum CastOp {
    /// The integer as another integer type it fits.
    Same,
    /// The integer wrapped to the width of an integer type.
    Wrap(Builtin),
    IntToFloat,
    /// Toward zero; the value fits `Int`.
    FloatToInt,
    Floor,
    Ceil,
    Trunc,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Rvalue<'db> {
    Use(Operand<'db>),
    /// A part of a value, borrowed from it.
    Read(Place<'db>),
    /// The operand as the type of the local it is assigned to: a type it
    /// fits, or a member of its union that a test has established.
    Convert(Operand<'db>),
    /// Arithmetic on a number type. With a check, the operation traps on
    /// overflow and on a zero divisor, at the expression; without one it
    /// is the machine's: integers wrap, and a `Float` follows IEEE 754.
    /// Checks become explicit operations before liveness (§3.1.1, §3.1.4).
    Binary {
        op: BinOp,
        ty: Builtin,
        a: Operand<'db>,
        b: Operand<'db>,
        check: Option<ExprId>,
    },
    /// A number as another number type: its bits as they are, wrapped to
    /// a narrower integer, between integers and `Float`, or a `Float`
    /// rounded to a whole number (§19.13). The prelude checks the range
    /// first where the result may not fit.
    Cast {
        op: CastOp,
        from: Builtin,
        value: Operand<'db>,
    },
    /// Whether the integer operation overflows its type.
    Overflows {
        op: BinOp,
        ty: Builtin,
        a: Operand<'db>,
        b: Operand<'db>,
    },
    /// Whether any of these `Float` results overflowed. Code generation
    /// may read and clear the sticky overflow flag instead of testing each.
    FloatOverflow(Vec<Local>),
    /// A comparison of numbers or code points, or `Eq` and `Ne` of
    /// strings and bytes: a `Bool`.
    Compare {
        op: CmpOp,
        ty: Builtin,
        a: Operand<'db>,
        b: Operand<'db>,
    },
    /// A record, its fields in the order of `fields_of`; for a type with a
    /// dispose handler, the dispose code its box holds (§11.6.11).
    Record {
        ty: Ty<'db>,
        fields: Vec<(Name<'db>, Operand<'db>)>,
        dispose: Option<InstanceKey<'db>>,
    },
    /// A list, or a set when the local is one.
    List(Vec<Operand<'db>>),
    Map(Vec<(Operand<'db>, Operand<'db>)>),
    /// Strings joined.
    Concat(Vec<Operand<'db>>),
    /// The number of elements of a list, an `Int`.
    Len(Place<'db>),
    /// An element of a list at an index known to lie inside it, borrowed.
    Index {
        list: Place<'db>,
        index: Operand<'db>,
    },
    /// The value of a map at a key, or `Empty`: an `Option`, borrowed,
    /// unless the values take two words, strings, bytes or function values:
    /// then the `Option` holds the value found in a member box of its own
    /// (Compiler Architecture §11), and is the code's.
    MapGet {
        map: Place<'db>,
        key: Operand<'db>,
        boxed: bool,
    },
    /// A list without its first `front` and last `back` elements.
    Slice {
        list: Place<'db>,
        front: u32,
        back: u32,
    },
    /// A function value: the code, and an environment of type `env`, a
    /// record of the captured values in its order, or null when there are
    /// none (§11.5.9). On the side stack the environment borrows the
    /// captured locals, which stay live while the value does; on the heap
    /// it takes their references.
    Closure {
        code: InstanceKey<'db>,
        env: Ty<'db>,
        captures: Vec<Operand<'db>>,
        placement: ClosurePlacement,
    },
    /// A function value of the code with an environment it already has:
    /// how a local function names itself.
    FnValue {
        code: InstanceKey<'db>,
        env: Operand<'db>,
    },
    /// An operation of the runtime, which a function of the standard
    /// library without a body or a binding stands for (Plan §11.7.14). It
    /// consumes the operands `Intrinsic::consumes` says, and borrows the
    /// others.
    Intrinsic(Intrinsic<'db>, Vec<Operand<'db>>),
}

/// The operations of the runtime that MIR names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Intrinsic<'db> {
    /// Suspends the task for a number of nanoseconds, an `Int` above
    /// zero: `std.time.sleepNanos`.
    Sleep,
    /// A new ref cell holding the value, a `Ref[T]` (Specification §9.1).
    RefNew,
    /// Begins a read of the ref cell: the version read, an `Int`. Nothing
    /// that suspends may come before the read ends with `RefDone` or
    /// `RefCommit`.
    RefRead,
    /// The value the last `RefRead` of the code read, borrowed from the
    /// cell.
    RefValue,
    /// Ends a read that writes nothing.
    RefDone,
    /// Ends a read with the ref cell, the version read and the new value:
    /// 0 when it was written, else the update must rerun. The value is
    /// given up when it was not written.
    RefCommit,
    /// Places the value in the ref cell and gives the old one.
    RefSwap,
    /// Applies `v op k` to the integer of type `ty` in the ref cell, as an
    /// update whose closure has that shape (§9.4), with the cell and `k`:
    /// 0, or 2 when the result does not fit the type and the cell is
    /// unchanged.
    RefApply {
        op: BinOp,
        ty: Builtin,
    },
    /// Opens an `atomic` block: the number of blocks open, an `Int`.
    TxBegin,
    /// How many `atomic` blocks the task is in, and abandoning those begun
    /// inside a depth, for a trap handler (§8.3.1).
    TxDepth,
    TxUnwind,
    /// Of the trap a handler took: its kind, the line or the column of its
    /// origin, by `rt_trap_caught`'s numbering; and its module, message or
    /// detail as a `Str`.
    TrapCaught(u8),
    TrapCaughtText(u8),
    /// Closes a block whose value is a success: 0, or else the attempt
    /// must rerun.
    TxCommit,
    /// Closes a block whose value is an error.
    TxAbort,
    /// Starts the next attempt of the outermost block.
    TxRetry,
    /// Leaves the attempt from code an `atomic` block of another function
    /// runs; it does not return.
    TxThrow,
    /// Whether a ref operation found that the attempt must rerun: an `Int`,
    /// nonzero if so.
    TxConflicted,
    /// The side stack's pointer and end, `Int`s, which `SideReset` gives
    /// back, freeing what was pushed since.
    SidePtr,
    SideEnd,
    SideReset,
    /// A scope of tasks with a limit, an `Int`; zero for none
    /// (`std.task.scopeNew`).
    ScopeNew,
    /// Starts a task of the scope that calls the function value, counted
    /// towards the limit unless the third operand is nonzero.
    ScopeStart,
    /// The next task of the scope to finish: its index times 4 plus how it
    /// finished, or -1 once every task was given.
    ScopeNext,
    /// The result of a task that returned, by its index.
    ScopeResult,
    ScopeCancel,
    ScopeEnd,
    /// A new `ext` holding the value, an `Ext[T]` (Specification §9.6).
    ExtNew,
    /// Takes the lock of the `ext`, suspending while another task holds
    /// it, and opens a region where cancellation waits.
    ExtLock,
    /// Gives the lock up and closes the region.
    ExtUnlock,
    /// The value of the `ext`, borrowed from it, which only its lock's
    /// holder reads.
    ExtValue,
    /// Places the value in the `ext`, giving up the one it held.
    ExtStore,
    /// A lazy value computed by the function value, a `Lazy[T]` (§6.10).
    LazyNew,
    /// Reads the lazy value: 0 when it is there for `LazyValue`, 1 when
    /// the reader must compute it with `LazyCode` and store it with
    /// `LazySet`, or 2 when its computation trapped, for `LazyTrap`.
    LazyGet,
    /// The value the last `LazyGet` of the code read, with references of
    /// its own.
    LazyValue,
    /// The function value that computes the lazy value, borrowed from it.
    LazyCode,
    /// Stores the computed value in the lazy value, which takes references
    /// of its own.
    LazySet,
    /// Traps as the computation that the last `LazyGet` found did; it does
    /// not return.
    LazyTrap,
    /// A stream of values of the type with a buffer of the capacity, an
    /// `Int`: its sink, a `RuntimeStream` (§10.5); `StreamPeer` gives the
    /// source.
    StreamNew {
        value: Ty<'db>,
    },
    /// The source of the stream the last `StreamNew` of the code made.
    StreamPeer,
    /// Puts the value, suspending while the buffer is full, or without
    /// waiting when `wait` is false: 0 once sent, else 1 for a full buffer
    /// or 2 and 3 for a closed or abandoned stream.
    StreamPut {
        wait: bool,
    },
    /// Takes the next value, suspending while there is none: 0 when there
    /// is one for `StreamValue`, else 2 or 3 as for `StreamPut`.
    StreamNext,
    /// The value the last `StreamNext` of the code took, with its
    /// references.
    StreamValue,
    StreamClose,
    /// A hub of values of the type, a fan-out for kind 0 and a broadcast
    /// for 1, with the capacity: a `RuntimeHub` (§10.6).
    HubNew {
        value: Ty<'db>,
    },
    /// A new end of the hub, a `RuntimeStream`: a sink or a source.
    HubSink,
    HubSource,
    HubSeal,
    /// Makes that many consumers of a fan-out read `Closed`.
    HubRelease,
    /// `std.io`'s sockets: a descriptor, or minus the error number, for
    /// `IoListen`, `IoAccept` and `IoSocket`.
    IoListen,
    IoAccept,
    IoSocket,
    /// The box of a `RuntimeSocket` for a descriptor.
    IoOwn,
    IoPort,
    /// Connects the socket to a port: 0, or the error number.
    IoConnect,
    /// Reads at most the count: how many were read, with their bytes for
    /// `IoReadBytes`, 0 at the end, or minus the error number.
    IoRead,
    IoReadBytes,
    /// Writes the last bytes the count says, all for -1: how many are left
    /// afterwards, or minus the error number.
    IoWrite,
    /// Prints a string, with a newline for 1: 0, or the error number.
    IoPrint,
    /// Traps with `Fault`: the environment failed (§15.6).
    IoFault,
    /// Reads the file a string names: 0, with its bytes for
    /// `IoReadBytes`, or the error number.
    IoReadFile,
    /// A socket for `IoConnectHost`: a descriptor, or minus the error
    /// number.
    IoSocketAny,
    /// Connects the socket to a host by name and a port: 0, the error
    /// number, or `crag_abi::UNKNOWN_HOST`.
    IoConnectHost,
    /// Whether bytes are UTF-8: 1 or 0.
    TextUtf8,
    /// The same text as another type: bytes as a string.
    TextCast,
    /// The text functions of the runtime (`crag_abi::text_op`): a count,
    /// what is at an offset, a search, a new string, the bytes between two
    /// offsets, a code point's property or mapping, and a number parsed,
    /// whose value waits for `TextParsed`.
    TextMeasure(u8),
    TextAt(u8),
    TextFind(u8),
    TextMap(u8),
    TextSlice,
    CodePointOp(u8),
    TextParse(u8),
    TextParsed,
    /// The same word as another one-word type: a code point's value.
    Word,
    /// The list with the element after its last, which it consumes.
    ListAppend,
    /// Traps with the kind, a `crag_abi::TrapKind` by its number.
    TrapWith(u8),
    /// Records a failed assertion of a test: its message and the byte
    /// offset of the assertion (§19.12).
    TestFailure,
    /// The byte offset of the expression in its module, an `Int`.
    Site(ExprId),
    /// A number read from bytes: whether it fits, with its word for
    /// `TextParsed`; new bytes with a number written; the bytes of a list
    /// of `UInt8`s.
    BytesRead,
    BytesWrite,
    BytesOfList,
    /// The program's arguments as a list of bytes; whether an environment
    /// variable is set, with its bytes for `IoReadBytes`; the variables as
    /// a map; the system or the processor by its code.
    EnvArgs,
    EnvVar,
    EnvVars,
    EnvPlatform,
    /// The number of elements of a list, map or set.
    CollCount,
    /// The list with an element replaced, which consumes the list and the
    /// value; two lists joined; the elements but the first and last
    /// counts given.
    ListSet,
    ListConcat,
    ListSlice,
    /// The map with a key bound, which consumes the map, the key and the
    /// value; the set with a key, which consumes both; either without a
    /// key, which consumes the collection.
    MapInsert,
    SetInsert,
    MapRemove,
    /// Whether a set has the key: 1 or 0.
    SetContains,
    /// The keys of a map or set, or the values of a map, as a list.
    MapKeys,
    MapValues,
    /// Equality, order or hash of values of the type by its shape
    /// (`crag_abi::value_op`), and a value written as source.
    ValueOp {
        op: u8,
        ty: Ty<'db>,
    },
    ValueShow {
        ty: Ty<'db>,
    },
    /// Emits the signal (§11.2), with the qualifier of
    /// `crag_abi::SIGNAL_PLAIN` to `SIGNAL_RETRY`: held in a block, else
    /// delivered at once.
    SignalEmit {
        qualifier: u8,
    },
    /// Delivers the signals an outcome of a block made deliverable.
    SignalDrain,
    /// The mark of a block's handlers, an `Int`.
    SignalMark,
    /// Registers the function value as a handler of the block with the
    /// mark (§11.3).
    SignalOn,
    /// Forgets the handlers since the mark; the function values after it,
    /// those handlers, stay live until then.
    SignalReset,
}

impl Intrinsic<'_> {
    /// Whether the operation consumes its operand at `index`.
    pub fn consumes(self, index: usize) -> bool {
        match self {
            Intrinsic::RefCommit => index == 2,
            Intrinsic::RefSwap | Intrinsic::ScopeStart | Intrinsic::ExtStore => index == 1,
            Intrinsic::ListAppend => index <= 1,
            Intrinsic::ListSet => index == 0 || index == 2,
            Intrinsic::MapInsert => index <= 2,
            Intrinsic::SetInsert => index <= 1,
            Intrinsic::MapRemove => index == 0,
            Intrinsic::RefNew
            | Intrinsic::ExtNew
            | Intrinsic::LazyNew
            | Intrinsic::SignalEmit { .. } => index == 0,
            _ => false,
        }
    }
}

/// Where a closure's environment lives, by its escape level (§11.5.8).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum ClosurePlacement {
    /// In the frame's part of the side stack, uncounted, for a closure
    /// that does not outlive the frame.
    SideStack,
    /// In a counted box.
    Heap,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Statement<'db> {
    /// The local must not occur in the rvalue.
    Assign(Local, Rvalue<'db>),
    /// Adds a reference to the value of a counted local.
    Retain(Local),
    /// Gives up the local's reference, freeing the value with the last.
    Release(Local),
    /// A point on a loop's back-edge where the runtime may stop the fiber.
    Poll,
    /// The start of a statement, where the debugger may stop the task
    /// (Implementation Plan §11.8.6): the expression it begins with, and
    /// the named locals that hold values there. It uses none of them, so
    /// it never keeps a value alive; liveness leaves only those that are.
    Step {
        at: Option<ExprId>,
        locals: Vec<Local>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum TrapKind {
    Overflow,
    DivideByZero,
    /// An index outside the list.
    Index,
    /// `???` (§6.11).
    Hole,
    /// No arm of a `case` matched, which checking rules out.
    NoMatch,
    /// The body has errors, reported where it was checked.
    Error,
    /// Something the builder does not lower yet.
    Unsupported,
    /// `!!` met an error (§8.4).
    Expectation,
    /// The trap a handler took, raised again for the handlers around it
    /// (§8.3.1).
    Rethrow,
    /// A value failed a condition of its type (§3.10.1).
    ConditionFailed,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Terminator<'db> {
    Jump(BlockId),
    /// Goes to `then` if the `Bool` is `True`.
    Branch {
        cond: Operand<'db>,
        then: BlockId,
        otherwise: BlockId,
    },
    /// Goes to the first case whose type the value at the place has.
    Switch {
        place: Place<'db>,
        cases: Vec<(Ty<'db>, BlockId)>,
        otherwise: BlockId,
    },
    /// Calls a function and continues at `target` with its result in
    /// `dst`, or at `unwind`, without one, when the code it called left
    /// the attempt of the transaction of an `atomic` block around the call
    /// (Plan §11.7.14).
    Call {
        func: InstanceKey<'db>,
        args: Vec<Operand<'db>>,
        dst: Local,
        target: BlockId,
        site: ExprId,
        unwind: Option<BlockId>,
        /// Where a trap in the code it called continues: the handler of
        /// a trap handler around the call (§8.3.1).
        catch: Option<BlockId>,
    },
    /// A call that replaces this function's frame (§5.6.3).
    TailCall {
        func: InstanceKey<'db>,
        args: Vec<Operand<'db>>,
        site: ExprId,
    },
    /// A call of a function value, which goes with its environment, before
    /// the arguments, to its code.
    CallValue {
        callee: Operand<'db>,
        args: Vec<Operand<'db>>,
        dst: Local,
        target: BlockId,
        site: ExprId,
        unwind: Option<BlockId>,
        catch: Option<BlockId>,
    },
    TailCallValue {
        callee: Operand<'db>,
        args: Vec<Operand<'db>>,
        site: ExprId,
    },
    Return(Operand<'db>),
    Trap {
        kind: TrapKind,
        site: Option<ExprId>,
        /// What the trap names beyond its kind, such as the type of the
        /// error `!!` met (§8.3).
        detail: Option<String>,
        /// The handler of a trap handler of this function that takes it
        /// (§8.3.1).
        catch: Option<BlockId>,
    },
}

impl<'db> Terminator<'db> {
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Terminator::Jump(b) => vec![*b],
            Terminator::Branch {
                then, otherwise, ..
            } => vec![*then, *otherwise],
            Terminator::Switch {
                cases, otherwise, ..
            } => cases.iter().map(|(_, b)| *b).chain([*otherwise]).collect(),
            Terminator::Call {
                target,
                unwind,
                catch,
                ..
            }
            | Terminator::CallValue {
                target,
                unwind,
                catch,
                ..
            } => [*target].into_iter().chain(*unwind).chain(*catch).collect(),
            Terminator::Trap { catch, .. } => catch.iter().copied().collect(),
            Terminator::TailCall { .. }
            | Terminator::TailCallValue { .. }
            | Terminator::Return(_) => Vec::new(),
        }
    }

    pub fn successors_mut(&mut self) -> Vec<&mut BlockId> {
        match self {
            Terminator::Jump(b) => vec![b],
            Terminator::Branch {
                then, otherwise, ..
            } => vec![then, otherwise],
            Terminator::Switch {
                cases, otherwise, ..
            } => cases
                .iter_mut()
                .map(|(_, b)| b)
                .chain([otherwise])
                .collect(),
            Terminator::Call {
                target,
                unwind,
                catch,
                ..
            }
            | Terminator::CallValue {
                target,
                unwind,
                catch,
                ..
            } => [target]
                .into_iter()
                .chain(unwind.as_mut())
                .chain(catch.as_mut())
                .collect(),
            Terminator::Trap { catch, .. } => catch.as_mut().into_iter().collect(),
            Terminator::TailCall { .. }
            | Terminator::TailCallValue { .. }
            | Terminator::Return(_) => Vec::new(),
        }
    }
}

impl Operand<'_> {
    fn locals_mut(&mut self) -> Option<&mut Local> {
        match self {
            Operand::Local(l) => Some(l),
            Operand::Const(_) => None,
        }
    }
}

impl<'db> Rvalue<'db> {
    /// Every local the rvalue mentions.
    pub fn locals_mut(&mut self) -> Vec<&mut Local> {
        let mut out = Vec::new();
        match self {
            Rvalue::Use(o)
            | Rvalue::Convert(o)
            | Rvalue::FnValue { env: o, .. }
            | Rvalue::Cast { value: o, .. } => out.extend(o.locals_mut()),
            Rvalue::Read(p) | Rvalue::Len(p) | Rvalue::Slice { list: p, .. } => {
                out.push(&mut p.local)
            }
            Rvalue::Binary { a, b, .. }
            | Rvalue::Overflows { a, b, .. }
            | Rvalue::Compare { a, b, .. } => {
                out.extend(a.locals_mut());
                out.extend(b.locals_mut());
            }
            Rvalue::FloatOverflow(locals) => out.extend(locals.iter_mut()),
            Rvalue::Record { fields, .. } => {
                out.extend(fields.iter_mut().filter_map(|(_, o)| o.locals_mut()))
            }
            Rvalue::List(items) | Rvalue::Concat(items) | Rvalue::Intrinsic(_, items) => {
                out.extend(items.iter_mut().filter_map(Operand::locals_mut))
            }
            Rvalue::Map(entries) => {
                for (k, v) in entries {
                    out.extend(k.locals_mut());
                    out.extend(v.locals_mut());
                }
            }
            Rvalue::Index { list: p, index: o } | Rvalue::MapGet { map: p, key: o, .. } => {
                out.push(&mut p.local);
                out.extend(o.locals_mut());
            }
            Rvalue::Closure { captures, .. } => {
                out.extend(captures.iter_mut().filter_map(Operand::locals_mut))
            }
        }
        out
    }
}

impl<'db> Statement<'db> {
    /// Every local the statement mentions.
    pub fn locals_mut(&mut self) -> Vec<&mut Local> {
        match self {
            Statement::Assign(l, rvalue) => {
                let mut out = vec![l];
                out.extend(rvalue.locals_mut());
                out
            }
            Statement::Retain(l) | Statement::Release(l) => vec![l],
            Statement::Poll => Vec::new(),
            Statement::Step { locals, .. } => locals.iter_mut().collect(),
        }
    }
}

impl<'db> Terminator<'db> {
    /// Every local the terminator mentions.
    pub fn locals_mut(&mut self) -> Vec<&mut Local> {
        match self {
            Terminator::Branch { cond: o, .. } | Terminator::Return(o) => {
                o.locals_mut().into_iter().collect()
            }
            Terminator::Switch { place, .. } => vec![&mut place.local],
            Terminator::Call { args, dst, .. } => {
                let mut out: Vec<&mut Local> =
                    args.iter_mut().filter_map(Operand::locals_mut).collect();
                out.push(dst);
                out
            }
            Terminator::TailCall { args, .. } => {
                args.iter_mut().filter_map(Operand::locals_mut).collect()
            }
            Terminator::CallValue {
                callee, args, dst, ..
            } => {
                let mut out: Vec<&mut Local> = callee.locals_mut().into_iter().collect();
                out.extend(args.iter_mut().filter_map(Operand::locals_mut));
                out.push(dst);
                out
            }
            Terminator::TailCallValue { callee, args, .. } => {
                let mut out: Vec<&mut Local> = callee.locals_mut().into_iter().collect();
                out.extend(args.iter_mut().filter_map(Operand::locals_mut));
                out
            }
            Terminator::Jump(_) | Terminator::Trap { .. } => Vec::new(),
        }
    }
}

impl<'db> MirBody<'db> {
    /// The instances the body needs code of: those it calls, and the code
    /// of the function values it makes, in the order they occur.
    pub fn callees(&self) -> Vec<InstanceKey<'db>> {
        let mut out = Vec::new();
        for block in &self.blocks {
            for statement in &block.statements {
                if let Statement::Assign(
                    _,
                    Rvalue::Closure { code, .. }
                    | Rvalue::FnValue { code, .. }
                    | Rvalue::Record {
                        dispose: Some(code),
                        ..
                    },
                ) = statement
                {
                    out.push(*code);
                }
            }
            if let Terminator::Call { func, .. } | Terminator::TailCall { func, .. } =
                &block.terminator
            {
                out.push(*func);
            }
        }
        let mut seen = Vec::new();
        out.retain(|k| {
            !seen.contains(k) && {
                seen.push(*k);
                true
            }
        });
        out
    }

    /// The body as text, one statement per line, for tests and debugging.
    pub fn pretty(&self, db: &'db dyn Db) -> String {
        let mut out = String::new();
        for (i, local) in self.locals.iter().enumerate() {
            let kind = if i < self.params { "param" } else { "let" };
            let name = match local.binding {
                Some((_, name)) => format!(" ({})", name.text(db)),
                None => String::new(),
            };
            out += &format!("{kind} _{i}: {}{name}\n", local.ty.display(db));
        }
        for (i, block) in self.blocks.iter().enumerate() {
            out += &format!("bb{i}:\n");
            for statement in &block.statements {
                out += &format!("  {}\n", statement_text(db, statement));
            }
            out += &format!("  {}\n", terminator_text(db, &block.terminator));
        }
        out
    }
}

fn statement_text<'db>(db: &'db dyn Db, statement: &Statement<'db>) -> String {
    match statement {
        Statement::Assign(local, rvalue) => {
            format!("_{} = {}", local.0, rvalue_text(db, rvalue))
        }
        Statement::Retain(local) => format!("retain _{}", local.0),
        Statement::Release(local) => format!("release _{}", local.0),
        Statement::Poll => "poll".into(),
        Statement::Step { at, locals } => {
            let locals: Vec<String> = locals.iter().map(|l| format!("_{}", l.0)).collect();
            match at {
                Some(at) => format!("step e{} [{}]", at.0, locals.join(", ")),
                None => format!("step [{}]", locals.join(", ")),
            }
        }
    }
}

fn rvalue_text<'db>(db: &'db dyn Db, rvalue: &Rvalue<'db>) -> String {
    let op = |o: &Operand<'db>| operand_text(db, o);
    let ops = |os: &[Operand<'db>]| os.iter().map(op).collect::<Vec<_>>().join(", ");
    let place = |p: &Place<'db>| place_text(db, p);
    match rvalue {
        Rvalue::Use(o) => op(o),
        Rvalue::Read(p) => place(p),
        Rvalue::Convert(o) => format!("convert {}", op(o)),
        Rvalue::Cast {
            op: cast,
            from,
            value,
        } => format!("{}.{cast:?}({})", ty_name(*from), op(value)),
        Rvalue::Binary {
            op: bin,
            ty,
            a,
            b,
            check,
        } => {
            let checked = if check.is_some() { "checked " } else { "" };
            format!(
                "{checked}{}.{}({}, {})",
                ty_name(*ty),
                bin_name(*bin),
                op(a),
                op(b)
            )
        }
        Rvalue::Overflows { op: bin, ty, a, b } => format!(
            "overflows {}.{}({}, {})",
            ty_name(*ty),
            bin_name(*bin),
            op(a),
            op(b)
        ),
        Rvalue::FloatOverflow(locals) => format!(
            "overflowed({})",
            locals
                .iter()
                .map(|l| format!("_{}", l.0))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Rvalue::Compare { op: cmp, ty, a, b } => {
            let name = match cmp {
                CmpOp::Eq => "eq",
                CmpOp::Ne => "ne",
                CmpOp::Lt => "lt",
                CmpOp::Le => "le",
                CmpOp::Gt => "gt",
                CmpOp::Ge => "ge",
            };
            format!("{}.{name}({}, {})", ty_name(*ty), op(a), op(b))
        }
        Rvalue::Record {
            ty,
            fields,
            dispose,
        } => {
            let fields: Vec<String> = fields
                .iter()
                .map(|(n, o)| format!("{}: {}", n.text(db), op(o)))
                .collect();
            let name = match ty.kind(db) {
                TyKind::Record { .. } => String::new(),
                _ => ty.display(db),
            };
            let dispose = match dispose {
                Some(code) => format!(" disposed by {}", func_name(db, *code)),
                None => String::new(),
            };
            format!("{name}({}){dispose}", fields.join(", "))
        }
        Rvalue::List(items) => format!("[{}]", ops(items)),
        Rvalue::Map(entries) if entries.is_empty() => "[:]".into(),
        Rvalue::Map(entries) => format!(
            "[{}]",
            entries
                .iter()
                .map(|(k, v)| format!("{}: {}", op(k), op(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Rvalue::Concat(parts) => format!("concat({})", ops(parts)),
        Rvalue::Intrinsic(intrinsic, args) => format!("{intrinsic:?}({})", ops(args)),
        Rvalue::Len(p) => format!("len {}", place(p)),
        Rvalue::Index { list, index } => format!("{}[{}]", place(list), op(index)),
        Rvalue::MapGet { map, key, .. } => format!("get {}[{}]", place(map), op(key)),
        Rvalue::Slice { list, front, back } => {
            format!("slice {}[{front}..-{back}]", place(list))
        }
        Rvalue::Closure {
            code,
            captures,
            placement,
            ..
        } => {
            let place = match placement {
                ClosurePlacement::SideStack => "side",
                ClosurePlacement::Heap => "heap",
            };
            format!(
                "closure {} {place}({})",
                func_name(db, *code),
                ops(captures)
            )
        }
        Rvalue::FnValue { code, env } => {
            format!("closure {} with {}", func_name(db, *code), op(env))
        }
    }
}

fn terminator_text<'db>(db: &'db dyn Db, terminator: &Terminator<'db>) -> String {
    let op = |o: &Operand<'db>| operand_text(db, o);
    let ops = |os: &[Operand<'db>]| os.iter().map(op).collect::<Vec<_>>().join(", ");
    match terminator {
        Terminator::Jump(b) => format!("jump bb{}", b.0),
        Terminator::Branch {
            cond,
            then,
            otherwise,
        } => format!("branch {} bb{} bb{}", op(cond), then.0, otherwise.0),
        Terminator::Switch {
            place,
            cases,
            otherwise,
        } => format!(
            "switch {} [{}] else bb{}",
            place_text(db, place),
            cases
                .iter()
                .map(|(t, b)| format!("{}: bb{}", t.display(db), b.0))
                .collect::<Vec<_>>()
                .join(", "),
            otherwise.0
        ),
        Terminator::Call {
            func,
            args,
            dst,
            target,
            unwind,
            ..
        } => format!(
            "_{} = call {}({}) -> bb{}{}",
            dst.0,
            func_name(db, *func),
            ops(args),
            target.0,
            unwind.map_or(String::new(), |u| format!(", unwind bb{}", u.0))
        ),
        Terminator::TailCall { func, args, .. } => {
            format!("tail call {}({})", func_name(db, *func), ops(args))
        }
        Terminator::CallValue {
            callee,
            args,
            dst,
            target,
            unwind,
            ..
        } => format!(
            "_{} = call value {}({}) -> bb{}{}",
            dst.0,
            op(callee),
            ops(args),
            target.0,
            unwind.map_or(String::new(), |u| format!(", unwind bb{}", u.0))
        ),
        Terminator::TailCallValue { callee, args, .. } => {
            format!("tail call value {}({})", op(callee), ops(args))
        }
        Terminator::Return(o) => format!("return {}", op(o)),
        Terminator::Trap { kind, .. } => {
            let kind = match kind {
                TrapKind::Overflow => "overflow",
                TrapKind::DivideByZero => "divide by zero",
                TrapKind::Index => "index",
                TrapKind::Hole => "hole",
                TrapKind::NoMatch => "no match",
                TrapKind::Error => "error",
                TrapKind::Unsupported => "unsupported",
                TrapKind::Expectation => "expectation",
                TrapKind::Rethrow => "rethrow",
                TrapKind::ConditionFailed => "condition failed",
            };
            format!("trap {kind}")
        }
    }
}

fn func_name<'db>(db: &'db dyn Db, func: InstanceKey<'db>) -> String {
    let mut owner = match func.owner(db) {
        Owner::Item(item) => item.name(db).text(db).clone(),
        Owner::Test(test) => format!("test {}", test.label(db)),
    };
    if !func.args(db).is_empty() {
        let args: Vec<String> = func.args(db).iter().map(|t| t.display(db)).collect();
        owner += &format!("[{}]", args.join(", "));
    }
    match *func.entry(db) {
        Entry::Body => owner,
        Entry::Closure(e) | Entry::Function(e) => format!("{owner}#{}", e.index()),
        Entry::Default(e) => format!("{owner}#default{}", e.index()),
        Entry::Dispose => format!("{owner}#dispose"),
        Entry::Part => format!("{owner}#part"),
        Entry::Check => format!("{owner}#check"),
    }
}

fn operand_text<'db>(db: &'db dyn Db, operand: &Operand<'db>) -> String {
    match operand {
        Operand::Local(l) => format!("_{}", l.0),
        Operand::Const(c) => match c {
            Constant::Int(n) => n.to_string(),
            Constant::Float(bits) => format!("{:?}", f64::from_bits(*bits)),
            Constant::Str(s) => format!("{s:?}"),
            Constant::Bytes(b) => format!("b{:?}", String::from_utf8_lossy(b)),
            Constant::Tag(ty) => ty.display(db),
            Constant::Unit => "()".into(),
        },
    }
}

fn place_text<'db>(db: &'db dyn Db, place: &Place<'db>) -> String {
    let mut text = format!("_{}", place.local.0);
    for step in &place.path {
        match step {
            Step::As(ty) => text = format!("({text} as {})", ty.display(db)),
            Step::Field(name) => text += &format!(".{}", name.text(db)),
            Step::Elem(i) => text += &format!("[{i}]"),
            Step::ElemBack(i) => text += &format!("[-{}]", i + 1),
            Step::Slice { front, back } => text += &format!("[{front}..-{back}]"),
        }
    }
    text
}

fn ty_name(ty: Builtin) -> String {
    match ty {
        Builtin::Fixed(scale) => format!("Fixed[{scale}]"),
        b => b.name().into(),
    }
}

fn bin_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::Rem => "rem",
    }
}
