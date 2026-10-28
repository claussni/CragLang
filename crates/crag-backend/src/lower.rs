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

//! MIR to LIR: one case per statement and terminator.
//!
//! Every local becomes as many registers as its layout has words. Numbers
//! are words; narrow integers are kept sign- or zero-extended to 64 bits,
//! and a `Float` is a word holding its bits. A `Bool` is the type index of
//! `True` or `False`, so a branch compares it with `True`'s. Boxes are
//! allocated and counted inline, and the runtime frees them. An empty list
//! or map is allocated inline too; the runtime grows it and finds its
//! elements.
//!
//! A function value is the address of its code and its environment. The
//! code takes the environment before the arguments, and a call goes
//! through the address. An environment is a box on the heap, or on the
//! side stack with a static count, so that counting it does nothing.
//!
//! A string or bytes value is its bytes inline, up to 15 of them, or a
//! buffer and where its bytes are in it (see `crag_abi`). A longer literal
//! has a static buffer in the code object; the runtime joins, compares and
//! writes numbers as text, and counting a value counts its buffer.
//!
//! What code generation does not handle yet ends its block with a trap and
//! is listed.

use std::ops::Range;

use crag_abi::{
    BUFFER_HEADER, CELL_FULL, CELL_STATE_OFFSET, CELL_VALUE_OFFSET, COUNT_OFFSET,
    FUNCTION_BOX_HEADER, HEADER_SIZE, HEAP_OFFSET, HandlerKind, INLINE_TEXT_MAX, LEN_OFFSET,
    LIST_SIZE, MAP_SIZE, MEMBER_BOX_SIZE, NO_POSITION, PAGE_FREE_OFFSET, PAGE_USED_OFFSET, REF_ADD,
    REF_CELL_SIZE, REF_MUL, REF_SUB, REF_UNSIGNED, SCOPE_DONE, SIDE_END_OFFSET, SIDE_PTR_OFFSET,
    SIGNAL_NONE, START_EXEMPT, STATIC_COUNT, TEXT_BOX_HEADER, TEXT_LEN_MAX, TX_CONFLICT_OFFSET,
    TYPE_INDEX_OFFSET, TrapKind as AbiTrap, TrapOrigin, TypeDescriptor, inline_text, size_class,
};
use crag_codegen::{
    BinOp as LirBin, Block as LirBlock, BlockId as LirBlockId, CallTarget, Cond, FuncId, Inst,
    LirFunction, OverflowOp, RuntimeFn, SlotKey, Term, UnOp, VReg,
};
use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{Name, Owner, Program, hir_body, lower_body};
use crag_mir::{
    BinOp, BlockId, CastOp, ClosurePlacement, CmpOp, Constant, Entry, InstanceKey, Intrinsic,
    Local, MirBody, Operand, Place, Rvalue, Statement, Terminator, TrapKind,
};
use crag_types::{Builtin, Step, Ty, TyKind, prelude_item, signature};

use crate::layout::{
    Layout, boxed_indices, deferred, dispose_word, equal_by_words, layout, record_layout,
    signal_types, subtypes, type_descriptor, type_index,
};
use crate::slot_key;

/// The LIR of a body, with what it could not lower.
pub struct Lowered<'db> {
    pub lir: LirFunction,
    pub unsupported: Vec<&'static str>,
    /// The functions it calls.
    pub calls: Vec<InstanceKey<'db>>,
    /// The types of the boxes it allocates, by type index, with their
    /// descriptors.
    pub types: Vec<(u32, TypeDescriptor)>,
    /// Its steps, by index (Implementation Plan §11.8.6).
    pub steps: Vec<StepInfo<'db>>,
    /// The module of its code, where the positions of its traps lie, and
    /// what they name (Specification §8.3).
    pub module: String,
    pub origins: Vec<TrapOrigin>,
    pub details: Vec<String>,
}

/// A statement's step, for the debugger: where the statement starts and
/// the named locals whose words `rt_step` gets, in order.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct StepInfo<'db> {
    pub position: Option<u32>,
    pub locals: Vec<(Name<'db>, Ty<'db>)>,
}

/// The function an instance is loaded as.
pub fn func_id(instance: InstanceKey<'_>) -> FuncId {
    FuncId(instance.as_id().index())
}

type Unsupported = &'static str;

/// Lowers the MIR of a body of `owner`, loaded as `func`, whose source map
/// gives the positions of traps and steps. The code of a module-level
/// value keeps the value in `cell` (§11.6.2).
pub fn lower_to_lir<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    func: FuncId,
    mir: &MirBody<'db>,
    cell: Option<SlotKey>,
) -> Lowered<'db> {
    let named = |name: &str| {
        prelude_item(db, program, name).map(|i| Ty::new(db, TyKind::Named(i, Vec::new())))
    };
    let mut l = Lower {
        db,
        program,
        mir,
        positions: &lower_body(db, program, owner).source_map.exprs,
        vregs: 0,
        locals: Vec::new(),
        layouts: Vec::new(),
        blocks: vec![None; mir.blocks.len()],
        current: (0, Vec::new()),
        unsupported: Vec::new(),
        calls: Vec::new(),
        types: Vec::new(),
        tracked: Vec::new(),
        data: Vec::new(),
        true_index: named("True").map_or(-1, type_index),
        false_index: named("False").map_or(-1, type_index),
        cell,
        scratch: None,
        func,
        steps: Vec::new(),
        source: owner.module(db).file(db).text(db),
        origins: Vec::new(),
        details: Vec::new(),
    };
    for (i, decl) in mir.locals.iter().enumerate() {
        let layout = layout(db, program, decl.ty);
        let mut words = layout.map_or(0, Layout::words);
        // An environment is passed as a word even when it holds nothing.
        if i == 0 && mir.env {
            words = words.max(1);
        }
        let regs: Vec<VReg> = (0..words).map(|_| l.reg()).collect();
        match layout {
            Some(Layout::Box) => l.tracked.extend(&regs),
            Some(Layout::Closure) => l.tracked.push(regs[1]),
            Some(Layout::Pair) => l.tracked.push(regs[0]),
            _ => {}
        }
        l.locals.push(regs);
        l.layouts.push(layout);
    }
    let params: usize = l.locals[..mir.params].iter().map(Vec::len).sum();
    let returns = layout(db, program, mir.result).map_or(0, Layout::words);
    let unknown_param = l.layouts[..mir.params].iter().any(Option::is_none);
    for (b, block) in mir.blocks.iter().enumerate() {
        l.current = (b, Vec::new());
        if unknown_param || returns > 2 {
            l.unsupported("types of parameters or results");
            continue;
        }
        let lowered = block
            .statements
            .iter()
            .try_for_each(|s| l.statement(s))
            .and_then(|()| l.terminator(&block.terminator, returns));
        if let Err(what) = lowered {
            l.unsupported(what);
        }
    }
    // MIR's entry block is no branch target, so the scratch words are
    // pushed once.
    if let (Some(dst), Some(entry)) = (l.scratch, l.blocks[0].as_mut()) {
        entry.insts.insert(
            0,
            Inst::SidePush {
                dst,
                size: 32,
                align: 8,
            },
        );
    }
    if let Some(cell) = cell
        && !unknown_param
        && returns <= 2
    {
        l.cell_entry(cell, returns);
    }
    // A block a failed lowering left unfinished is never reached.
    let blocks = l
        .blocks
        .into_iter()
        .map(|b| {
            b.unwrap_or(LirBlock {
                insts: Vec::new(),
                term: Term::Trap {
                    kind: AbiTrap::Unsupported,
                    position: None,
                },
            })
        })
        .collect();
    Lowered {
        lir: LirFunction {
            params: params as u32,
            returns: returns as u32,
            vregs: l.vregs,
            tracked: l.tracked,
            blocks,
            data: l.data,
        },
        unsupported: l.unsupported,
        calls: l.calls,
        types: l.types,
        steps: l.steps,
        module: owner.module(db).path(db).clone(),
        origins: {
            let mut origins = l.origins;
            origins.sort_by_key(|o| o.position);
            origins.dedup();
            origins
        },
        details: l.details,
    }
}

/// The handlers of a call: for leaving a transaction's attempt, and for a
/// trap (Specification §8.3.1).
fn handlers(unwind: &Option<BlockId>, catch: &Option<BlockId>) -> Vec<(HandlerKind, LirBlockId)> {
    let block = |b: &BlockId| LirBlockId(b.0);
    unwind
        .iter()
        .map(|b| (HandlerKind::Transaction, block(b)))
        .chain(catch.iter().map(|b| (HandlerKind::Trap, block(b))))
        .collect()
}

struct Lower<'a, 'db> {
    db: &'db dyn Db,
    program: Program,
    mir: &'a MirBody<'db>,
    /// Where each expression of the body is in its module's source.
    positions: &'db [Range<u32>],
    vregs: u32,
    /// The registers of each local.
    locals: Vec<Vec<VReg>>,
    layouts: Vec<Option<Layout>>,
    /// MIR block `i` is LIR block `i`; tests add more.
    blocks: Vec<Option<LirBlock>>,
    current: (usize, Vec<Inst>),
    unsupported: Vec<Unsupported>,
    calls: Vec<InstanceKey<'db>>,
    /// The types it allocates, with their descriptors.
    types: Vec<(u32, TypeDescriptor)>,
    tracked: Vec<VReg>,
    /// The static data of the code: the buffers of long literals.
    data: Vec<Vec<u8>>,
    true_index: i64,
    false_index: i64,
    /// The cell of the value the code computes, if it is a value's.
    cell: Option<SlotKey>,
    /// The source of the module, for the origins of traps.
    source: &'db str,
    origins: Vec<TrapOrigin>,
    details: Vec<String>,
    /// Three words on the side stack that the runtime's reads put what they
    /// read in, pushed at the entry once the code reads anything.
    scratch: Option<VReg>,
    /// The function the code is loaded as, and its steps so far.
    func: FuncId,
    steps: Vec<StepInfo<'db>>,
}

impl<'a, 'db> Lower<'a, 'db> {
    fn reg(&mut self) -> VReg {
        self.vregs += 1;
        VReg(self.vregs - 1)
    }

    fn push(&mut self, inst: Inst) {
        self.current.1.push(inst);
    }

    /// The line and column, from one, of a byte offset in the module, the
    /// column counted in characters.
    fn origin(&self, at: u32) -> TrapOrigin {
        let before = &self.source[..(at as usize).min(self.source.len())];
        let line = before.matches('\n').count() as u32 + 1;
        let start = before.rfind('\n').map_or(0, |i| i + 1);
        let column = before[start..].chars().count() as u32 + 1;
        TrapOrigin {
            position: at,
            line,
            column,
        }
    }

    fn new_block(&mut self) -> LirBlockId {
        self.blocks.push(None);
        LirBlockId(self.blocks.len() as u32 - 1)
    }

    /// Ends the current block; what follows goes to `next`.
    fn end(&mut self, term: Term, next: Option<LirBlockId>) {
        let (b, insts) = std::mem::take(&mut self.current);
        self.blocks[b] = Some(LirBlock { insts, term });
        if let Some(next) = next {
            self.current = (next.0 as usize, Vec::new());
        }
    }

    fn unsupported(&mut self, what: Unsupported) {
        if !self.unsupported.contains(&what) {
            self.unsupported.push(what);
        }
        let term = Term::Trap {
            kind: AbiTrap::Unsupported,
            position: None,
        };
        self.end(term, None);
    }

    fn constant(&mut self, value: i64) -> VReg {
        let dst = self.reg();
        self.push(Inst::Const { dst, value });
        dst
    }

    fn bin(&mut self, op: LirBin, a: VReg, b: VReg) -> VReg {
        let dst = self.reg();
        self.push(Inst::Bin { op, dst, a, b });
        dst
    }

    fn cmp(&mut self, cond: Cond, a: VReg, b: VReg) -> VReg {
        let dst = self.reg();
        self.push(Inst::Cmp { cond, dst, a, b });
        dst
    }

    fn layout_of(&self, ty: Ty<'db>) -> Result<Layout, Unsupported> {
        layout(self.db, self.program, ty).ok_or("values of this type")
    }

    fn local_ty(&self, local: Local) -> Ty<'db> {
        self.mir.locals[local.index()].ty
    }

    /// Copies values into a local's registers.
    fn assign(&mut self, local: Local, values: Vec<VReg>) -> Result<(), Unsupported> {
        let regs = self.locals[local.index()].clone();
        if regs.len() != values.len() {
            return Err("this conversion");
        }
        for (dst, src) in regs.into_iter().zip(values) {
            if dst != src {
                self.push(Inst::Move { dst, src });
            }
        }
        Ok(())
    }

    /// The words of an operand that goes where a `ty` is expected.
    fn operand(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        match op {
            Operand::Local(l) => {
                self.layouts[l.index()].ok_or("values of this type")?;
                Ok(self.locals[l.index()].clone())
            }
            Operand::Const(c) => self.constant_words(c, ty),
        }
    }

    fn constant_words(&mut self, c: &Constant<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        Ok(match c {
            Constant::Int(n) => vec![self.constant(*n as i64)],
            Constant::Float(bits) => vec![self.constant(*bits as i64)],
            Constant::Tag(_) | Constant::Unit => {
                if self.layout_of(ty)? != Layout::Zero {
                    return Err("this conversion");
                }
                Vec::new()
            }
            Constant::Str(s) => self.text_literal(s.as_bytes())?,
            Constant::Bytes(b) => self.text_literal(b)?,
        })
    }

    /// The words of a string or bytes literal: inline, or a static buffer
    /// in the code object, which counting leaves alone.
    fn text_literal(&mut self, bytes: &[u8]) -> Result<Vec<VReg>, Unsupported> {
        if bytes.len() <= INLINE_TEXT_MAX {
            let [w0, w1] = inline_text(bytes);
            return Ok(vec![self.constant(w0 as i64), self.constant(w1 as i64)]);
        }
        if bytes.len() as u64 > TEXT_LEN_MAX {
            return Err("literals of 4 GiB or more");
        }
        let mut buffer = Vec::with_capacity(16 + bytes.len());
        buffer.extend(STATIC_COUNT.to_le_bytes());
        buffer.extend(BUFFER_HEADER.to_le_bytes());
        buffer.extend(bytes);
        let data = match self.data.iter().position(|d| *d == buffer) {
            Some(d) => d,
            None => {
                self.data.push(buffer);
                self.data.len() - 1
            }
        };
        let ptr = self.reg();
        self.push(Inst::DataAddr {
            dst: ptr,
            data: data as u32,
        });
        Ok(vec![ptr, self.constant(bytes.len() as i64)])
    }

    /// The type of an operand.
    fn operand_ty(&self, op: &Operand<'db>, otherwise: Ty<'db>) -> Ty<'db> {
        match op {
            Operand::Local(l) => self.local_ty(*l),
            Operand::Const(Constant::Tag(ty)) => *ty,
            Operand::Const(Constant::Unit) => Ty::unit(self.db),
            Operand::Const(_) => otherwise,
        }
    }

    /// A `Bool` from a 0 or 1 word.
    fn bool_of(&mut self, flag: VReg) -> VReg {
        let t = self.constant(self.true_index);
        let f = self.constant(self.false_index);
        let dst = self.reg();
        self.push(Inst::Select {
            dst,
            cond: flag,
            a: t,
            b: f,
        });
        dst
    }

    // Statements.

    fn statement(&mut self, statement: &Statement<'db>) -> Result<(), Unsupported> {
        match statement {
            Statement::Assign(local, rvalue) => {
                let values = self.rvalue(*local, rvalue)?;
                self.assign(*local, values)
            }
            Statement::Retain(local) => self.count(*local, Self::retain),
            Statement::Release(local) => {
                // A long chain of boxes is freed between fibers (§13.5).
                let op = match deferred(self.db, self.program, self.local_ty(*local)) {
                    true => Self::release_deferred,
                    false => Self::release,
                };
                self.count(*local, op)
            }
            Statement::Poll => {
                self.push(Inst::Poll);
                Ok(())
            }
            Statement::Step { at, locals } => {
                let step = self.steps.len() as u32;
                let position = at
                    .and_then(|e| self.positions.get(e.index()))
                    .map(|r| r.start);
                let mut values = Vec::new();
                let mut named = Vec::new();
                for &local in locals {
                    let decl = &self.mir.locals[local.index()];
                    // A local without a layout has no words to show.
                    if let (Some((_, name)), Some(_)) = (decl.binding, self.layouts[local.index()])
                    {
                        values.extend(self.locals[local.index()].iter().copied());
                        named.push((name, decl.ty));
                    }
                }
                self.steps.push(StepInfo {
                    position,
                    locals: named,
                });
                self.push(Inst::Step {
                    func: self.func,
                    step,
                    values,
                });
                Ok(())
            }
        }
    }

    /// Retains or releases the box a local holds, if it holds one.
    fn count(&mut self, local: Local, op: fn(&mut Self, VReg)) -> Result<(), Unsupported> {
        let regs = self.locals[local.index()].clone();
        let (layout, ty) = (self.layouts[local.index()], self.local_ty(local));
        self.count_words(layout, ty, &regs, op)
    }

    /// Retains or releases the box the words of a value hold, if they hold
    /// one.
    fn count_words(
        &mut self,
        layout: Option<Layout>,
        ty: Ty<'db>,
        regs: &[VReg],
        op: fn(&mut Self, VReg),
    ) -> Result<(), Unsupported> {
        match layout {
            Some(Layout::Box) => {
                op(self, regs[0]);
                Ok(())
            }
            Some(Layout::Union) => {
                let boxed =
                    boxed_indices(self.db, self.program, ty).ok_or("values of this type")?;
                let boxed: Vec<i64> = boxed.into_iter().map(i64::from).collect();
                let (call, done) = (self.new_block(), self.new_block());
                self.test_index(regs[0], &boxed, call, done);
                self.current = (call.0 as usize, Vec::new());
                op(self, regs[1]);
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            // A function value without an environment has a null one.
            Some(Layout::Closure) => {
                let (call, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: regs[1],
                        then: call,
                        otherwise: done,
                    },
                    Some(call),
                );
                op(self, regs[1]);
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            // A buffer, unless the bytes are inline.
            Some(Layout::Pair) => {
                let one = self.constant(1);
                let inline = self.bin(LirBin::And, regs[0], one);
                let (call, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: inline,
                        then: done,
                        otherwise: call,
                    },
                    Some(call),
                );
                op(self, regs[0]);
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Adds a reference to a box, unless it is static (see `crag_abi`).
    fn retain(&mut self, ptr: VReg) {
        let (add, done) = (self.new_block(), self.new_block());
        let counted = self.counted(ptr);
        self.end(
            Term::Branch {
                cond: counted,
                then: add,
                otherwise: done,
            },
            Some(add),
        );
        let one = self.constant(1);
        self.atomic_add(ptr, one);
        self.end(Term::Jump(done), Some(done));
    }

    /// Gives up a reference to a box, unless it is static, and has the
    /// runtime free it with the last.
    fn release(&mut self, ptr: VReg) {
        self.release_by(ptr, RuntimeFn::Release);
    }

    /// Gives up a reference as `release` does, but has the runtime free
    /// the box with the last through deferred teardown, a bounded part at
    /// once and the rest between fibers (Plan §11.7.12).
    fn release_deferred(&mut self, ptr: VReg) {
        self.release_by(ptr, RuntimeFn::ReleaseDeferred);
    }

    fn release_by(&mut self, ptr: VReg, func: RuntimeFn) {
        let (sub, free, done) = (self.new_block(), self.new_block(), self.new_block());
        let counted = self.counted(ptr);
        self.end(
            Term::Branch {
                cond: counted,
                then: sub,
                otherwise: done,
            },
            Some(sub),
        );
        let minus_one = self.constant(-1);
        let before = self.atomic_add(ptr, minus_one);
        let one = self.constant(1);
        let last = self.cmp(Cond::Eq, before, one);
        self.end(
            Term::Branch {
                cond: last,
                then: free,
                otherwise: done,
            },
            Some(free),
        );
        self.push(Inst::CallRuntime {
            func,
            args: vec![ptr],
            dsts: Vec::new(),
        });
        self.dispose();
        self.end(Term::Jump(done), Some(done));
    }

    /// Runs the dispose code of each box the runtime queued, until none is
    /// left (§11.6.11): after a release that may have freed boxes, so that
    /// each handler runs at the drop, on the fiber that dropped the box.
    fn dispose(&mut self) {
        let (next, run, done) = (self.new_block(), self.new_block(), self.new_block());
        self.end(Term::Jump(next), Some(next));
        let [ptr, code] = self.runtime2(RuntimeFn::Disposal, Vec::new())[..] else {
            unreachable!("two words");
        };
        let zero = self.constant(0);
        let none = self.cmp(Cond::Eq, ptr, zero);
        self.end(
            Term::Branch {
                cond: none,
                then: done,
                otherwise: run,
            },
            Some(run),
        );
        self.push(Inst::CallIndirect {
            callee: code,
            args: vec![ptr],
            dsts: Vec::new(),
        });
        self.end(Term::Jump(next), Some(done));
    }

    /// Whether a box is counted: its count is not negative, which a static
    /// box's is.
    fn counted(&mut self, ptr: VReg) -> VReg {
        let count = self.load(ptr, COUNT_OFFSET);
        let zero = self.constant(0);
        self.cmp(Cond::Ge, count, zero)
    }

    /// Adds `value` to a box's count atomically; the count before.
    fn atomic_add(&mut self, ptr: VReg, value: VReg) -> VReg {
        let dst = self.reg();
        self.push(Inst::AtomicAdd {
            dst,
            addr: ptr,
            offset: COUNT_OFFSET,
            value,
        });
        dst
    }

    /// A new box of `size` bytes with a count of one and the type index in
    /// its header: popped inline from the free list of the heap's current
    /// page of its size class, or from `rt_alloc` when that list is empty
    /// or the box is too large for a class (see `crag_abi`).
    fn alloc(&mut self, size: u32, index: i64) -> VReg {
        let ptr = self.reg();
        let size_reg = self.constant(i64::from(size));
        let index = self.constant(index);
        let call = |this: &mut Self| {
            this.push(Inst::CallRuntime {
                func: RuntimeFn::Alloc,
                args: vec![size_reg, index],
                dsts: vec![ptr],
            })
        };
        let Some(class) = size_class(size) else {
            call(self);
            return ptr;
        };
        let ctx = self.reg();
        self.push(Inst::Context { dst: ctx });
        let heap = self.load(ctx, HEAP_OFFSET);
        let page = self.load(heap, 8 * class as i32);
        let block = self.load(page, PAGE_FREE_OFFSET);
        let (fast, slow, done) = (self.new_block(), self.new_block(), self.new_block());
        self.end(
            Term::Branch {
                cond: block,
                then: fast,
                otherwise: slow,
            },
            Some(fast),
        );
        let next = self.load(block, 0);
        self.push(Inst::Store {
            src: next,
            addr: page,
            offset: PAGE_FREE_OFFSET,
        });
        let used = self.load(page, PAGE_USED_OFFSET);
        let one = self.constant(1);
        let used = self.bin(LirBin::Add, used, one);
        self.push(Inst::Store {
            src: used,
            addr: page,
            offset: PAGE_USED_OFFSET,
        });
        self.push(Inst::Store {
            src: one,
            addr: block,
            offset: COUNT_OFFSET,
        });
        self.push(Inst::Store {
            src: index,
            addr: block,
            offset: TYPE_INDEX_OFFSET,
        });
        self.push(Inst::Move {
            dst: ptr,
            src: block,
        });
        self.end(Term::Jump(done), Some(slow));
        call(self);
        self.end(Term::Jump(done), Some(done));
        ptr
    }

    fn load(&mut self, addr: VReg, offset: i32) -> VReg {
        let dst = self.reg();
        self.push(Inst::Load { dst, addr, offset });
        dst
    }

    /// Ends the block with a test whether an index is one of `indices`.
    fn test_index(&mut self, index: VReg, indices: &[i64], hit: LirBlockId, miss: LirBlockId) {
        for (k, &i) in indices.iter().enumerate() {
            let c = self.constant(i);
            let same = self.cmp(Cond::Eq, index, c);
            let next = match k + 1 == indices.len() {
                true => miss,
                false => self.new_block(),
            };
            let term = Term::Branch {
                cond: same,
                then: hit,
                otherwise: next,
            };
            let more = (next != miss).then_some(next);
            self.end(term, more);
        }
        if indices.is_empty() {
            self.end(Term::Jump(miss), None);
        }
    }

    fn rvalue(&mut self, dst: Local, rvalue: &Rvalue<'db>) -> Result<Vec<VReg>, Unsupported> {
        let ty = self.local_ty(dst);
        match rvalue {
            Rvalue::Use(op) => self.operand(op, ty),
            Rvalue::Read(place) => self.read(place),
            Rvalue::Convert(op) => {
                let from = self.operand_ty(op, ty);
                let values = self.operand(op, from)?;
                self.convert(values, from, ty)
            }
            Rvalue::Binary {
                op, ty: b, a, b: c, ..
            } => {
                let operand_ty = Ty::builtin(self.db, *b);
                let x = self.operand(a, operand_ty)?;
                let y = self.operand(c, operand_ty)?;
                let (x, y) = (word(&x)?, word(&y)?);
                Ok(vec![self.arith(*op, *b, x, y)?])
            }
            Rvalue::Cast { op, from, value } => {
                let operand_ty = Ty::builtin(self.db, *from);
                let x = word(&self.operand(value, operand_ty)?)?;
                let un = |this: &mut Self, op: UnOp| {
                    let dst = this.reg();
                    this.push(Inst::Un { op, dst, src: x });
                    dst
                };
                Ok(vec![match op {
                    CastOp::Same => x,
                    CastOp::Wrap(to) => self.narrow(*to, x),
                    CastOp::IntToFloat if *from == Builtin::UInt64 => un(self, UnOp::UIntToFloat),
                    CastOp::IntToFloat => un(self, UnOp::SIntToFloat),
                    CastOp::FloatToInt => un(self, UnOp::FloatToSInt),
                    CastOp::Floor => un(self, UnOp::FloatFloor),
                    CastOp::Ceil => un(self, UnOp::FloatCeil),
                    CastOp::Trunc => un(self, UnOp::FloatTrunc),
                }])
            }
            Rvalue::Overflows { op, ty: b, a, b: c } => {
                let operand_ty = Ty::builtin(self.db, *b);
                let x = self.operand(a, operand_ty)?;
                let y = self.operand(c, operand_ty)?;
                let flag = self.overflows(*op, *b, word(&x)?, word(&y)?)?;
                Ok(vec![self.bool_of(flag)])
            }
            Rvalue::FloatOverflow(locals) => {
                let mask = self.constant(i64::MAX);
                let infinity = self.constant(f64::INFINITY.to_bits() as i64);
                let mut any = self.constant(0);
                for l in locals {
                    let bits = word(&self.locals[l.index()].clone())?;
                    let magnitude = self.bin(LirBin::And, bits, mask);
                    let infinite = self.cmp(Cond::Eq, magnitude, infinity);
                    any = self.bin(LirBin::Or, any, infinite);
                }
                Ok(vec![self.bool_of(any)])
            }
            Rvalue::Compare { op, ty: b, a, b: c } => {
                let operand_ty = Ty::builtin(self.db, *b);
                let x = self.operand(a, operand_ty)?;
                let y = self.operand(c, operand_ty)?;
                if let (Builtin::Str | Builtin::Bytes, CmpOp::Eq) = (b, op) {
                    let flag = self.text_equals(&x, &y)?;
                    return Ok(vec![self.bool_of(flag)]);
                }
                let cond = compare_cond(*op, *b)?;
                let flag = self.cmp(cond, word(&x)?, word(&y)?);
                Ok(vec![self.bool_of(flag)])
            }
            Rvalue::Record {
                ty: record,
                fields,
                dispose,
            } => {
                let (slots, size) =
                    record_layout(self.db, self.program, *record).ok_or("records of this type")?;
                let index = type_index(*record);
                self.describe(*record)?;
                let mut values = Vec::new();
                for (name, op) in fields {
                    let slot = slots
                        .iter()
                        .find(|s| s.name == *name)
                        .ok_or("records of this type")?;
                    values.push((slot.offset, self.operand(op, slot.ty)?));
                }
                let ptr = self.alloc(size, index);
                for (offset, words) in values {
                    for (k, src) in words.into_iter().enumerate() {
                        self.push(Inst::Store {
                            src,
                            addr: ptr,
                            offset: (offset + 8 * k as u32) as i32,
                        });
                    }
                }
                // The box holds the address of its dispose code, which the
                // runtime gives generated code when the count reaches zero.
                if let Some(code) = dispose {
                    let at = dispose_word(self.db, self.program, *record)
                        .ok_or("records of this type")?;
                    if !self.calls.contains(code) {
                        self.calls.push(*code);
                    }
                    let addr = self.reg();
                    self.push(Inst::FuncAddr {
                        dst: addr,
                        func: self.slot(*code),
                        params: 1,
                        returns: 0,
                    });
                    self.push(Inst::Store {
                        src: addr,
                        addr: ptr,
                        offset: at as i32,
                    });
                }
                Ok(vec![ptr])
            }
            Rvalue::List(items) => match ty.as_builtin(self.db) {
                Some((Builtin::List, [element])) => {
                    let element = *element;
                    let values = items
                        .iter()
                        .map(|op| self.operand(op, element))
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut list = self.empty(ty, LIST_SIZE)?;
                    for words in values {
                        let [w0, w1] = self.pad(words);
                        list = self.runtime(RuntimeFn::ListPush, vec![list, w0, w1]);
                    }
                    Ok(vec![list])
                }
                Some((Builtin::Set, [element])) => {
                    let element = *element;
                    let entries: Vec<_> = items.iter().map(|op| (op.clone(), None)).collect();
                    Ok(vec![self.map(ty, element, None, &entries)?])
                }
                _ => Err("collections of this type"),
            },
            Rvalue::Map(entries) => match ty.as_builtin(self.db) {
                Some((Builtin::Map, [k, v])) => {
                    let (k, v) = (*k, *v);
                    let entries: Vec<_> = entries
                        .iter()
                        .map(|(key, value)| (key.clone(), Some(value.clone())))
                        .collect();
                    Ok(vec![self.map(ty, k, Some(v), &entries)?])
                }
                _ => Err("collections of this type"),
            },
            Rvalue::Len(place) => {
                let list = word(&self.read(place)?)?;
                Ok(vec![self.load(list, LEN_OFFSET)])
            }
            Rvalue::Index { list, index } => {
                let list_ty = self.place_ty(list)?;
                let ptr = word(&self.read(list)?)?;
                let int = Ty::builtin(self.db, Builtin::Int);
                let index = word(&self.operand(index, int)?)?;
                self.element(ptr, list_ty, index)
            }
            Rvalue::MapGet { map, key, boxed } => {
                let map_ty = self.place_ty(map)?;
                let Some((Builtin::Map, &[k, v])) = map_ty.as_builtin(self.db) else {
                    return Err("collections of this type");
                };
                self.describe(map_ty)?;
                let ptr = word(&self.read(map)?)?;
                let key = self.operand(key, k)?;
                let [k0, k1] = self.pad(key);
                let at = self.runtime(RuntimeFn::MapGet, vec![ptr, k0, k1]);
                self.option(at, v, ty, *boxed)
            }
            Rvalue::Slice { list, front, back } => {
                let list_ty = self.place_ty(list)?;
                self.describe(list_ty)?;
                let ptr = word(&self.read(list)?)?;
                let front = self.constant(i64::from(*front));
                let back = self.constant(i64::from(*back));
                Ok(vec![
                    self.runtime(RuntimeFn::ListSlice, vec![ptr, front, back]),
                ])
            }
            Rvalue::Concat(parts) => self.concat(parts, ty),
            Rvalue::Closure {
                code,
                env,
                captures,
                placement,
            } => {
                let addr = self.code_addr(*code, ty)?;
                if captures.is_empty() {
                    return Ok(vec![addr, self.constant(0)]);
                }
                let (slots, size) =
                    record_layout(self.db, self.program, *env).ok_or("captures of this type")?;
                let mut values = Vec::new();
                for (i, op) in captures.iter().enumerate() {
                    let name = i.to_string();
                    let slot = slots
                        .iter()
                        .find(|s| *s.name.text(self.db) == name)
                        .ok_or("captures of this type")?;
                    values.push((slot.offset, self.operand(op, slot.ty)?));
                }
                let index = type_index(*env);
                let ptr = match placement {
                    ClosurePlacement::Heap => {
                        self.describe(*env)?;
                        self.alloc(size, index)
                    }
                    ClosurePlacement::SideStack => {
                        let ptr = self.reg();
                        self.push(Inst::SidePush {
                            dst: ptr,
                            size,
                            align: 8,
                        });
                        let count = self.constant(STATIC_COUNT as i64);
                        self.push(Inst::Store {
                            src: count,
                            addr: ptr,
                            offset: COUNT_OFFSET,
                        });
                        let index = self.constant(index);
                        self.push(Inst::Store {
                            src: index,
                            addr: ptr,
                            offset: TYPE_INDEX_OFFSET,
                        });
                        ptr
                    }
                };
                for (offset, words) in values {
                    for (k, src) in words.into_iter().enumerate() {
                        self.push(Inst::Store {
                            src,
                            addr: ptr,
                            offset: (offset + 8 * k as u32) as i32,
                        });
                    }
                }
                Ok(vec![addr, ptr])
            }
            Rvalue::FnValue { code, env } => {
                let addr = self.code_addr(*code, ty)?;
                let env = match env {
                    Operand::Local(l) => self.locals[l.index()].clone(),
                    Operand::Const(_) => vec![self.constant(0)],
                };
                Ok(vec![addr, word(&env)?])
            }
            Rvalue::Intrinsic(intrinsic, args) => self.intrinsic(*intrinsic, args, ty),
        }
    }

    /// The type of the value a ref cell or an `ext` of type `cell` holds.
    fn cell_value_ty(&self, cell: Ty<'db>) -> Result<Ty<'db>, Unsupported> {
        match cell.as_builtin(self.db) {
            Some((Builtin::Ref | Builtin::Ext, &[value])) => Ok(value),
            _ => Err("cells of this type"),
        }
    }

    /// Static data with the bytes, and its address.
    fn static_data(&mut self, bytes: Vec<u8>) -> VReg {
        let data = match self.data.iter().position(|d| *d == bytes) {
            Some(d) => d,
            None => {
                self.data.push(bytes);
                self.data.len() - 1
            }
        };
        let ptr = self.reg();
        self.push(Inst::DataAddr {
            dst: ptr,
            data: data as u32,
        });
        ptr
    }

    /// What the delivery of a signal of type `ty` needs to know of it, in
    /// static data (see `crag_abi::RuntimeFn::SignalEmit`): its type index,
    /// whether its box's header has the index instead, and its name.
    fn signal_info(&mut self, ty: Ty<'db>, boxed: bool) -> VReg {
        let name = ty.display(self.db);
        let mut bytes = Vec::new();
        bytes.extend((type_index(ty) as u64).to_le_bytes());
        bytes.extend(u64::from(boxed).to_le_bytes());
        bytes.extend((name.len() as u64).to_le_bytes());
        bytes.extend(name.as_bytes());
        self.static_data(bytes)
    }

    /// Delivers a signal, whose first word is `w0`, to its handler, or to
    /// the root's (§11.3). The handler gets a reference of its own; the
    /// caller keeps the signal's.
    fn deliver(&mut self, w0: VReg, info: VReg) {
        let index = self.reg();
        let (from_box, from_type, found_index) =
            (self.new_block(), self.new_block(), self.new_block());
        let boxed = self.load(info, 8);
        self.end(
            Term::Branch {
                cond: boxed,
                then: from_box,
                otherwise: from_type,
            },
            Some(from_box),
        );
        // The box of a record has the type index of the record's type, a
        // subtype's too, in the lower half of its header's second word.
        let header = self.load(w0, TYPE_INDEX_OFFSET);
        let lower = self.constant(0xffff_ffff);
        let masked = self.bin(LirBin::And, header, lower);
        self.push(Inst::Move {
            dst: index,
            src: masked,
        });
        self.end(Term::Jump(found_index), Some(from_type));
        let static_index = self.load(info, 0);
        self.push(Inst::Move {
            dst: index,
            src: static_index,
        });
        self.end(Term::Jump(found_index), Some(found_index));
        let out = self.scratch();
        let found = self.runtime(RuntimeFn::SignalFind, vec![index, out]);
        let (call, root, done) = (self.new_block(), self.new_block(), self.new_block());
        self.end(
            Term::Branch {
                cond: found,
                then: call,
                otherwise: root,
            },
            Some(call),
        );
        let code = self.load(out, 0);
        let env = self.load(out, 8);
        let words = self.load(out, 16);
        let (with_value, without, left) = (self.new_block(), self.new_block(), self.new_block());
        self.end(
            Term::Branch {
                cond: words,
                then: with_value,
                otherwise: without,
            },
            Some(with_value),
        );
        // A handler of one word takes a record: the signal's box.
        self.retain(w0);
        self.push(Inst::CallIndirect {
            callee: code,
            args: vec![env, w0],
            dsts: Vec::new(),
        });
        self.end(Term::Jump(left), Some(without));
        self.push(Inst::CallIndirect {
            callee: code,
            args: vec![env],
            dsts: Vec::new(),
        });
        self.end(Term::Jump(left), Some(left));
        self.push(Inst::CallRuntime {
            func: RuntimeFn::SignalLeave,
            args: Vec::new(),
            dsts: Vec::new(),
        });
        self.end(Term::Jump(done), Some(root));
        let header = self.constant(24);
        let name = self.bin(LirBin::Add, info, header);
        let len = self.load(info, 16);
        self.push(Inst::CallRuntime {
            func: RuntimeFn::SignalDefault,
            args: vec![name, len],
            dsts: Vec::new(),
        });
        self.end(Term::Jump(done), Some(done));
    }

    /// A box of type `ty`, a `RuntimeStream` or `RuntimeHub`, holding a
    /// handle of the runtime.
    fn handle_box(&mut self, ty: Ty<'db>, handle: VReg) -> Result<Vec<VReg>, Unsupported> {
        self.describe(ty)?;
        let ptr = self.alloc(HEADER_SIZE + 8, type_index(ty));
        self.push(Inst::Store {
            src: handle,
            addr: ptr,
            offset: HEADER_SIZE as i32,
        });
        Ok(vec![ptr])
    }

    /// A result of the runtime's sockets as `std.io` takes it: `value`, or
    /// minus the error number when there is one.
    fn fd_or_error(&mut self, value: VReg, errno: VReg) -> VReg {
        let zero = self.constant(0);
        let failed = self.cmp(Cond::Ne, errno, zero);
        let negated = self.bin(LirBin::Sub, zero, errno);
        let out = self.reg();
        self.push(Inst::Select {
            dst: out,
            cond: failed,
            a: negated,
            b: value,
        });
        out
    }

    /// The runtime's handle of a type's shapes, which the code keeps as
    /// bytes (`RuntimeFn::ValueShapes`).
    fn value_shapes(&mut self, ty: Ty<'db>) -> Result<VReg, Unsupported> {
        let (shapes, root) = crate::shape::shapes(self.db, self.program, ty);
        let mut bytes = root.to_le_bytes().to_vec();
        bytes.extend(shapes.encode());
        let words = self.text_literal(&bytes)?;
        Ok(self.runtime(RuntimeFn::ValueShapes, words))
    }

    /// The two words of a string or bytes operand.
    fn text_words(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<[VReg; 2], Unsupported> {
        let op_ty = self.operand_ty(op, ty);
        match self.operand(op, op_ty)?[..] {
            [w0, w1] => Ok([w0, w1]),
            _ => Err("this operation of the runtime"),
        }
    }

    /// The runtime handle in the box of a `RuntimeStream` or `RuntimeHub`.
    fn handle_of(&mut self, handle: &Operand<'db>) -> Result<VReg, Unsupported> {
        let ptr = self.box_of(handle)?;
        Ok(self.load(ptr, HEADER_SIZE as i32))
    }

    /// The box a local of a `Ref` or an `Ext` holds.
    fn box_of(&mut self, cell: &Operand<'db>) -> Result<VReg, Unsupported> {
        let Operand::Local(local) = cell else {
            return Err("cells of this type");
        };
        word(&self.locals[local.index()].clone())
    }

    /// The address of the cell in the box a local of a `Ref` holds.
    fn cell_addr(&mut self, cell: &Operand<'db>) -> Result<VReg, Unsupported> {
        let Operand::Local(local) = cell else {
            return Err("cells of this type");
        };
        let ptr = word(&self.locals[local.index()].clone())?;
        let header = self.constant(i64::from(HEADER_SIZE));
        Ok(self.bin(LirBin::Add, ptr, header))
    }

    /// The type index of the list of `value`, whose elements the runtime
    /// lays a cell's value out as.
    fn cell_list(&mut self, value: Ty<'db>) -> Result<VReg, Unsupported> {
        let list = Ty::new(self.db, TyKind::Builtin(Builtin::List, vec![value]));
        self.describe(list)?;
        Ok(self.constant(type_index(list)))
    }

    /// The scratch words for reads of ref cells.
    fn scratch(&mut self) -> VReg {
        match self.scratch {
            Some(reg) => reg,
            None => {
                let reg = self.reg();
                self.scratch = Some(reg);
                reg
            }
        }
    }

    /// The runtime call of an intrinsic, and its result's words; `ty` is
    /// the result's type.
    fn intrinsic(
        &mut self,
        intrinsic: Intrinsic<'db>,
        args: &[Operand<'db>],
        ty: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let int = Ty::builtin(self.db, Builtin::Int);
        match (intrinsic, args) {
            (Intrinsic::RefNew, [value]) => {
                let value_ty = self.cell_value_ty(ty)?;
                self.describe(ty)?;
                let words = self.operand(value, value_ty)?;
                let ptr = self.alloc(HEADER_SIZE + REF_CELL_SIZE as u32, type_index(ty));
                let zero = self.constant(0);
                let header = HEADER_SIZE as i32;
                self.push(Inst::Store {
                    src: zero,
                    addr: ptr,
                    offset: header,
                });
                for (k, src) in self.pad(words).into_iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: header + 8 + 8 * k as i32,
                    });
                }
                Ok(vec![ptr])
            }
            (Intrinsic::RefRead, [cell]) => {
                let cell = self.cell_addr(cell)?;
                let out = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::RefRead, vec![cell, out])])
            }
            (Intrinsic::RefValue, []) => {
                let out = self.scratch();
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                Ok((0..words).map(|k| self.load(out, 8 * k as i32)).collect())
            }
            (Intrinsic::RefDone, []) => {
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::RefDone,
                    args: Vec::new(),
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::RefCommit, [cell, version, value]) => {
                let cell_ty = self.operand_ty(cell, ty);
                let value_ty = self.cell_value_ty(cell_ty)?;
                let list = self.cell_list(value_ty)?;
                let cell = self.cell_addr(cell)?;
                let version = word(&self.operand(version, int)?)?;
                let words = self.operand(value, value_ty)?;
                let [w0, w1] = self.pad(words);
                Ok(vec![self.runtime(
                    RuntimeFn::RefCommit,
                    vec![cell, version, list, w0, w1],
                )])
            }
            (Intrinsic::ExtNew, [value]) => {
                let value_ty = self.cell_value_ty(ty)?;
                self.describe(ty)?;
                let words = self.operand(value, value_ty)?;
                let ptr = self.alloc(HEADER_SIZE + 24, type_index(ty));
                let lock = self.runtime(RuntimeFn::ExtNew, Vec::new());
                let header = HEADER_SIZE as i32;
                self.push(Inst::Store {
                    src: lock,
                    addr: ptr,
                    offset: header,
                });
                for (k, src) in self.pad(words).into_iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: header + 8 + 8 * k as i32,
                    });
                }
                Ok(vec![ptr])
            }
            (Intrinsic::ExtLock | Intrinsic::ExtUnlock, [cell]) => {
                let ptr = self.box_of(cell)?;
                let lock = self.load(ptr, HEADER_SIZE as i32);
                let (func, region) = match intrinsic {
                    Intrinsic::ExtLock => (RuntimeFn::ExtLock, RuntimeFn::EnterNoCancel),
                    _ => (RuntimeFn::ExtUnlock, RuntimeFn::ExitNoCancel),
                };
                // The lock is where a cancelled task stops; the closure
                // runs where cancellation waits.
                self.push(Inst::CallRuntime {
                    func,
                    args: vec![lock],
                    dsts: Vec::new(),
                });
                self.push(Inst::CallRuntime {
                    func: region,
                    args: Vec::new(),
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::ExtValue, [cell]) => {
                let ptr = self.box_of(cell)?;
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                let at = HEADER_SIZE as i32 + 8;
                Ok((0..words)
                    .map(|k| self.load(ptr, at + 8 * k as i32))
                    .collect())
            }
            (Intrinsic::ExtStore, [cell, value]) => {
                let cell_ty = self.operand_ty(cell, ty);
                let Some((Builtin::Ext, &[value_ty])) = cell_ty.as_builtin(self.db) else {
                    return Err("cells of this type");
                };
                let value_layout = layout(self.db, self.program, value_ty);
                let words = value_layout.ok_or("values of this type")?.words();
                let ptr = self.box_of(cell)?;
                let new = self.operand(value, value_ty)?;
                let at = HEADER_SIZE as i32 + 8;
                let old: Vec<VReg> = (0..words)
                    .map(|k| self.load(ptr, at + 8 * k as i32))
                    .collect();
                for (k, &src) in new.iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: at + 8 * k as i32,
                    });
                }
                self.count_words(value_layout, value_ty, &old, Self::release)?;
                Ok(Vec::new())
            }
            (Intrinsic::LazyNew, [code]) => {
                let Some((Builtin::Lazy, &[value_ty])) = ty.as_builtin(self.db) else {
                    return Err("lazy values of this type");
                };
                self.describe(ty)?;
                let code_ty = self.operand_ty(code, ty);
                let [code, env] = self.operand(code, code_ty)?[..] else {
                    return Err("lazy values of this type");
                };
                let list = self.cell_list(value_ty)?;
                let cell = self.runtime(RuntimeFn::LazyNew, vec![list]);
                let ptr = self.alloc(HEADER_SIZE + 24, type_index(ty));
                let header = HEADER_SIZE as i32;
                for (k, src) in [cell, code, env].into_iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: header + 8 * k as i32,
                    });
                }
                Ok(vec![ptr])
            }
            (Intrinsic::LazyGet, [lazy]) => {
                let ptr = self.box_of(lazy)?;
                let cell = self.load(ptr, HEADER_SIZE as i32);
                let out = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::LazyGet, vec![cell, out])])
            }
            (Intrinsic::LazyValue, []) => {
                let out = self.scratch();
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                Ok((0..words).map(|k| self.load(out, 8 * k as i32)).collect())
            }
            (Intrinsic::LazyCode, [lazy]) => {
                let ptr = self.box_of(lazy)?;
                let header = HEADER_SIZE as i32;
                Ok(vec![
                    self.load(ptr, header + 8),
                    self.load(ptr, header + 16),
                ])
            }
            (Intrinsic::LazySet, [lazy, value]) => {
                let value_ty = self.operand_ty(value, ty);
                let value_layout = layout(self.db, self.program, value_ty);
                let ptr = self.box_of(lazy)?;
                let cell = self.load(ptr, HEADER_SIZE as i32);
                let words = self.operand(value, value_ty)?;
                // The cell takes references of its own; the reader keeps
                // the value.
                self.count_words(value_layout, value_ty, &words, Self::retain)?;
                let [w0, w1] = self.pad(words);
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::LazySet,
                    args: vec![cell, w0, w1],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::LazyTrap, []) => {
                let out = self.scratch();
                let kind = self.load(out, 0);
                let position = self.constant(NO_POSITION as i64);
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::Trap,
                    args: vec![kind, position],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::StreamNew { value }, [capacity]) => {
                let capacity = word(&self.operand(capacity, int)?)?;
                let list = self.cell_list(value)?;
                let ends = self.runtime2(RuntimeFn::StreamNew, vec![capacity, list]);
                // The source waits in the scratch words for `StreamPeer`.
                let out = self.scratch();
                self.push(Inst::Store {
                    src: ends[1],
                    addr: out,
                    offset: 0,
                });
                self.handle_box(ty, ends[0])
            }
            (Intrinsic::StreamPeer, []) => {
                let out = self.scratch();
                let source = self.load(out, 0);
                self.handle_box(ty, source)
            }
            (Intrinsic::StreamPut { wait }, [end, value]) => {
                let value_ty = self.operand_ty(value, ty);
                let value_layout = layout(self.db, self.program, value_ty);
                let end = self.handle_of(end)?;
                let words = self.operand(value, value_ty)?;
                // The value's references go with it once it is sent; those
                // taken for it are given back otherwise.
                self.count_words(value_layout, value_ty, &words, Self::retain)?;
                let [w0, w1] = self.pad(words.clone());
                let func = if wait {
                    RuntimeFn::StreamPut
                } else {
                    RuntimeFn::StreamTryPut
                };
                let status = self.runtime(func, vec![end, w0, w1]);
                let (unsent, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: status,
                        then: unsent,
                        otherwise: done,
                    },
                    Some(unsent),
                );
                self.count_words(value_layout, value_ty, &words, Self::release)?;
                self.end(Term::Jump(done), Some(done));
                Ok(vec![status])
            }
            (Intrinsic::StreamNext, [end]) => {
                let end = self.handle_of(end)?;
                let out = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::StreamNext, vec![end, out])])
            }
            (Intrinsic::StreamValue, []) => {
                let out = self.scratch();
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                Ok((0..words).map(|k| self.load(out, 8 * k as i32)).collect())
            }
            (
                Intrinsic::StreamClose
                | Intrinsic::HubSeal
                | Intrinsic::HubSink
                | Intrinsic::HubSource,
                [handle],
            ) => {
                let handle = self.handle_of(handle)?;
                let func = match intrinsic {
                    Intrinsic::StreamClose => RuntimeFn::StreamClose,
                    Intrinsic::HubSeal => RuntimeFn::HubSeal,
                    Intrinsic::HubSink => RuntimeFn::HubSink,
                    _ => RuntimeFn::HubSource,
                };
                if matches!(intrinsic, Intrinsic::StreamClose | Intrinsic::HubSeal) {
                    self.push(Inst::CallRuntime {
                        func,
                        args: vec![handle],
                        dsts: Vec::new(),
                    });
                    return Ok(Vec::new());
                }
                let end = self.runtime(func, vec![handle]);
                self.handle_box(ty, end)
            }
            (Intrinsic::HubNew { value }, [capacity, kind]) => {
                let capacity = word(&self.operand(capacity, int)?)?;
                let kind = word(&self.operand(kind, int)?)?;
                let list = self.cell_list(value)?;
                let hub = self.runtime(RuntimeFn::HubNew, vec![capacity, list, kind]);
                self.handle_box(ty, hub)
            }
            (Intrinsic::HubRelease, [hub, n]) => {
                let hub = self.handle_of(hub)?;
                let n = word(&self.operand(n, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::HubRelease,
                    args: vec![hub, n],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::IoListen | Intrinsic::IoAccept | Intrinsic::IoSocket, args) => {
                let (func, args) = match (intrinsic, args) {
                    (Intrinsic::IoListen, [port]) => {
                        (RuntimeFn::IoListen, vec![word(&self.operand(port, int)?)?])
                    }
                    (Intrinsic::IoAccept, [socket]) => {
                        (RuntimeFn::IoAccept, vec![self.handle_of(socket)?])
                    }
                    (Intrinsic::IoSocket, []) => (RuntimeFn::IoSocket, Vec::new()),
                    _ => return Err("this operation of the runtime"),
                };
                let out = self.runtime2(func, args);
                Ok(vec![self.fd_or_error(out[0], out[1])])
            }
            (Intrinsic::IoOwn, [fd]) => {
                let fd = word(&self.operand(fd, int)?)?;
                self.handle_box(ty, fd)
            }
            (Intrinsic::IoPort, [socket]) => {
                let fd = self.handle_of(socket)?;
                Ok(vec![self.runtime(RuntimeFn::IoPort, vec![fd])])
            }
            (Intrinsic::IoConnect, [socket, port]) => {
                let fd = self.handle_of(socket)?;
                let port = word(&self.operand(port, int)?)?;
                let out = self.runtime2(RuntimeFn::IoConnectLocal, vec![fd, port]);
                Ok(vec![out[1]])
            }
            (Intrinsic::IoRead, [socket, max]) => {
                let fd = self.handle_of(socket)?;
                let max = word(&self.operand(max, int)?)?;
                let buffer = self.runtime(RuntimeFn::IoBuffer, vec![max]);
                let header = self.constant(i64::from(HEADER_SIZE));
                let data = self.bin(LirBin::Add, buffer, header);
                let out = self.runtime2(RuntimeFn::IoRead, vec![fd, data, max]);
                let (n, errno) = (out[0], out[1]);
                // An end or an error keeps no bytes.
                let zero = self.constant(0);
                let failed = self.cmp(Cond::Ne, errno, zero);
                let count = self.reg();
                self.push(Inst::Select {
                    dst: count,
                    cond: failed,
                    a: zero,
                    b: n,
                });
                let bytes = self.runtime2(RuntimeFn::IoBytes, vec![buffer, count]);
                let scratch = self.scratch();
                for (k, &src) in bytes.iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: scratch,
                        offset: 8 * k as i32,
                    });
                }
                Ok(vec![self.fd_or_error(n, errno)])
            }
            (Intrinsic::IoReadBytes, []) => {
                let scratch = self.scratch();
                Ok(vec![self.load(scratch, 0), self.load(scratch, 8)])
            }
            (Intrinsic::IoWrite, [socket, bytes, left]) => {
                let fd = self.handle_of(socket)?;
                let bytes_ty = self.operand_ty(bytes, ty);
                let [w0, w1] = self.operand(bytes, bytes_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let left = word(&self.operand(left, int)?)?;
                let out = self.runtime2(RuntimeFn::IoWriteBytes, vec![fd, w0, w1, left]);
                Ok(vec![self.fd_or_error(out[0], out[1])])
            }
            (Intrinsic::IoPrint, [text, newline]) => {
                let text_ty = self.operand_ty(text, ty);
                let [w0, w1] = self.operand(text, text_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let newline = word(&self.operand(newline, int)?)?;
                Ok(vec![
                    self.runtime(RuntimeFn::IoPrint, vec![w0, w1, newline]),
                ])
            }
            (Intrinsic::IoFault | Intrinsic::TrapWith(_), []) => {
                let kind = match intrinsic {
                    Intrinsic::TrapWith(kind) => self.constant(i64::from(kind)),
                    _ => self.constant(AbiTrap::Fault as i64),
                };
                let position = self.constant(crag_abi::NO_POSITION as i64);
                // `rt_trap` does not return.
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::Trap,
                    args: vec![kind, position],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::IoReadFile, [path]) => {
                let path_ty = self.operand_ty(path, ty);
                let [w0, w1] = self.operand(path, path_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                // The bytes wait in the scratch words for `IoReadBytes`.
                let scratch = self.scratch();
                Ok(vec![
                    self.runtime(RuntimeFn::IoReadFile, vec![w0, w1, scratch]),
                ])
            }
            (Intrinsic::IoSocketAny, []) => {
                let out = self.runtime2(RuntimeFn::IoSocketAny, Vec::new());
                Ok(vec![self.fd_or_error(out[0], out[1])])
            }
            (Intrinsic::IoConnectHost, [socket, host, port]) => {
                let fd = self.handle_of(socket)?;
                let host_ty = self.operand_ty(host, ty);
                let [w0, w1] = self.operand(host, host_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let port = word(&self.operand(port, int)?)?;
                let out = self.runtime2(RuntimeFn::IoConnectHost, vec![fd, w0, w1, port]);
                Ok(vec![out[1]])
            }
            (Intrinsic::TextUtf8, [bytes]) => {
                let bytes_ty = self.operand_ty(bytes, ty);
                let [w0, w1] = self.operand(bytes, bytes_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                Ok(vec![self.runtime(RuntimeFn::TextUtf8, vec![w0, w1])])
            }
            (Intrinsic::TextCast, [text]) => {
                let bytes = Ty::builtin(self.db, Builtin::Bytes);
                self.concat(std::slice::from_ref(text), bytes)
            }
            (Intrinsic::TextMeasure(op), [text]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let op = self.constant(i64::from(op));
                Ok(vec![self.runtime(RuntimeFn::TextMeasure, vec![op, w0, w1])])
            }
            (Intrinsic::TextAt(op), [text, at]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let at = word(&self.operand(at, int)?)?;
                let op = self.constant(i64::from(op));
                Ok(vec![self.runtime(RuntimeFn::TextAt, vec![op, w0, w1, at])])
            }
            (Intrinsic::TextFind(op), [text, part, from @ ..]) => {
                let [a0, a1] = self.text_words(text, ty)?;
                let [b0, b1] = self.text_words(part, ty)?;
                let op = self.constant(i64::from(op));
                let packed = match from {
                    [from] => {
                        let from = word(&self.operand(from, int)?)?;
                        let three = self.constant(3);
                        let shifted = self.bin(LirBin::Shl, from, three);
                        self.bin(LirBin::Or, shifted, op)
                    }
                    _ => op,
                };
                Ok(vec![self.runtime(
                    RuntimeFn::TextFind,
                    vec![a0, a1, b0, b1, packed],
                )])
            }
            (Intrinsic::TextMap(op), [text]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let op = self.constant(i64::from(op));
                Ok(self.runtime2(RuntimeFn::TextMap, vec![op, w0, w1]).to_vec())
            }
            (Intrinsic::TextSlice, [text, from, to]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let from = word(&self.operand(from, int)?)?;
                let to = word(&self.operand(to, int)?)?;
                Ok(self
                    .runtime2(RuntimeFn::TextSlice, vec![w0, w1, from, to])
                    .to_vec())
            }
            (Intrinsic::CodePointOp(op), [c]) => {
                let c_ty = self.operand_ty(c, ty);
                let c = word(&self.operand(c, c_ty)?)?;
                let op = self.constant(i64::from(op));
                Ok(vec![self.runtime(RuntimeFn::CodePointOp, vec![op, c])])
            }
            (Intrinsic::TextParse(op), [text, base @ ..]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let base = match base {
                    [base] => word(&self.operand(base, int)?)?,
                    _ => self.constant(10),
                };
                let op = self.constant(i64::from(op));
                let out = self.runtime2(RuntimeFn::TextParse, vec![op, w0, w1, base]);
                // The value waits in the scratch words for `TextParsed`.
                let scratch = self.scratch();
                self.push(Inst::Store {
                    src: out[0],
                    addr: scratch,
                    offset: 0,
                });
                Ok(vec![out[1]])
            }
            (Intrinsic::TextParsed, []) => {
                let scratch = self.scratch();
                Ok(vec![self.load(scratch, 0)])
            }
            (Intrinsic::Word, [x]) => {
                let x_ty = self.operand_ty(x, ty);
                Ok(vec![word(&self.operand(x, x_ty)?)?])
            }
            (Intrinsic::ValueOp { op, ty: value_ty }, [a, rest @ ..]) => {
                let handle = self.value_shapes(value_ty)?;
                let a = self.operand(a, value_ty)?;
                let [a0, a1] = self.pad(a);
                let [b0, b1] = match rest {
                    [b] => {
                        let b = self.operand(b, value_ty)?;
                        self.pad(b)
                    }
                    _ => [a0, a1],
                };
                let eight = self.constant(8);
                let shifted = self.bin(LirBin::Shl, handle, eight);
                let op = self.constant(i64::from(op));
                let packed = self.bin(LirBin::Or, shifted, op);
                Ok(vec![
                    self.runtime(RuntimeFn::ValueOp, vec![packed, a0, a1, b0, b1]),
                ])
            }
            (Intrinsic::ValueShow { ty: value_ty }, [x]) => {
                let handle = self.value_shapes(value_ty)?;
                let x = self.operand(x, value_ty)?;
                let [w0, w1] = self.pad(x);
                Ok(self
                    .runtime2(RuntimeFn::ValueShow, vec![handle, w0, w1])
                    .to_vec())
            }
            (Intrinsic::TestFailure, [message, at]) => {
                let [w0, w1] = self.text_words(message, ty)?;
                let at = word(&self.operand(at, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::TestRecord,
                    args: vec![w0, w1, at],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::Site(expr), []) => {
                let at = self
                    .positions
                    .get(expr.index())
                    .map_or(NO_POSITION as i64, |r| i64::from(r.start));
                Ok(vec![self.constant(at)])
            }
            (Intrinsic::BytesRead, [bytes, packed, at]) => {
                let [w0, w1] = self.text_words(bytes, ty)?;
                let packed = word(&self.operand(packed, int)?)?;
                let at = word(&self.operand(at, int)?)?;
                let out = self.runtime2(RuntimeFn::BytesRead, vec![packed, w0, w1, at]);
                // The value waits in the scratch words for `TextParsed`.
                let scratch = self.scratch();
                self.push(Inst::Store {
                    src: out[0],
                    addr: scratch,
                    offset: 0,
                });
                Ok(vec![out[1]])
            }
            (Intrinsic::BytesWrite, [bytes, packed, at, value]) => {
                let [w0, w1] = self.text_words(bytes, ty)?;
                let packed = word(&self.operand(packed, int)?)?;
                let at = word(&self.operand(at, int)?)?;
                let value = word(&self.operand(value, int)?)?;
                let args = vec![packed, w0, w1, at, value];
                Ok(self.runtime2(RuntimeFn::BytesWrite, args).to_vec())
            }
            (Intrinsic::BytesOfList, [list]) => {
                let list_ty = self.operand_ty(list, ty);
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                Ok(self.runtime2(RuntimeFn::BytesOfList, vec![list]).to_vec())
            }
            (Intrinsic::EnvArgs, []) => {
                let list = self.empty(ty, LIST_SIZE)?;
                Ok(vec![self.runtime(RuntimeFn::EnvArgs, vec![list])])
            }
            (Intrinsic::EnvVar, [name]) => {
                let [w0, w1] = self.text_words(name, ty)?;
                // The value waits in the scratch words for `IoReadBytes`.
                let scratch = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::EnvVar, vec![w0, w1, scratch])])
            }
            (Intrinsic::EnvVars, []) => {
                let map = self.empty(ty, MAP_SIZE)?;
                Ok(vec![self.runtime(RuntimeFn::EnvVars, vec![map])])
            }
            (Intrinsic::EnvPlatform, [which]) => {
                let which = word(&self.operand(which, int)?)?;
                Ok(vec![self.runtime(RuntimeFn::EnvPlatform, vec![which])])
            }
            (Intrinsic::CollCount, [c]) => {
                let c_ty = self.operand_ty(c, ty);
                let ptr = word(&self.operand(c, c_ty)?)?;
                Ok(vec![self.load(ptr, LEN_OFFSET)])
            }
            (Intrinsic::ListSet, [list, at, value]) => {
                let list_ty = self.operand_ty(list, ty);
                let element = element_of(self.db, list_ty)?;
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                let at = word(&self.operand(at, int)?)?;
                let words = self.operand(value, element)?;
                let [w0, w1] = self.pad(words);
                Ok(vec![
                    self.runtime(RuntimeFn::ListSet, vec![list, at, w0, w1]),
                ])
            }
            (Intrinsic::ListConcat, [a, b]) => {
                let list_ty = self.operand_ty(a, ty);
                self.describe(list_ty)?;
                let a = word(&self.operand(a, list_ty)?)?;
                let b = word(&self.operand(b, list_ty)?)?;
                Ok(vec![self.runtime(RuntimeFn::ListConcat, vec![a, b])])
            }
            (Intrinsic::ListSlice, [list, front, back]) => {
                let list_ty = self.operand_ty(list, ty);
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                let front = word(&self.operand(front, int)?)?;
                let back = word(&self.operand(back, int)?)?;
                Ok(vec![
                    self.runtime(RuntimeFn::ListSlice, vec![list, front, back]),
                ])
            }
            (Intrinsic::MapInsert | Intrinsic::SetInsert, [map, key, value @ ..]) => {
                let map_ty = self.operand_ty(map, ty);
                let (k, v) = match map_ty.as_builtin(self.db) {
                    Some((Builtin::Map, &[k, v])) => (k, Some(v)),
                    Some((Builtin::Set, &[k])) => (k, None),
                    _ => return Err("collections of this type"),
                };
                self.describe(map_ty)?;
                let map = word(&self.operand(map, map_ty)?)?;
                let key = self.operand(key, k)?;
                let [k0, k1] = self.pad(key);
                let [v0, v1] = match (value, v) {
                    ([value], Some(v)) => {
                        let value = self.operand(value, v)?;
                        self.pad(value)
                    }
                    _ => self.pad(Vec::new()),
                };
                Ok(vec![
                    self.runtime(RuntimeFn::MapInsert, vec![map, k0, k1, v0, v1]),
                ])
            }
            (Intrinsic::MapRemove | Intrinsic::SetContains, [map, key]) => {
                let map_ty = self.operand_ty(map, ty);
                let k = match map_ty.as_builtin(self.db) {
                    Some((Builtin::Map | Builtin::Set, args)) => args[0],
                    _ => return Err("collections of this type"),
                };
                self.describe(map_ty)?;
                let map = word(&self.operand(map, map_ty)?)?;
                let key = self.operand(key, k)?;
                let [k0, k1] = self.pad(key);
                if intrinsic == Intrinsic::MapRemove {
                    return Ok(vec![self.runtime(RuntimeFn::MapRemove, vec![map, k0, k1])]);
                }
                let at = self.runtime(RuntimeFn::MapGet, vec![map, k0, k1]);
                let zero = self.constant(0);
                Ok(vec![self.cmp(Cond::Ne, at, zero)])
            }
            (Intrinsic::MapKeys | Intrinsic::MapValues, [map]) => {
                let map_ty = self.operand_ty(map, ty);
                self.describe(map_ty)?;
                let map = word(&self.operand(map, map_ty)?)?;
                let list = self.empty(ty, LIST_SIZE)?;
                let values = self.constant(i64::from(intrinsic == Intrinsic::MapValues));
                Ok(vec![
                    self.runtime(RuntimeFn::MapList, vec![map, list, values]),
                ])
            }
            (Intrinsic::ListAppend, [list, value]) => {
                let list_ty = self.operand_ty(list, ty);
                let element = element_of(self.db, list_ty)?;
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                let words = self.operand(value, element)?;
                let [w0, w1] = self.pad(words);
                Ok(vec![self.runtime(RuntimeFn::ListPush, vec![list, w0, w1])])
            }
            (Intrinsic::SignalMark, []) => {
                Ok(vec![self.runtime(RuntimeFn::SignalMark, Vec::new())])
            }
            (Intrinsic::SignalReset, [mark, ..]) => {
                let mark = word(&self.operand(mark, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::SignalReset,
                    args: vec![mark],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::SignalOn, [handler, base]) => {
                let handler_ty = self.operand_ty(handler, ty);
                let TyKind::Fn { params, .. } = handler_ty.kind(self.db) else {
                    return Err("signal handlers of this type");
                };
                let signal = params[0];
                let words = layout(self.db, self.program, signal)
                    .ok_or("signal handlers of this type")?
                    .words();
                if words > 1 {
                    return Err("signal handlers of this type");
                }
                let (types, parents) = signal_types(self.db, self.program, signal);
                let bytes: Vec<u8> = types.iter().flat_map(|t| t.to_le_bytes()).collect();
                let table = self.static_data(bytes);
                let [code, env] = self.operand(handler, handler_ty)?[..] else {
                    return Err("signal handlers of this type");
                };
                let packed = (types.len() as i64) << 32 | i64::from(parents) << 8 | words as i64;
                let packed = self.constant(packed);
                let base = word(&self.operand(base, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::SignalOn,
                    args: vec![code, env, table, packed, base],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::SignalEmit { qualifier }, [signal]) => {
                let signal_ty = self.operand_ty(signal, ty);
                let signal_layout = layout(self.db, self.program, signal_ty);
                let boxed = match signal_layout {
                    Some(Layout::Box) => true,
                    Some(Layout::Zero | Layout::Tag) => false,
                    _ => return Err("signals of this type"),
                };
                let words = self.operand(signal, signal_ty)?;
                let info = self.signal_info(signal_ty, boxed);
                let list = self.cell_list(signal_ty)?;
                let [w0, w1] = self.pad(words.clone());
                let qualifier = self.constant(i64::from(qualifier));
                let held = self.runtime(RuntimeFn::SignalEmit, vec![qualifier, list, w0, w1, info]);
                let (deliver, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: held,
                        then: deliver,
                        otherwise: done,
                    },
                    Some(deliver),
                );
                self.deliver(w0, info);
                self.count_words(signal_layout, signal_ty, &words, Self::release)?;
                self.end(Term::Jump(done), Some(done));
                Ok(Vec::new())
            }
            (Intrinsic::SignalDrain, []) => {
                let (head, take, done) = (self.new_block(), self.new_block(), self.new_block());
                self.end(Term::Jump(head), Some(head));
                let out = self.scratch();
                let list = self.runtime(RuntimeFn::SignalNext, vec![out]);
                let none = self.constant(SIGNAL_NONE as i64);
                let more = self.cmp(Cond::Ne, list, none);
                self.end(
                    Term::Branch {
                        cond: more,
                        then: take,
                        otherwise: done,
                    },
                    Some(take),
                );
                let w0 = self.load(out, 0);
                let info = self.load(out, 16);
                self.deliver(w0, info);
                self.end(Term::Jump(head), Some(done));
                Ok(Vec::new())
            }
            (Intrinsic::ScopeNew, [limit]) => {
                let limit = word(&self.operand(limit, int)?)?;
                Ok(vec![self.runtime(RuntimeFn::ScopeNew, vec![limit])])
            }
            (Intrinsic::ScopeStart, [scope, task, exempt]) => {
                let task_ty = self.operand_ty(task, int);
                let TyKind::Fn { result, .. } = task_ty.kind(self.db) else {
                    return Err("this operation of the runtime");
                };
                let results = layout(self.db, self.program, *result)
                    .ok_or("values of this type")?
                    .words();
                let scope = word(&self.operand(scope, int)?)?;
                let [code, env] = self.operand(task, task_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let exempt = word(&self.operand(exempt, int)?)?;
                let shift = self.constant(START_EXEMPT.trailing_zeros().into());
                let exempt = self.bin(LirBin::Shl, exempt, shift);
                let results = self.constant(results as i64);
                let flags = self.bin(LirBin::Or, exempt, results);
                self.runtime(RuntimeFn::ScopeStart, vec![scope, code, env, flags]);
                Ok(Vec::new())
            }
            (Intrinsic::ScopeNext, [scope]) => {
                let scope = word(&self.operand(scope, int)?)?;
                let next = self.runtime2(RuntimeFn::ScopeNext, vec![scope]);
                let (index, status) = (next[0], next[1]);
                let done = self.constant(SCOPE_DONE as i64);
                let is_done = self.cmp(Cond::Eq, index, done);
                let two = self.constant(2);
                let shifted = self.bin(LirBin::Shl, index, two);
                let packed = self.bin(LirBin::Or, shifted, status);
                let none = self.constant(-1);
                let out = self.reg();
                self.push(Inst::Select {
                    dst: out,
                    cond: is_done,
                    a: none,
                    b: packed,
                });
                Ok(vec![out])
            }
            (Intrinsic::ScopeResult, [scope, index]) => {
                let scope = word(&self.operand(scope, int)?)?;
                let index = word(&self.operand(index, int)?)?;
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                let out = self.runtime2(RuntimeFn::ScopeResult, vec![scope, index]);
                Ok(out[..words].to_vec())
            }
            (Intrinsic::ScopeCancel | Intrinsic::ScopeEnd, [scope]) => {
                let scope = word(&self.operand(scope, int)?)?;
                let func = match intrinsic {
                    Intrinsic::ScopeCancel => RuntimeFn::ScopeCancel,
                    _ => RuntimeFn::ScopeEnd,
                };
                self.push(Inst::CallRuntime {
                    func,
                    args: vec![scope],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::TxBegin, []) => Ok(vec![self.runtime(RuntimeFn::TxBegin, Vec::new())]),
            (Intrinsic::TxDepth, []) => Ok(vec![self.runtime(RuntimeFn::TxDepth, Vec::new())]),
            (Intrinsic::TxUnwind, [depth]) => {
                let depth = word(&self.operand(depth, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::TxUnwind,
                    args: vec![depth],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::TrapCaught(which), []) => {
                let which = self.constant(i64::from(which));
                Ok(vec![self.runtime(RuntimeFn::TrapCaught, vec![which])])
            }
            (Intrinsic::TrapCaughtText(which), []) => {
                let which = self.constant(i64::from(which));
                Ok(self.runtime2(RuntimeFn::TrapCaughtText, vec![which]))
            }
            (Intrinsic::TxCommit, []) => Ok(vec![self.runtime(RuntimeFn::TxCommit, Vec::new())]),
            (Intrinsic::TxAbort | Intrinsic::TxRetry | Intrinsic::TxThrow, []) => {
                let func = match intrinsic {
                    Intrinsic::TxAbort => RuntimeFn::TxAbort,
                    Intrinsic::TxRetry => RuntimeFn::TxRetry,
                    _ => RuntimeFn::TxThrow,
                };
                self.push(Inst::CallRuntime {
                    func,
                    args: Vec::new(),
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::TxConflicted | Intrinsic::SidePtr | Intrinsic::SideEnd, []) => {
                let offset = match intrinsic {
                    Intrinsic::TxConflicted => TX_CONFLICT_OFFSET,
                    Intrinsic::SidePtr => SIDE_PTR_OFFSET,
                    _ => SIDE_END_OFFSET,
                };
                let ctx = self.reg();
                self.push(Inst::Context { dst: ctx });
                Ok(vec![self.load(ctx, offset)])
            }
            (Intrinsic::SideReset, [ptr, end]) => {
                let ptr = word(&self.operand(ptr, int)?)?;
                let end = word(&self.operand(end, int)?)?;
                let ctx = self.reg();
                self.push(Inst::Context { dst: ctx });
                for (src, offset) in [(ptr, SIDE_PTR_OFFSET), (end, SIDE_END_OFFSET)] {
                    self.push(Inst::Store {
                        src,
                        addr: ctx,
                        offset,
                    });
                }
                Ok(Vec::new())
            }
            (Intrinsic::RefApply { op, ty: builtin }, [cell, k]) => {
                let op = match op {
                    BinOp::Add => REF_ADD,
                    BinOp::Sub => REF_SUB,
                    BinOp::Mul => REF_MUL,
                    _ => return Err("this operation of the runtime"),
                };
                let (bits, unsigned) = match builtin {
                    Builtin::Int => (64, false),
                    Builtin::Int8 => (8, false),
                    Builtin::Int16 => (16, false),
                    Builtin::Int32 => (32, false),
                    Builtin::UInt8 => (8, true),
                    Builtin::UInt16 => (16, true),
                    Builtin::UInt32 => (32, true),
                    Builtin::UInt64 => (64, true),
                    _ => return Err("this operation of the runtime"),
                };
                let width = if unsigned { bits | REF_UNSIGNED } else { bits };
                let k_ty = Ty::builtin(self.db, builtin);
                let k = word(&self.operand(k, k_ty)?)?;
                let list = self.cell_list(k_ty)?;
                let cell = self.cell_addr(cell)?;
                let op = self.constant(op as i64);
                let width = self.constant(width as i64);
                Ok(vec![self.runtime(
                    RuntimeFn::RefApply,
                    vec![cell, op, width, k, list],
                )])
            }
            (Intrinsic::RefSwap, [cell, value]) => {
                let list = self.cell_list(ty)?;
                let cell = self.cell_addr(cell)?;
                let words = self.operand(value, ty)?;
                let [w0, w1] = self.pad(words);
                let old = self.runtime2(RuntimeFn::RefSwap, vec![cell, list, w0, w1]);
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                Ok(old[..words].to_vec())
            }
            (Intrinsic::Sleep, [nanos]) => {
                let nanos = word(&self.operand(nanos, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::Sleep,
                    args: vec![nanos],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            _ => Err("this operation of the runtime"),
        }
    }

    /// 1 when two strings or bytes values hold the same bytes, else 0.
    /// Equal words are equal values, and a value of at most 15 bytes is
    /// always inline, so only two buffers of the same length need the
    /// runtime to compare.
    fn text_equals(&mut self, a: &[VReg], b: &[VReg]) -> Result<VReg, Unsupported> {
        let ([a0, a1], [b0, b1]) = (a, b) else {
            return Err("this conversion");
        };
        let (a0, a1, b0, b1) = (*a0, *a1, *b0, *b1);
        let out = self.reg();
        let same0 = self.cmp(Cond::Eq, a0, b0);
        let same1 = self.cmp(Cond::Eq, a1, b1);
        let same = self.bin(LirBin::And, same0, same1);
        let one = self.constant(1);
        let either = self.bin(LirBin::Or, a0, b0);
        let inline = self.bin(LirBin::And, either, one);
        let mask = self.constant(0xffff_ffff);
        let a_len = self.bin(LirBin::And, a1, mask);
        let b_len = self.bin(LirBin::And, b1, mask);
        let unequal = self.cmp(Cond::Ne, a_len, b_len);
        let known = self.bin(LirBin::Or, same, inline);
        let known = self.bin(LirBin::Or, known, unequal);
        let (fast, slow, done) = (self.new_block(), self.new_block(), self.new_block());
        self.end(
            Term::Branch {
                cond: known,
                then: fast,
                otherwise: slow,
            },
            Some(fast),
        );
        self.push(Inst::Move {
            dst: out,
            src: same,
        });
        self.end(Term::Jump(done), Some(slow));
        let equal = self.runtime(RuntimeFn::TextEquals, vec![a0, a1, b0, b1]);
        self.push(Inst::Move {
            dst: out,
            src: equal,
        });
        self.end(Term::Jump(done), Some(done));
        Ok(out)
    }

    /// Strings joined, each part borrowed: a string, bytes joined into
    /// bytes, a number written as text, or any other value as `show`
    /// writes it by its structure. The result has a reference of its own.
    fn concat(
        &mut self,
        parts: &[Operand<'db>],
        result: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        // Bytes join as they are into bytes, but are shown in a string.
        let raw_bytes = matches!(result.as_builtin(self.db), Some((Builtin::Bytes, _)));
        let db = self.db;
        let str_ty = Ty::builtin(db, Builtin::Str);
        // The text so far, and whether this code owns a reference to it.
        let mut text: Option<(Vec<VReg>, bool)> = None;
        for part in parts {
            let ty = self.operand_ty(part, str_ty);
            let words = self.operand(part, ty)?;
            let number = ty.as_builtin(db).and_then(|(b, _)| crate::shape::number(b));
            let (words, owned) = match (ty.as_builtin(db), number) {
                (Some((Builtin::Str, _)), _) => (words, false),
                (Some((Builtin::Bytes, _)), _) if raw_bytes => (words, false),
                (_, Some(number)) => {
                    let code = self.constant(number.code() as i64);
                    (
                        self.runtime2(RuntimeFn::TextShow, vec![word(&words)?, code]),
                        true,
                    )
                }
                // Any other value as `show` writes it by its structure.
                _ => {
                    let handle = self.value_shapes(ty)?;
                    let [w0, w1] = self.pad(words);
                    (
                        self.runtime2(RuntimeFn::ValueShow, vec![handle, w0, w1])
                            .to_vec(),
                        true,
                    )
                }
            };
            text = Some(match text {
                None => (words, owned),
                Some((so_far, owned_so_far)) => {
                    let mut args = so_far.clone();
                    args.extend(&words);
                    let joined = self.runtime2(RuntimeFn::TextConcat, args);
                    if owned_so_far {
                        self.count_text(&so_far, Self::release);
                    }
                    if owned {
                        self.count_text(&words, Self::release);
                    }
                    (joined, true)
                }
            });
        }
        let Some((words, owned)) = text else {
            return self.text_literal(b"");
        };
        if !owned {
            self.count_text(&words, Self::retain);
        }
        Ok(words)
    }

    /// Retains or releases the buffer of a string's words, if it has one.
    fn count_text(&mut self, words: &[VReg], op: fn(&mut Self, VReg)) {
        let str_ty = Ty::builtin(self.db, Builtin::Str);
        self.count_words(Some(Layout::Pair), str_ty, words, op)
            .expect("a string is counted");
    }

    /// Calls a runtime function with two results.
    fn runtime2(&mut self, func: RuntimeFn, args: Vec<VReg>) -> Vec<VReg> {
        let dsts = vec![self.reg(), self.reg()];
        self.push(Inst::CallRuntime {
            func,
            args,
            dsts: dsts.clone(),
        });
        dsts
    }

    /// Where a call of an instance goes: through its slot.
    fn slot(&self, callee: InstanceKey<'db>) -> CallTarget {
        CallTarget::Slot(slot_key(self.db, self.program, callee))
    }

    /// The address of a function value's code, of the function type `ty`,
    /// which is loaded with this function.
    fn code_addr(&mut self, code: InstanceKey<'db>, ty: Ty<'db>) -> Result<VReg, Unsupported> {
        let (params, returns) = self.value_words(ty)?;
        if !self.calls.contains(&code) {
            self.calls.push(code);
        }
        let dst = self.reg();
        self.push(Inst::FuncAddr {
            dst,
            func: self.slot(code),
            params,
            returns,
        });
        Ok(dst)
    }

    /// The words of the parameters, the environment's included, and of the
    /// result of a function value's code.
    fn value_words(&self, ty: Ty<'db>) -> Result<(u32, u32), Unsupported> {
        let TyKind::Fn { params, result, .. } = ty.kind(self.db) else {
            return Err("values of this type");
        };
        let mut words = 1;
        for &p in params {
            words += self.layout_of(p)?.words() as u32;
        }
        let returns = self.layout_of(*result)?.words() as u32;
        if returns > 2 {
            return Err("types of parameters or results");
        }
        Ok((words, returns))
    }

    /// The words of the value at a place.
    fn read(&mut self, place: &Place<'db>) -> Result<Vec<VReg>, Unsupported> {
        let db = self.db;
        let mut ty = self.local_ty(place.local);
        let mut values = self.operand(&Operand::Local(place.local), ty)?;
        for step in &place.path {
            let current = self.layout_of(ty)?;
            match step {
                Step::As(member) => {
                    let target = self.layout_of(*member)?;
                    values = match (current, target) {
                        (Layout::Union, Layout::Zero) | (Layout::Tag, Layout::Zero) => Vec::new(),
                        // Borrowed from the member box.
                        (Layout::Union, Layout::Pair | Layout::Closure) => {
                            self.member_words(values[1])
                        }
                        (Layout::Union, _) => vec![values[1]],
                        (Layout::Box, Layout::Box) => values,
                        _ => return Err("this conversion"),
                    };
                    ty = *member;
                }
                Step::Field(name) => {
                    let (slots, _) =
                        record_layout(db, self.program, ty).ok_or("records of this type")?;
                    let slot = slots
                        .iter()
                        .find(|s| s.name == *name)
                        .ok_or("records of this type")?;
                    let ptr = word(&values)?;
                    values = (0..slot.layout.words())
                        .map(|k| self.load(ptr, (slot.offset + 8 * k as u32) as i32))
                        .collect();
                    ty = slot.ty;
                }
                Step::Elem(i) => {
                    let index = self.constant(i64::from(*i));
                    values = self.element(word(&values)?, ty, index)?;
                    ty = element_of(db, ty)?;
                }
                Step::ElemBack(i) => {
                    let list = word(&values)?;
                    let len = self.load(list, LEN_OFFSET);
                    let from_end = self.constant(i64::from(*i) + 1);
                    let index = self.bin(LirBin::Sub, len, from_end);
                    values = self.element(list, ty, index)?;
                    ty = element_of(db, ty)?;
                }
                Step::Slice { .. } => return Err("this place"),
            }
        }
        Ok(values)
    }

    /// The type of the value at a place.
    fn place_ty(&self, place: &Place<'db>) -> Result<Ty<'db>, Unsupported> {
        let db = self.db;
        let mut ty = self.local_ty(place.local);
        for step in &place.path {
            ty = match step {
                Step::As(t) => *t,
                Step::Field(name) => crag_types::fields_of(db, self.program, ty)
                    .and_then(|fs| fs.into_iter().find(|(n, _)| n == name))
                    .map(|(_, t)| t)
                    .ok_or("records of this type")?,
                Step::Elem(_) | Step::ElemBack(_) => element_of(db, ty)?,
                Step::Slice { .. } => ty,
            };
        }
        Ok(ty)
    }

    /// Registers the descriptor of a record or collection type, which the
    /// runtime needs to free its boxes and to store its elements.
    fn describe(&mut self, ty: Ty<'db>) -> Result<(), Unsupported> {
        let index = type_index(ty) as u32;
        if self.types.iter().any(|(i, _)| *i == index) {
            return Ok(());
        }
        let Some(descriptor) = type_descriptor(self.db, self.program, ty) else {
            return Err(match ty.as_builtin(self.db) {
                Some((Builtin::Map | Builtin::Set, [key, ..]))
                    if !equal_by_words(self.db, self.program, *key) =>
                {
                    "maps with keys of this type"
                }
                Some(_) => "collections of this type",
                None => "records of this type",
            });
        };
        self.types.push((index, descriptor));
        Ok(())
    }

    /// Calls a runtime function with one result.
    fn runtime(&mut self, func: RuntimeFn, args: Vec<VReg>) -> VReg {
        let dst = self.reg();
        self.push(Inst::CallRuntime {
            func,
            args,
            dsts: vec![dst],
        });
        dst
    }

    /// A value's words as the two arguments of a runtime function, zero
    /// where it has fewer.
    fn pad(&mut self, words: Vec<VReg>) -> [VReg; 2] {
        let mut out = [VReg(0); 2];
        for (k, slot) in out.iter_mut().enumerate() {
            *slot = match words.get(k) {
                Some(&w) => w,
                None => self.constant(0),
            };
        }
        out
    }

    /// A new empty list or map of `size` bytes: its header, and zero for
    /// the rest (see `crag_abi`).
    fn empty(&mut self, ty: Ty<'db>, size: u32) -> Result<VReg, Unsupported> {
        self.describe(ty)?;
        let ptr = self.alloc(size, type_index(ty));
        let zero = self.constant(0);
        for offset in (LEN_OFFSET..size as i32).step_by(8) {
            self.push(Inst::Store {
                src: zero,
                addr: ptr,
                offset,
            });
        }
        Ok(ptr)
    }

    /// A map or set with the entries, each a key and, for a map, a value.
    fn map(
        &mut self,
        ty: Ty<'db>,
        key: Ty<'db>,
        value: Option<Ty<'db>>,
        entries: &[(Operand<'db>, Option<Operand<'db>>)],
    ) -> Result<VReg, Unsupported> {
        let mut words = Vec::new();
        for (k, v) in entries {
            let k = self.operand(k, key)?;
            let v = match (v, value) {
                (Some(v), Some(value)) => self.operand(v, value)?,
                _ => Vec::new(),
            };
            words.push((k, v));
        }
        let mut map = self.empty(ty, MAP_SIZE)?;
        for (k, v) in words {
            let [k0, k1] = self.pad(k);
            let [v0, v1] = self.pad(v);
            map = self.runtime(RuntimeFn::MapInsert, vec![map, k0, k1, v0, v1]);
        }
        // A key written twice releases the value it had first.
        self.dispose();
        Ok(map)
    }

    /// The words of element `index` of a list of type `ty`, borrowed.
    fn element(&mut self, list: VReg, ty: Ty<'db>, index: VReg) -> Result<Vec<VReg>, Unsupported> {
        let element = element_of(self.db, ty)?;
        self.describe(ty)?;
        let words = self.layout_of(element)?.words();
        let at = self.runtime(RuntimeFn::ListElem, vec![list, index]);
        Ok((0..words).map(|k| self.load(at, 8 * k as i32)).collect())
    }

    /// The `Option` of a map's value: the value at `at`, or `Empty` when
    /// `at` is null. A `boxed` value gets a reference of its own, which
    /// its member box takes.
    fn option(
        &mut self,
        at: VReg,
        value: Ty<'db>,
        ty: Ty<'db>,
        boxed: bool,
    ) -> Result<Vec<VReg>, Unsupported> {
        let db = self.db;
        let present = value.members(db);
        let empty = ty
            .members(db)
            .into_iter()
            .find(|m| !present.contains(m))
            .ok_or("this conversion")?;
        let out: Vec<VReg> = (0..self.layout_of(ty)?.words())
            .map(|_| self.reg())
            .collect();
        let (hit, miss, done) = (self.new_block(), self.new_block(), self.new_block());
        let term = Term::Branch {
            cond: at,
            then: hit,
            otherwise: miss,
        };
        self.end(term, Some(hit));
        let words = self.layout_of(value)?.words();
        let found: Vec<VReg> = (0..words).map(|k| self.load(at, 8 * k as i32)).collect();
        let layout = self.layout_of(value)?;
        if boxed != matches!(layout, Layout::Pair | Layout::Closure) {
            return Err("this conversion");
        }
        if boxed {
            self.count_words(Some(layout), value, &found, Self::retain)?;
        }
        let found = self.convert(found, value, ty)?;
        self.moves(&out, found)?;
        self.end(Term::Jump(done), Some(miss));
        let nothing = self.convert(Vec::new(), empty, ty)?;
        self.moves(&out, nothing)?;
        self.end(Term::Jump(done), Some(done));
        Ok(out)
    }

    /// Copies values into registers.
    fn moves(&mut self, dsts: &[VReg], values: Vec<VReg>) -> Result<(), Unsupported> {
        if dsts.len() != values.len() {
            return Err("this conversion");
        }
        for (&dst, src) in dsts.iter().zip(values) {
            self.push(Inst::Move { dst, src });
        }
        Ok(())
    }

    /// A value of `from` as a value of `to`: a member put into a union or
    /// taken out of it, or a record as its parent.
    fn convert(
        &mut self,
        values: Vec<VReg>,
        from: Ty<'db>,
        to: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let (f, t) = (self.layout_of(from)?, self.layout_of(to)?);
        let tag = type_index(self.member_of(from, to));
        Ok(match (f, t) {
            (Layout::Zero, Layout::Zero) => Vec::new(),
            (Layout::Zero, Layout::Tag) => vec![self.constant(tag)],
            (Layout::Zero, Layout::Union) => vec![self.constant(tag), self.constant(0)],
            (Layout::Imm(_) | Layout::Box, Layout::Union) => vec![self.constant(tag), values[0]],
            (Layout::Tag, Layout::Union) => vec![self.retag(values[0], from, to), self.constant(0)],
            (Layout::Union, Layout::Union) => vec![self.retag(values[0], from, to), values[1]],
            (Layout::Tag, Layout::Tag) => vec![self.retag(values[0], from, to)],
            (Layout::Box, Layout::Box) | (Layout::Pair, Layout::Pair) => values,
            (Layout::Union, Layout::Imm(_) | Layout::Box) => vec![values[1]],
            (Layout::Union, Layout::Tag) => vec![values[0]],
            (Layout::Union | Layout::Tag, Layout::Zero) => Vec::new(),
            // A function value fits where one of its type is expected,
            // or one that is not Pure.
            (Layout::Closure, Layout::Closure) if self.same_code(from, to) => values,
            (Layout::Closure, Layout::Closure) => return Err("conversions of function values"),
            // A member of two words goes into a member box, which takes
            // over its references, and comes out with references of its
            // own, giving up the box.
            (Layout::Pair | Layout::Closure, Layout::Union) => {
                let header = match f {
                    Layout::Pair => TEXT_BOX_HEADER,
                    _ => FUNCTION_BOX_HEADER,
                };
                let ptr = self.alloc(MEMBER_BOX_SIZE, header as i64);
                for (k, src) in values.into_iter().enumerate() {
                    let offset = (HEADER_SIZE + 8 * k as u32) as i32;
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset,
                    });
                }
                vec![self.constant(tag), ptr]
            }
            (Layout::Union, Layout::Pair | Layout::Closure) => {
                let words = self.member_words(values[1]);
                self.count_words(Some(t), to, &words, Self::retain)?;
                self.release(values[1]);
                words
            }
            _ => return Err("this conversion"),
        })
    }

    /// The two words of a union's member in the member box at `ptr`.
    fn member_words(&mut self, ptr: VReg) -> Vec<VReg> {
        (0..2)
            .map(|k| self.load(ptr, (HEADER_SIZE + 8 * k) as i32))
            .collect()
    }

    /// Whether values of two function types call the same code: their
    /// parameters and results are the same, if not whether they are Pure.
    fn same_code(&self, from: Ty<'db>, to: Ty<'db>) -> bool {
        match (from.kind(self.db), to.kind(self.db)) {
            (
                TyKind::Fn {
                    params: a,
                    result: r,
                    ..
                },
                TyKind::Fn {
                    params: b,
                    result: q,
                    ..
                },
            ) => a == b && r == q,
            _ => false,
        }
    }

    /// The member of the union `to` that a value of `from` is tagged
    /// with: the member it is a value of, which may be a parent of its
    /// type. A type test of a finer type reads the box's header.
    fn member_of(&self, from: Ty<'db>, to: Ty<'db>) -> Ty<'db> {
        let members = to.members(self.db);
        if members.contains(&from) {
            return from;
        }
        members
            .into_iter()
            .find(|&m| crag_types::is_subtype(self.db, self.program, from, m))
            .unwrap_or(from)
    }

    /// The tag of a union value of `from` as one of `to`, where a member of
    /// `from` may be part of a member of `to`.
    fn retag(&mut self, tag: VReg, from: Ty<'db>, to: Ty<'db>) -> VReg {
        let mut tag = tag;
        for member in from.members(self.db) {
            let target = self.member_of(member, to);
            if target == member {
                continue;
            }
            let (old, new) = (
                self.constant(type_index(member)),
                self.constant(type_index(target)),
            );
            let cond = self.cmp(Cond::Eq, tag, old);
            let dst = self.reg();
            self.push(Inst::Select {
                dst,
                cond,
                a: new,
                b: tag,
            });
            tag = dst;
        }
        tag
    }

    /// The machine operation of a number type.
    fn arith(&mut self, op: BinOp, ty: Builtin, a: VReg, b: VReg) -> Result<VReg, Unsupported> {
        let unsigned = matches!(
            ty,
            Builtin::UInt8 | Builtin::UInt16 | Builtin::UInt32 | Builtin::UInt64
        );
        let lir = match (ty, op) {
            (Builtin::Float, BinOp::Add) => LirBin::FAdd,
            (Builtin::Float, BinOp::Sub) => LirBin::FSub,
            (Builtin::Float, BinOp::Mul) => LirBin::FMul,
            (Builtin::Float, BinOp::Div) => LirBin::FDiv,
            (Builtin::Float, BinOp::Rem) => return Err("Float remainders"),
            (_, BinOp::Add) => LirBin::Add,
            (_, BinOp::Sub) => LirBin::Sub,
            (_, BinOp::Mul) => LirBin::Mul,
            (_, BinOp::Div) if unsigned => LirBin::UDiv,
            (_, BinOp::Div) => LirBin::SDiv,
            (_, BinOp::Rem) if unsigned => LirBin::URem,
            (_, BinOp::Rem) => LirBin::SRem,
        };
        let result = self.bin(lir, a, b);
        Ok(self.narrow(ty, result))
    }

    /// A 64-bit result wrapped to the width of a narrow integer type.
    fn narrow(&mut self, ty: Builtin, value: VReg) -> VReg {
        let (bits, signed) = match ty {
            Builtin::Int8 => (8, true),
            Builtin::Int16 => (16, true),
            Builtin::Int32 => (32, true),
            Builtin::UInt8 => (8, false),
            Builtin::UInt16 => (16, false),
            Builtin::UInt32 => (32, false),
            _ => return value,
        };
        if signed {
            let shift = self.constant(64 - bits);
            let up = self.bin(LirBin::Shl, value, shift);
            self.bin(LirBin::SShr, up, shift)
        } else {
            let mask = self.constant((1i64 << bits) - 1);
            self.bin(LirBin::And, value, mask)
        }
    }

    /// 1 if the operation overflows its type, else 0.
    fn overflows(&mut self, op: BinOp, ty: Builtin, a: VReg, b: VReg) -> Result<VReg, Unsupported> {
        let (least, greatest) = match ty {
            Builtin::Fixed(_) => (i64::MIN.into(), i64::MAX.into()),
            b => b.int_range().ok_or("overflow of this type")?,
        };
        if op == BinOp::Div {
            // Only the least value divided by -1 overflows.
            let min = self.constant(least as i64);
            let minus_one = self.constant(-1);
            let is_min = self.cmp(Cond::Eq, a, min);
            let is_minus_one = self.cmp(Cond::Eq, b, minus_one);
            return Ok(self.bin(LirBin::And, is_min, is_minus_one));
        }
        let wide = matches!(ty, Builtin::Int | Builtin::UInt64 | Builtin::Fixed(_));
        if wide {
            let unsigned = ty == Builtin::UInt64;
            let op = match (op, unsigned) {
                (BinOp::Add, false) => OverflowOp::SAdd,
                (BinOp::Add, true) => OverflowOp::UAdd,
                (BinOp::Sub, false) => OverflowOp::SSub,
                (BinOp::Sub, true) => OverflowOp::USub,
                (BinOp::Mul, false) => OverflowOp::SMul,
                (BinOp::Mul, true) => OverflowOp::UMul,
                _ => return Err("overflow of this operation"),
            };
            let dst = self.reg();
            self.push(Inst::Overflow { op, dst, a, b });
            return Ok(dst);
        }
        // Narrow operands cannot overflow 64 bits; the result is then
        // compared with the type's range.
        let lir = match op {
            BinOp::Add => LirBin::Add,
            BinOp::Sub => LirBin::Sub,
            BinOp::Mul => LirBin::Mul,
            _ => return Err("overflow of this operation"),
        };
        let result = self.bin(lir, a, b);
        let min = self.constant(least as i64);
        let max = self.constant(greatest as i64);
        let below = self.cmp(Cond::Lt, result, min);
        let above = self.cmp(Cond::Gt, result, max);
        Ok(self.bin(LirBin::Or, below, above))
    }

    // Terminators.

    fn terminator(&mut self, term: &Terminator<'db>, returns: usize) -> Result<(), Unsupported> {
        match term {
            Terminator::Jump(b) => self.end(Term::Jump(block(*b)), None),
            Terminator::Branch {
                cond,
                then,
                otherwise,
            } => {
                let value = self.operand(cond, self.mir.bool_ty)?;
                let t = self.constant(self.true_index);
                let holds = self.cmp(Cond::Eq, word(&value)?, t);
                let term = Term::Branch {
                    cond: holds,
                    then: block(*then),
                    otherwise: block(*otherwise),
                };
                self.end(term, None);
            }
            Terminator::Switch {
                place,
                cases,
                otherwise,
            } => self.switch(place, cases, block(*otherwise))?,
            Terminator::Call {
                func,
                args,
                dst,
                target,
                unwind,
                catch,
                ..
            } => {
                let args = self.arguments(*func, args)?;
                let dsts = self.locals[dst.index()].clone();
                self.layouts[dst.index()].ok_or("values of this type")?;
                let func = self.slot(*func);
                let handlers = handlers(unwind, catch);
                self.push(match handlers.is_empty() {
                    true => Inst::Call { func, args, dsts },
                    false => Inst::TryCall {
                        func,
                        args,
                        dsts,
                        handlers,
                    },
                });
                self.end(Term::Jump(block(*target)), None);
            }
            Terminator::TailCall { func, args, .. } => {
                let args = self.arguments(*func, args)?;
                let term = Term::TailCall {
                    func: self.slot(*func),
                    args,
                };
                self.end(term, None);
            }
            Terminator::CallValue {
                callee,
                args,
                dst,
                target,
                unwind,
                catch,
                ..
            } => {
                let (code, args) = self.value_arguments(callee, args)?;
                let dsts = self.locals[dst.index()].clone();
                self.layouts[dst.index()].ok_or("values of this type")?;
                let handlers = handlers(unwind, catch);
                self.push(match handlers.is_empty() {
                    true => Inst::CallIndirect {
                        callee: code,
                        args,
                        dsts,
                    },
                    false => Inst::TryCallIndirect {
                        callee: code,
                        args,
                        dsts,
                        handlers,
                    },
                });
                self.end(Term::Jump(block(*target)), None);
            }
            Terminator::TailCallValue { callee, args, .. } => {
                let (code, args) = self.value_arguments(callee, args)?;
                let term = Term::TailCallIndirect { callee: code, args };
                self.end(term, None);
            }
            Terminator::Return(op) => {
                let values = self.operand(op, self.mir.result)?;
                if values.len() != returns {
                    return Err("this conversion");
                }
                if let Some(cell) = self.cell {
                    self.keep(cell, op, &values)?;
                }
                self.end(Term::Return(values), None);
            }
            Terminator::Trap {
                kind,
                site,
                detail,
                catch,
            } => {
                // A trap raised again goes to the handler around, in this
                // function or past it.
                if let TrapKind::Rethrow = kind {
                    let term = match catch {
                        Some(handler) => Term::Jump(block(*handler)),
                        None => Term::Rethrow,
                    };
                    self.end(term, None);
                    return Ok(());
                }
                let kind = match kind {
                    TrapKind::Rethrow => unreachable!("raised again above"),
                    TrapKind::Overflow => AbiTrap::Overflow,
                    TrapKind::DivideByZero => AbiTrap::DivideByZero,
                    TrapKind::Index => AbiTrap::Index,
                    TrapKind::Hole => AbiTrap::Hole,
                    TrapKind::NoMatch => AbiTrap::NoMatch,
                    TrapKind::Error => AbiTrap::Error,
                    TrapKind::Unsupported => AbiTrap::Unsupported,
                    TrapKind::Expectation => AbiTrap::Expectation,
                    TrapKind::ConditionFailed => AbiTrap::ConditionFailed,
                };
                // The byte offset of the expression in the module's source,
                // with the detail it names in the upper half.
                let position = site.and_then(|e| self.positions.get(e.index()).map(|r| r.start));
                if let Some(at) = position {
                    let origin = self.origin(at);
                    self.origins.push(origin);
                }
                let word = |this: &mut Self| -> u64 {
                    let Some(at) = position else {
                        return NO_POSITION;
                    };
                    let index = detail.as_ref().map_or(0, |d| {
                        this.details.push(d.clone());
                        this.details.len() as u64
                    });
                    u64::from(at) | index << 32
                };
                let term = match (catch, detail) {
                    (Some(handler), _) => Term::Caught {
                        kind,
                        position: word(self),
                        handler: block(*handler),
                    },
                    (None, Some(_)) => Term::Raise {
                        kind,
                        position: word(self),
                    },
                    (None, None) => Term::Trap { kind, position },
                };
                self.end(term, None);
            }
        }
        Ok(())
    }

    /// Keeps the value the code of a module-level value gives in its cell,
    /// with a reference of the cell's own, and marks the cell full.
    fn keep(
        &mut self,
        cell: SlotKey,
        op: &Operand<'db>,
        values: &[VReg],
    ) -> Result<(), Unsupported> {
        let addr = self.reg();
        self.push(Inst::CellAddr { dst: addr, cell });
        for (i, &src) in values.iter().enumerate() {
            let offset = CELL_VALUE_OFFSET + 8 * i as i32;
            self.push(Inst::Store { src, addr, offset });
        }
        if let Operand::Local(local) = op {
            self.count(*local, Self::retain)?;
        }
        let full = self.constant(CELL_FULL as i64);
        self.push(Inst::Store {
            src: full,
            addr,
            offset: CELL_STATE_OFFSET,
        });
        Ok(())
    }

    /// The entry of a module-level value's code: the value in its cell,
    /// once computed. Otherwise the code that computes it runs, which moves
    /// from block 0 to a block of its own; a trap there leaves the cell
    /// empty.
    fn cell_entry(&mut self, cell: SlotKey, returns: usize) {
        let compute = self.new_block();
        self.blocks[compute.0 as usize] = self.blocks[0].take();
        // MIR's entry block is no branch target, so nothing jumps to the
        // code where it was.
        debug_assert!(self.blocks.iter().flatten().all(|block| match block.term {
            Term::Jump(b) => b.0 != 0,
            Term::Branch {
                then, otherwise, ..
            } => then.0 != 0 && otherwise.0 != 0,
            _ => true,
        }));
        let read = self.new_block();
        self.current = (0, Vec::new());
        let addr = self.reg();
        self.push(Inst::CellAddr { dst: addr, cell });
        let state = self.reg();
        self.push(Inst::Load {
            dst: state,
            addr,
            offset: CELL_STATE_OFFSET,
        });
        let full = self.constant(CELL_FULL as i64);
        let is_full = self.cmp(Cond::Eq, state, full);
        self.end(
            Term::Branch {
                cond: is_full,
                then: read,
                otherwise: compute,
            },
            Some(read),
        );
        // The caller gets a reference of its own.
        let words: Vec<VReg> = (0..returns)
            .map(|i| {
                let dst = self.reg();
                let offset = CELL_VALUE_OFFSET + 8 * i as i32;
                self.push(Inst::Load { dst, addr, offset });
                dst
            })
            .collect();
        let result = layout(self.db, self.program, self.mir.result);
        match self.count_words(result, self.mir.result, &words, Self::retain) {
            Ok(()) => self.end(Term::Return(words), None),
            Err(what) => self.unsupported(what),
        }
    }

    /// The words of a call's arguments, laid out for the callee's
    /// parameters. A builtin of the prelude has no code yet. The code of a
    /// default takes the parameters before it, so its arguments are the
    /// first of its function's; a field's takes none.
    fn arguments(
        &mut self,
        func: InstanceKey<'db>,
        args: &[Operand<'db>],
    ) -> Result<Vec<VReg>, Unsupported> {
        let db = self.db;
        let Owner::Item(item) = *func.owner(db) else {
            return Err("calls of tests");
        };
        if *func.entry(db) == Entry::Body
            && hir_body(db, self.program, Owner::Item(item)).root.is_none()
        {
            return Err("builtin functions");
        }
        // The conditions of a type take a value of the instance's type.
        if *func.entry(db) == Entry::Check {
            let identity = crag_hir::type_identity(db, self.program, item);
            let ty = Ty::new(db, TyKind::Named(identity, func.args(db).clone()));
            let mut words = Vec::new();
            for arg in args {
                words.extend(self.operand(arg, ty)?);
            }
            if !self.calls.contains(&func) {
                self.calls.push(func);
            }
            return Ok(words);
        }
        let params = match args.is_empty() {
            true => &[][..],
            false => &signature(db, self.program, item).params[..],
        };
        let mut words = Vec::new();
        for (arg, param) in args.iter().zip(params) {
            // An instance's parameters have its type arguments in place.
            let ty = match func.args(db).is_empty() {
                true => param.ty,
                false => crag_types::subst(db, self.program, param.ty, item, func.args(db)),
            };
            words.extend(self.operand(arg, ty)?);
        }
        if !self.calls.contains(&func) {
            self.calls.push(func);
        }
        Ok(words)
    }

    /// The code address of a function value, and the words of a call's
    /// arguments for it: the environment, then the arguments laid out for
    /// the value's parameters.
    fn value_arguments(
        &mut self,
        callee: &Operand<'db>,
        args: &[Operand<'db>],
    ) -> Result<(VReg, Vec<VReg>), Unsupported> {
        let fn_ty = self.operand_ty(callee, Ty::error(self.db));
        let TyKind::Fn { params, .. } = fn_ty.kind(self.db) else {
            return Err("calls of values of this type");
        };
        let value = self.operand(callee, fn_ty)?;
        let [code, env] = value[..] else {
            return Err("calls of values of this type");
        };
        let mut words = vec![env];
        for (arg, &param) in args.iter().zip(params) {
            words.extend(self.operand(arg, param)?);
        }
        Ok((code, words))
    }

    /// Tests the runtime type of the value at a place, case by case.
    fn switch(
        &mut self,
        place: &Place<'db>,
        cases: &[(Ty<'db>, BlockId)],
        otherwise: LirBlockId,
    ) -> Result<(), Unsupported> {
        let db = self.db;
        let values = self.read(place)?;
        let ty = self.place_ty(place)?;
        let members = ty.members(db);
        let shape = self.layout_of(ty)?;
        for &(case, target) in cases {
            // Every value of the place's type has the case's.
            if crag_types::is_subtype(db, self.program, ty, case) {
                self.end(Term::Jump(block(target)), None);
                return Ok(());
            }
            let target = block(target);
            let next = self.new_block();
            let exact = members.contains(&case);
            match shape {
                Layout::Tag | Layout::Union if exact => {
                    let index = self.constant(type_index(case));
                    let same = self.cmp(Cond::Eq, values[0], index);
                    let term = Term::Branch {
                        cond: same,
                        then: target,
                        otherwise: next,
                    };
                    self.end(term, Some(next));
                }
                // A finer record type: the box's header has the value's
                // own type.
                Layout::Union => {
                    let member = members
                        .iter()
                        .copied()
                        .find(|&m| crag_types::is_subtype(db, self.program, case, m))
                        .ok_or("this type test")?;
                    let index = self.constant(type_index(member));
                    let same = self.cmp(Cond::Eq, values[0], index);
                    let header = self.new_block();
                    let term = Term::Branch {
                        cond: same,
                        then: header,
                        otherwise: next,
                    };
                    self.end(term, Some(header));
                    self.test_header(values[1], case, target, next);
                }
                Layout::Box => self.test_header(values[0], case, target, next),
                _ => return Err("this type test"),
            }
        }
        self.end(Term::Jump(otherwise), None);
        Ok(())
    }

    /// Ends the block with a test whether the box is of a type that fits
    /// `ty`; the following code goes to `miss`.
    fn test_header(&mut self, ptr: VReg, ty: Ty<'db>, hit: LirBlockId, miss: LirBlockId) {
        let index = self.load(ptr, TYPE_INDEX_OFFSET);
        let indices = subtypes(self.db, self.program, ty);
        self.test_index(index, &indices, hit, miss);
        self.current = (miss.0 as usize, Vec::new());
    }
}

fn block(b: BlockId) -> LirBlockId {
    LirBlockId(b.0)
}

/// The element type of a list type.
fn element_of<'db>(db: &'db dyn Db, ty: Ty<'db>) -> Result<Ty<'db>, Unsupported> {
    match ty.as_builtin(db) {
        Some((Builtin::List, [element])) => Ok(*element),
        _ => Err("collections of this type"),
    }
}

fn word(values: &[VReg]) -> Result<VReg, Unsupported> {
    match values {
        [one] => Ok(*one),
        _ => Err("this conversion"),
    }
}

fn compare_cond(op: CmpOp, ty: Builtin) -> Result<Cond, Unsupported> {
    let unsigned = matches!(
        ty,
        Builtin::UInt8 | Builtin::UInt16 | Builtin::UInt32 | Builtin::UInt64 | Builtin::CodePoint
    );
    Ok(match (ty, op) {
        (Builtin::Str | Builtin::Bytes, _) => return Err("orderings of strings and bytes"),
        (Builtin::Float, CmpOp::Eq) => Cond::FEq,
        (Builtin::Float, CmpOp::Ne) => Cond::FNe,
        (Builtin::Float, CmpOp::Lt) => Cond::FLt,
        (Builtin::Float, CmpOp::Le) => Cond::FLe,
        (Builtin::Float, CmpOp::Gt) => Cond::FGt,
        (Builtin::Float, CmpOp::Ge) => Cond::FGe,
        (_, CmpOp::Eq) => Cond::Eq,
        (_, CmpOp::Ne) => Cond::Ne,
        (_, CmpOp::Lt) if unsigned => Cond::ULt,
        (_, CmpOp::Le) if unsigned => Cond::ULe,
        (_, CmpOp::Gt) if unsigned => Cond::UGt,
        (_, CmpOp::Ge) if unsigned => Cond::UGe,
        (_, CmpOp::Lt) => Cond::Lt,
        (_, CmpOp::Le) => Cond::Le,
        (_, CmpOp::Gt) => Cond::Gt,
        (_, CmpOp::Ge) => Cond::Ge,
    })
}
