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
//! What code generation does not handle yet, such as strings, ends its
//! block with a trap and is listed.

use std::ops::Range;

use crag_abi::{
    COUNT_OFFSET, HEAP_OFFSET, LEN_OFFSET, LIST_SIZE, MAP_SIZE, PAGE_FREE_OFFSET, PAGE_USED_OFFSET,
    TYPE_INDEX_OFFSET, TrapKind as AbiTrap, TypeDescriptor, size_class,
};
use crag_codegen::{
    BinOp as LirBin, Block as LirBlock, BlockId as LirBlockId, Cond, FuncId, Inst, LirFunction,
    OverflowOp, RuntimeFn, Term, VReg,
};
use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{Owner, Program, hir_body, lower_body};
use crag_mir::{
    BinOp, BlockId, CmpOp, Constant, InstanceKey, Local, MirBody, Operand, Place, Rvalue,
    Statement, Terminator, TrapKind,
};
use crag_types::{Builtin, Step, Ty, TyKind, prelude_item, signature};

use crate::layout::{
    Layout, boxed_indices, equal_by_words, layout, record_layout, subtypes, type_descriptor,
    type_index,
};

/// The LIR of a body, with what it could not lower.
pub struct Lowered<'db> {
    pub lir: LirFunction,
    pub unsupported: Vec<&'static str>,
    /// The functions it calls.
    pub calls: Vec<InstanceKey<'db>>,
    /// The types of the boxes it allocates, by type index, with their
    /// descriptors.
    pub types: Vec<(u32, TypeDescriptor)>,
}

/// The function an instance is loaded as.
pub fn func_id(instance: InstanceKey<'_>) -> FuncId {
    FuncId(instance.as_id().index())
}

type Unsupported = &'static str;

/// Lowers the MIR of a body of `owner`, whose source map gives the
/// positions of traps.
pub fn lower_to_lir<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    mir: &MirBody<'db>,
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
        true_index: named("True").map_or(-1, type_index),
        false_index: named("False").map_or(-1, type_index),
    };
    for decl in &mir.locals {
        let layout = layout(db, program, decl.ty);
        let words = layout.map_or(0, Layout::words);
        let regs: Vec<VReg> = (0..words).map(|_| l.reg()).collect();
        if layout == Some(Layout::Box) {
            l.tracked.extend(&regs);
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
        },
        unsupported: l.unsupported,
        calls: l.calls,
        types: l.types,
    }
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
    true_index: i64,
    false_index: i64,
}

impl<'a, 'db> Lower<'a, 'db> {
    fn reg(&mut self) -> VReg {
        self.vregs += 1;
        VReg(self.vregs - 1)
    }

    fn push(&mut self, inst: Inst) {
        self.current.1.push(inst);
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
            Constant::Str(_) | Constant::Bytes(_) => return Err("strings and bytes"),
        })
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
            Statement::Release(local) => self.count(*local, Self::release),
            Statement::Poll => {
                self.push(Inst::Poll);
                Ok(())
            }
        }
    }

    /// Retains or releases the box a local holds, if it holds one.
    fn count(&mut self, local: Local, op: fn(&mut Self, VReg)) -> Result<(), Unsupported> {
        let regs = self.locals[local.index()].clone();
        match self.layouts[local.index()] {
            Some(Layout::Box) => {
                op(self, regs[0]);
                Ok(())
            }
            Some(Layout::Union) => {
                let boxed = boxed_indices(self.db, self.program, self.local_ty(local))
                    .ok_or("values of this type")?;
                let boxed: Vec<i64> = boxed.into_iter().map(i64::from).collect();
                let (call, done) = (self.new_block(), self.new_block());
                self.test_index(regs[0], &boxed, call, done);
                self.current = (call.0 as usize, Vec::new());
                op(self, regs[1]);
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            Some(Layout::Pair) => Err("strings, bytes and closures"),
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
            func: RuntimeFn::Release,
            args: vec![ptr],
            dsts: Vec::new(),
        });
        self.end(Term::Jump(done), Some(done));
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
                let cond = compare_cond(*op, *b)?;
                let flag = self.cmp(cond, word(&x)?, word(&y)?);
                Ok(vec![self.bool_of(flag)])
            }
            Rvalue::Record { ty: record, fields } => {
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
            Rvalue::MapGet { map, key } => {
                let map_ty = self.place_ty(map)?;
                let Some((Builtin::Map, &[k, v])) = map_ty.as_builtin(self.db) else {
                    return Err("collections of this type");
                };
                self.describe(map_ty)?;
                let ptr = word(&self.read(map)?)?;
                let key = self.operand(key, k)?;
                let [k0, k1] = self.pad(key);
                let at = self.runtime(RuntimeFn::MapGet, vec![ptr, k0, k1]);
                self.option(at, v, ty)
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
            Rvalue::Concat(_) => Err("strings and bytes"),
            Rvalue::Global(_) => Err("module-level values"),
        }
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
                Some(_) => "collections holding strings, bytes or closures",
                None => "records holding strings, bytes or closures",
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
    /// `at` is null.
    fn option(&mut self, at: VReg, value: Ty<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
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
        let found = (0..words).map(|k| self.load(at, 8 * k as i32)).collect();
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
        Ok(match (f, t) {
            (Layout::Zero, Layout::Zero) => Vec::new(),
            (Layout::Zero, Layout::Tag) => vec![self.constant(type_index(from))],
            (Layout::Zero, Layout::Union) => {
                vec![self.constant(type_index(from)), self.constant(0)]
            }
            (Layout::Imm(_) | Layout::Box, Layout::Union) => {
                vec![self.constant(type_index(from)), values[0]]
            }
            (Layout::Tag, Layout::Union) => vec![values[0], self.constant(0)],
            (Layout::Union, Layout::Union) | (Layout::Tag, Layout::Tag) => values,
            (Layout::Box, Layout::Box) => values,
            (Layout::Union, Layout::Imm(_) | Layout::Box) => vec![values[1]],
            (Layout::Union, Layout::Tag) => vec![values[0]],
            (Layout::Union | Layout::Tag, Layout::Zero) => Vec::new(),
            _ => return Err("this conversion"),
        })
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
                ..
            } => {
                let args = self.arguments(*func, args)?;
                let dsts = self.locals[dst.index()].clone();
                self.layouts[dst.index()].ok_or("values of this type")?;
                self.push(Inst::Call {
                    func: func_id(*func),
                    args,
                    dsts,
                });
                self.end(Term::Jump(block(*target)), None);
            }
            Terminator::TailCall { func, args, .. } => {
                let args = self.arguments(*func, args)?;
                let term = Term::TailCall {
                    func: func_id(*func),
                    args,
                };
                self.end(term, None);
            }
            Terminator::Return(op) => {
                let values = self.operand(op, self.mir.result)?;
                if values.len() != returns {
                    return Err("this conversion");
                }
                self.end(Term::Return(values), None);
            }
            Terminator::Trap { kind, site } => {
                let kind = match kind {
                    TrapKind::Overflow => AbiTrap::Overflow,
                    TrapKind::DivideByZero => AbiTrap::DivideByZero,
                    TrapKind::Index => AbiTrap::Index,
                    TrapKind::Hole => AbiTrap::Hole,
                    TrapKind::NoMatch => AbiTrap::NoMatch,
                    TrapKind::Error => AbiTrap::Error,
                    TrapKind::Unsupported => AbiTrap::Unsupported,
                };
                // The byte offset of the expression in the module's source.
                let position = site.and_then(|e| self.positions.get(e.index()).map(|r| r.start));
                self.end(Term::Trap { kind, position }, None);
            }
        }
        Ok(())
    }

    /// The words of a call's arguments, laid out for the callee's
    /// parameters. A builtin of the prelude has no code yet.
    fn arguments(
        &mut self,
        func: InstanceKey<'db>,
        args: &[Operand<'db>],
    ) -> Result<Vec<VReg>, Unsupported> {
        let db = self.db;
        let Owner::Item(item) = *func.owner(db) else {
            return Err("calls of tests");
        };
        if hir_body(db, self.program, Owner::Item(item)).root.is_none() {
            return Err("builtin functions");
        }
        let sig = signature(db, self.program, item);
        let mut words = Vec::new();
        for (arg, param) in args.iter().zip(&sig.params) {
            words.extend(self.operand(arg, param.ty)?);
        }
        if !self.calls.contains(&func) {
            self.calls.push(func);
        }
        Ok(words)
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
        (Builtin::Str | Builtin::Bytes, _) => return Err("strings and bytes"),
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
