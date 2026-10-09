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
//! allocated, retained and released through the runtime.
//!
//! What code generation does not handle yet, such as strings and
//! collections, ends its block with a trap and is listed.

use crag_abi::{TYPE_INDEX_OFFSET, TrapKind as AbiTrap};
use crag_codegen::{
    BinOp as LirBin, Block as LirBlock, BlockId as LirBlockId, Cond, FuncId, Inst, LirFunction,
    OverflowOp, RuntimeFn, Term, VReg,
};
use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{Owner, Program, hir_body};
use crag_mir::{
    BinOp, BlockId, CmpOp, Constant, InstanceKey, Local, MirBody, Operand, Place, Rvalue,
    Statement, Terminator, TrapKind,
};
use crag_types::{Builtin, Step, Ty, TyKind, prelude_item, signature};

use crate::layout::{Layout, layout, record_layout, subtypes, type_index};

/// The LIR of a body, with what it could not lower.
pub struct Lowered<'db> {
    pub lir: LirFunction,
    pub unsupported: Vec<&'static str>,
    /// The functions it calls.
    pub calls: Vec<InstanceKey<'db>>,
}

/// The function an instance is loaded as.
pub fn func_id(instance: InstanceKey<'_>) -> FuncId {
    FuncId(instance.as_id().index())
}

type Unsupported = &'static str;

pub fn lower_to_lir<'db>(db: &'db dyn Db, program: Program, mir: &MirBody<'db>) -> Lowered<'db> {
    let named = |name: &str| {
        prelude_item(db, program, name).map(|i| Ty::new(db, TyKind::Named(i, Vec::new())))
    };
    let mut l = Lower {
        db,
        program,
        mir,
        vregs: 0,
        locals: Vec::new(),
        layouts: Vec::new(),
        blocks: vec![None; mir.blocks.len()],
        current: (0, Vec::new()),
        unsupported: Vec::new(),
        calls: Vec::new(),
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
                term: Term::Trap(AbiTrap::Unsupported),
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
    }
}

struct Lower<'a, 'db> {
    db: &'db dyn Db,
    program: Program,
    mir: &'a MirBody<'db>,
    vregs: u32,
    /// The registers of each local.
    locals: Vec<Vec<VReg>>,
    layouts: Vec<Option<Layout>>,
    /// MIR block `i` is LIR block `i`; tests add more.
    blocks: Vec<Option<LirBlock>>,
    current: (usize, Vec<Inst>),
    unsupported: Vec<Unsupported>,
    calls: Vec<InstanceKey<'db>>,
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
        self.end(Term::Trap(AbiTrap::Unsupported), None);
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
            Statement::Retain(local) => self.count(*local, RuntimeFn::Retain),
            Statement::Release(local) => self.count(*local, RuntimeFn::Release),
            Statement::Poll => {
                self.push(Inst::Poll);
                Ok(())
            }
        }
    }

    /// Retains or releases the box a local holds, if it holds one.
    fn count(&mut self, local: Local, func: RuntimeFn) -> Result<(), Unsupported> {
        let regs = self.locals[local.index()].clone();
        match self.layouts[local.index()] {
            Some(Layout::Box) => {
                self.push(Inst::CallRuntime {
                    func,
                    args: regs,
                    dsts: Vec::new(),
                });
                Ok(())
            }
            Some(Layout::Union) => {
                let members = self.local_ty(local).members(self.db);
                let mut boxed = Vec::new();
                for m in members {
                    if self.layout_of(m)? == Layout::Box {
                        boxed.extend(subtypes(self.db, self.program, m));
                    }
                }
                let (call, done) = (self.new_block(), self.new_block());
                self.test_index(regs[0], &boxed, call, done);
                self.current = (call.0 as usize, Vec::new());
                self.push(Inst::CallRuntime {
                    func,
                    args: vec![regs[1]],
                    dsts: Vec::new(),
                });
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            Some(Layout::Pair) => Err("strings, bytes and closures"),
            _ => Ok(()),
        }
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
                let mut values = Vec::new();
                for (name, op) in fields {
                    let slot = slots
                        .iter()
                        .find(|s| s.name == *name)
                        .ok_or("records of this type")?;
                    values.push((slot.offset, self.operand(op, slot.ty)?));
                }
                let size = self.constant(i64::from(size));
                let index = self.constant(type_index(*record));
                let ptr = self.reg();
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::Alloc,
                    args: vec![size, index],
                    dsts: vec![ptr],
                });
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
            Rvalue::List(_)
            | Rvalue::Map(_)
            | Rvalue::Len(_)
            | Rvalue::Index { .. }
            | Rvalue::MapGet { .. }
            | Rvalue::Slice { .. } => Err("collections"),
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
                        .map(|k| {
                            let dst = self.reg();
                            self.push(Inst::Load {
                                dst,
                                addr: ptr,
                                offset: (slot.offset + 8 * k as u32) as i32,
                            });
                            dst
                        })
                        .collect();
                    ty = slot.ty;
                }
                Step::Elem(_) | Step::ElemBack(_) | Step::Slice { .. } => {
                    return Err("collections");
                }
            }
        }
        Ok(values)
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
            Terminator::Trap { kind, .. } => {
                let kind = match kind {
                    TrapKind::Overflow => AbiTrap::Overflow,
                    TrapKind::DivideByZero => AbiTrap::DivideByZero,
                    TrapKind::Index => AbiTrap::Index,
                    TrapKind::Hole => AbiTrap::Hole,
                    TrapKind::NoMatch => AbiTrap::NoMatch,
                    TrapKind::Error => AbiTrap::Error,
                    TrapKind::Unsupported => AbiTrap::Unsupported,
                };
                self.end(Term::Trap(kind), None);
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
        let mut ty = self.local_ty(place.local);
        for step in &place.path {
            ty = match step {
                Step::As(t) => *t,
                Step::Field(name) => crag_types::fields_of(db, self.program, ty)
                    .and_then(|fs| fs.into_iter().find(|(n, _)| n == name))
                    .map(|(_, t)| t)
                    .ok_or("records of this type")?,
                _ => return Err("collections"),
            };
        }
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
        let index = self.reg();
        self.push(Inst::Load {
            dst: index,
            addr: ptr,
            offset: TYPE_INDEX_OFFSET,
        });
        let indices = subtypes(self.db, self.program, ty);
        self.test_index(index, &indices, hit, miss);
        self.current = (miss.0 as usize, Vec::new());
    }
}

fn block(b: BlockId) -> LirBlockId {
    LirBlockId(b.0)
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
