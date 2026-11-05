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
    BUFFER_HEADER, CELL_FULL, CELL_STATE_OFFSET, CELL_VALUE_OFFSET, COUNT_OFFSET, CountedField,
    FUNCTION_BOX_HEADER, HEADER_SIZE, HEAP_OFFSET, HandlerKind, INLINE_TEXT_MAX, INLINED_POSITION,
    InlinedCode, LEN_OFFSET, LIST_SIZE, MAP_SIZE, MEMBER_BOX_SIZE, NO_POSITION, NativeSymbol,
    PAGE_FREE_OFFSET, PAGE_USED_OFFSET, REF_ADD, REF_CELL_SIZE, REF_MUL, REF_SUB, REF_UNSIGNED,
    SCOPE_DONE, SIDE_END_OFFSET, SIDE_PTR_OFFSET, SIGNAL_NONE, START_EXEMPT, STATIC_COUNT,
    TEXT_BOX_HEADER, TEXT_LEN_MAX, TX_CONFLICT_OFFSET, TYPE_INDEX_OFFSET, TrapKind as AbiTrap,
    TrapOrigin, TypeDescriptor, c_kind, inline_text, size_class, threading,
};
use crag_codegen::{
    BinOp as LirBin, Block as LirBlock, BlockId as LirBlockId, CallTarget, Cond, FuncId, Inst,
    LirFunction, OverflowOp, RuntimeFn, SlotKey, Term, UnOp, VReg,
};
use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{ExprId, ItemId, Name, Owner, Program, Threading, hir_body, lower_body};
use crag_mir::{
    BUDGET, BinOp, BlockId, CastOp, ClosurePlacement, CmpOp, Constant, Entry, InstanceKey,
    Intrinsic, Local, LocalDecl, MirBody, Operand, Place, Rvalue, Statement, TREE, TREE_HASH,
    Terminator, Tier, TrapKind, WIRE,
};
use crag_types::{Builtin, CForm, Step, Ty, TyKind, prelude_item, signature};

use crate::boxes::{BoxForm, box_form, member_slots, rebase, select, span};
use crate::flat::MAX_FLAT_SIZE;
use crate::layout::{
    Layout, boxed_indices, deferred, is_text, layout, signal_types, subtypes, type_descriptor,
    type_index, word_keys,
};
use crate::slot_key;
use crate::split::{
    Form, NicheTest, Slot, SlotKind, UnionTag, element_form, element_storage, flat_params,
    flat_result, form, place_form, ref_storage, storage,
};

mod boxing;
mod convert;
mod count;
mod form;
mod intrinsic;
mod place;
mod rvalue;
mod terminator;

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
    /// The calls inlined into it (Implementation Plan §11.10.1).
    pub inlined: Vec<InlinedCode>,
}

/// A statement's step, for the debugger: where the statement starts and
/// the named locals whose words `rt_step` gets, in order.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct StepInfo<'db> {
    /// In the module of the innermost of `inlined`, else of the function.
    pub position: Option<u32>,
    /// The functions whose code was inlined where the step is, innermost
    /// first.
    pub inlined: Vec<InstanceKey<'db>>,
    /// The named locals whose words it passes, and whether each is split.
    pub locals: Vec<(Name<'db>, Ty<'db>, bool)>,
}

/// The function an instance is loaded as.
pub fn func_id(instance: InstanceKey<'_>) -> FuncId {
    FuncId(instance.as_id().index())
}

type Unsupported = &'static str;

/// A parameter that passes by value: the words of its storage form, its
/// bytes and its slots.
type Incoming = (Vec<VReg>, u32, Vec<Slot>);

/// Lowers the MIR of an instance, whose owner's source map gives the
/// positions of traps and steps. The code of a module-level value keeps
/// the value in `cell` (§11.6.2). Flat records pass to and from it by
/// value as `flat_params` and `flat_result` say (Plan §11.10.10). With
/// `direct`, calls go straight to their callees, as in release code.
pub fn lower_to_lir<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    mir: &MirBody<'db>,
    cell: Option<SlotKey>,
    direct: bool,
) -> Lowered<'db> {
    let owner = *instance.owner(db);
    let func = func_id(instance);
    let flat = flat_params(db, program, instance);
    let result = flat_result(db, program, instance).as_ref();
    let named = |name: &str| {
        prelude_item(db, program, name).map(|i| Ty::new(db, TyKind::Named(i, Vec::new())))
    };
    let mut l = Lower {
        db,
        program,
        instance,
        mir,
        direct,
        positions: &lower_body(db, program, owner).source_map.exprs,
        name_at: lower_body(db, program, owner).source_map.name.start,
        vregs: 0,
        locals: Vec::new(),
        layouts: Vec::new(),
        forms: Vec::new(),
        blocks: vec![None; mir.blocks.len()],
        current: (0, Vec::new()),
        catch: None,
        unsupported: Vec::new(),
        calls: Vec::new(),
        types: Vec::new(),
        tracked: Vec::new(),
        data: Vec::new(),
        true_index: named("True").map_or(-1, |t| type_index(db, program, t)),
        false_index: named("False").map_or(-1, |t| type_index(db, program, t)),
        cell,
        scratch: None,
        func,
        steps: Vec::new(),
        source: owner.module(db).file(db).text(db),
        origins: Vec::new(),
        details: Vec::new(),
        scopes: mir
            .inlined
            .iter()
            .map(|call| {
                let owner = *call.func.owner(db);
                let lowered = lower_body(db, program, owner);
                Scope {
                    positions: &lowered.source_map.exprs,
                    name_at: lowered.source_map.name.start,
                    source: owner.module(db).file(db).text(db),
                }
            })
            .collect(),
        scope: None,
        block_scopes: vec![0; mir.blocks.len()],
        inlined_origins: 0,
        natives: Vec::new(),
        c_buffer: None,
        result: result.cloned(),
        sret: None,
        fresh: None,
        kept: Vec::new(),
        owned: Vec::new(),
        results: None,
    };
    // The parameters' words come first: a parameter that passes by value
    // has its storage form's, and registers of its own besides.
    let n = mir.locals.len();
    l.locals = vec![Vec::new(); n];
    l.layouts = vec![None; n];
    l.forms = vec![None; n];
    let mut incoming: Vec<Option<Incoming>> = vec![None; mir.params];
    let mut params = 0;
    // A result of more than two words given by value goes to a buffer
    // the caller gives first.
    if let Some((size, _)) = result
        && size.div_ceil(8) > 2
    {
        l.sret = Some(l.reg());
        params += 1;
    }
    for (i, decl) in mir.locals.iter().enumerate().take(mir.params) {
        match flat.get(i) == Some(&true) {
            true => {
                let (size, slots) = storage(db, program, decl.ty).expect("a flat parameter");
                let words: Vec<VReg> = (0..size.div_ceil(8)).map(|_| l.reg()).collect();
                params += words.len();
                incoming[i] = Some((words, size, slots));
            }
            false => {
                l.local(i, decl);
                params += l.locals[i].len();
            }
        }
    }
    for (i, decl) in mir.locals.iter().enumerate() {
        if i >= mir.params || incoming[i].is_some() {
            l.local(i, decl);
        }
    }
    let returns = match result {
        Some((size, _)) if size.div_ceil(8) > 2 => 0,
        Some((size, _)) => size.div_ceil(8) as usize,
        None => layout(db, program, mir.result).map_or(0, Layout::words),
    };
    let unknown_param = l.layouts[..mir.params].iter().any(Option::is_none);
    for (b, block) in mir.blocks.iter().enumerate() {
        l.current = (b, Vec::new());
        l.fresh = None;
        l.kept = block
            .statements
            .iter()
            .flat_map(|s| match s {
                Statement::Reclaim { kept, .. } => kept.iter().map(|&(_, k)| k).collect(),
                _ => Vec::new(),
            })
            .collect();
        l.owned.clear();
        l.catch = block.catch;
        l.scope = block.inlined;
        if unknown_param || returns > 2 {
            l.unsupported("types of parameters or results");
            continue;
        }
        let entry = match b {
            0 => l.receive(&incoming),
            _ => Ok(()),
        };
        let lowered = entry
            .and_then(|()| block.statements.iter().try_for_each(|s| l.statement(s)))
            .and_then(|()| l.terminator(&block.terminator, returns));
        if let Err(what) = lowered {
            l.unsupported(what);
        }
    }
    // MIR's entry block is no branch target, so the scratch words are
    // pushed once.
    if let (Some(dst), Some(entry)) = (l.results, l.blocks[0].as_mut()) {
        entry.insts.insert(
            0,
            Inst::SidePush {
                dst,
                size: MAX_FLAT_SIZE,
                align: 8,
            },
        );
    }
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
    if let (Some((dst, words)), Some(entry)) = (l.c_buffer, l.blocks[0].as_mut()) {
        entry.insts.insert(
            0,
            Inst::SidePush {
                dst,
                size: words * 8,
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
    let mut blocks: Vec<LirBlock> = l
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
    // Each block of code with inlined calls tells whose code it is.
    if !mir.inlined.is_empty() {
        for (block, scope) in blocks.iter_mut().zip(&l.block_scopes) {
            block.insts.insert(0, Inst::Inlined(*scope));
        }
    }
    let inlined = mir
        .inlined
        .iter()
        .map(|call| {
            let mut frames = vec![func_id(call.func)];
            let mut parent = call.parent;
            while let Some(p) = parent {
                frames.push(func_id(mir.inlined[p as usize].func));
                parent = mir.inlined[p as usize].parent;
            }
            InlinedCode {
                frames,
                module: call.func.owner(db).module(db).path(db).clone(),
            }
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
            natives: l.natives,
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
        inlined,
    }
}

/// The kind of a plain C value's type in a `CCall` descriptor
/// (`CForm::Value`).
fn c_kind_of<'db>(db: &'db dyn Db, ty: Ty<'db>) -> Option<u8> {
    Some(match ty.as_builtin(db)?.0 {
        Builtin::Int8 => c_kind::I8,
        Builtin::Int16 => c_kind::I16,
        Builtin::Int32 => c_kind::I32,
        Builtin::Int => c_kind::I64,
        Builtin::UInt8 => c_kind::U8,
        Builtin::UInt16 => c_kind::U16,
        Builtin::UInt32 => c_kind::U32,
        Builtin::UInt64 => c_kind::U64,
        Builtin::Float => c_kind::F64,
        Builtin::CF32 => c_kind::F32,
        Builtin::CPtr => c_kind::PTR,
        _ => return None,
    })
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

/// Where the expressions of an inlined call's code lie: the positions and
/// source of the callee's owner.
struct Scope<'db> {
    positions: &'db [Range<u32>],
    name_at: u32,
    source: &'db str,
}

struct Lower<'a, 'db> {
    db: &'db dyn Db,
    program: Program,
    /// The instance whose MIR this is, whose type arguments code trees
    /// put in.
    instance: InstanceKey<'db>,
    mir: &'a MirBody<'db>,
    /// Whether calls go straight to their callees instead of their slots.
    direct: bool,
    /// Where each expression of the body is in its module's source.
    positions: &'db [Range<u32>],
    /// Where the name of the declaration starts: the position of a trap
    /// with a detail but no expression, as of a C function's result.
    name_at: u32,
    vregs: u32,
    /// The registers of each local.
    locals: Vec<Vec<VReg>>,
    layouts: Vec<Option<Layout>>,
    /// The register form of each split local.
    forms: Vec<Option<Form<'db>>>,
    /// MIR block `i` is LIR block `i`; tests add more.
    blocks: Vec<Option<LirBlock>>,
    current: (usize, Vec<Inst>),
    /// The handler of the trap handler around the MIR block being lowered.
    catch: Option<BlockId>,
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
    /// Where the expressions of each inlined call's code lie.
    scopes: Vec<Scope<'db>>,
    /// The inlined call whose code the MIR block being lowered is.
    scope: Option<u32>,
    /// The inlined call of each LIR block's code, from one, or zero.
    block_scopes: Vec<u32>,
    /// The positions of traps in inlined code numbered so far.
    inlined_origins: u32,
    /// Three words on the side stack that the runtime's reads put what they
    /// read in, pushed at the entry once the code reads anything.
    scratch: Option<VReg>,
    /// The function the code is loaded as, and its steps so far.
    func: FuncId,
    steps: Vec<StepInfo<'db>>,
    /// The C functions it calls, and the words on the side stack their
    /// arguments go in, pushed at the entry with room for the most any
    /// call needs.
    natives: Vec<NativeSymbol>,
    c_buffer: Option<(VReg, u32)>,
    /// The storage form of the result when the code gives it by value,
    /// and the buffer its caller gave for one of more than two words.
    result: Option<(u32, Vec<Slot>)>,
    sret: Option<VReg>,
    /// A local a read gave a value of its own, which owns its reference
    /// already: the retain that follows the read is its own, and without
    /// one the value dies at once.
    fresh: Option<Local>,
    /// The locals the block's reclaims keep, whose reads are not retained
    /// (Plan §11.10.1), and those of them a read gave values of their own.
    kept: Vec<Local>,
    owned: Vec<Local>,
    /// A buffer on the side stack for the results of more than two words
    /// that calls give by value, pushed at the entry.
    results: Option<VReg>,
}

impl<'a, 'db> Lower<'a, 'db> {
    /// Gives local `i` its registers: its layout's words, or a split
    /// local's fields' (Plan §11.10.10).
    fn local(&mut self, i: usize, decl: &LocalDecl<'db>) {
        let (db, program) = (self.db, self.program);
        let layout = layout(db, program, decl.ty);
        let mut words = layout.map_or(0, Layout::words);
        // An environment is passed as a word even when it holds nothing.
        if i == 0 && self.mir.env {
            words = words.max(1);
        }
        let form = decl.split.then(|| form(db, program, decl.ty)).flatten();
        let pointers = match &form {
            Some(f) => {
                words = f.words();
                pointer_regs(f)
            }
            None => layout.map_or(Vec::new(), |l| pointer_regs(&Form::Words(l))),
        };
        let regs: Vec<VReg> = (0..words).map(|_| self.reg()).collect();
        // A borrowed parameter's references are its caller's to release.
        if !decl.borrowed {
            for at in pointers {
                self.tracked.push(regs[at]);
            }
        }
        self.locals[i] = regs;
        self.layouts[i] = layout;
        self.forms[i] = form;
    }

    /// Takes the parameters that pass by value from their storage form
    /// into their registers, or into a box when they are not split.
    fn receive(&mut self, incoming: &[Option<Incoming>]) -> Result<(), Unsupported> {
        for (i, words) in incoming.iter().enumerate() {
            let Some((words, _, slots)) = words else {
                continue;
            };
            let ty = self.local_ty(Local(i as u32));
            let f = form(self.db, self.program, ty).ok_or("records of this type")?;
            let regs = self.unpack(slots, words, f.words());
            let values = match self.forms[i] {
                Some(_) => regs,
                None => self.boxed(ty, &f, &regs)?,
            };
            self.assign(Local(i as u32), values)?;
        }
        Ok(())
    }

    fn reg(&mut self) -> VReg {
        self.vregs += 1;
        VReg(self.vregs - 1)
    }

    fn push(&mut self, inst: Inst) {
        self.current.1.push(inst);
    }

    /// Where the expressions of the code being lowered lie, where the
    /// name of its declaration starts, and its module's source.
    fn scope(&self) -> (&'db [Range<u32>], u32, &'db str) {
        match self.scope {
            None => (self.positions, self.name_at, self.source),
            Some(k) => {
                let scope = &self.scopes[k as usize];
                (scope.positions, scope.name_at, scope.source)
            }
        }
    }

    /// The byte offset of an expression of the code being lowered in its
    /// module's source.
    fn position(&self, e: ExprId) -> Option<u32> {
        self.scope().0.get(e.index()).map(|r| r.start)
    }

    /// The position a trap at a byte offset of the code being lowered
    /// names, with its origin: the line and column, from one, the column
    /// counted in characters.
    fn origin(&mut self, at: u32) -> u32 {
        let source = self.scope().2;
        let before = &source[..(at as usize).min(source.len())];
        let line = before.matches('\n').count() as u32 + 1;
        let start = before.rfind('\n').map_or(0, |i| i + 1);
        let column = before[start..].chars().count() as u32 + 1;
        let (position, inlined) = match self.scope {
            None => (at, 0),
            Some(k) => {
                self.inlined_origins += 1;
                (INLINED_POSITION | self.inlined_origins, k + 1)
            }
        };
        self.origins.push(TrapOrigin {
            position,
            line,
            column,
            inlined,
            offset: at,
        });
        position
    }

    fn new_block(&mut self) -> LirBlockId {
        self.blocks.push(None);
        self.block_scopes.push(0);
        LirBlockId(self.blocks.len() as u32 - 1)
    }

    /// Ends the current block; what follows goes to `next`.
    fn end(&mut self, term: Term, next: Option<LirBlockId>) {
        let (b, insts) = std::mem::take(&mut self.current);
        self.blocks[b] = Some(LirBlock { insts, term });
        self.block_scopes[b] = self.scope.map_or(0, |k| k + 1);
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
    /// A split local goes where a value must be in a box: it is boxed
    /// there, and the box takes its references.
    fn operand(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        match op {
            Operand::Local(l) => {
                self.layouts[l.index()].ok_or("values of this type")?;
                let regs = self.locals[l.index()].clone();
                match self.forms[l.index()].clone() {
                    Some(form) => self.boxed(self.local_ty(*l), &form, &regs),
                    None => Ok(regs),
                }
            }
            Operand::Const(c) => self.constant_words(c, ty),
        }
    }

    /// The words of an operand that goes where a split record is
    /// expected: a split local's registers as they are.
    fn split_operand(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        match op {
            Operand::Local(l) if self.forms[l.index()].is_some() => {
                Ok(self.locals[l.index()].clone())
            }
            _ => self.operand(op, ty),
        }
    }

    /// The registers of an operand in a split form, which take its
    /// references: a split local's as they are, a boxed value's loaded.
    fn split_value(
        &mut self,
        op: &Operand<'db>,
        ty: Ty<'db>,
        f: &Form<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        if let Operand::Local(l) = op
            && let Some(own) = self.forms[l.index()].clone()
        {
            let regs = self.locals[l.index()].clone();
            return self.reform(ty, &own, f, &regs);
        }
        let words = self.operand(op, ty)?;
        match words_form(f) {
            true => Ok(words),
            false => self.owned_fields(ty, f, &words),
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
            Constant::Tree { owner, expr, hash } => {
                let (db, program) = (self.db, self.program);
                let args = self.instance.args(db);
                let generic = match owner {
                    Owner::Item(item) if !args.is_empty() => Some((*item, &args[..])),
                    _ => None,
                };
                let (digest, bytes) = crate::tree::expr_tree(db, program, *owner, *expr, generic)
                    .map_err(|_| "code of this form as an `Expr`")?;
                match hash {
                    true => self.text_literal(&digest)?,
                    false => self.text_literal(&bytes)?,
                }
            }
            Constant::Wire(env) => {
                let (shapes, root) = crate::shape::shapes(self.db, self.program, *env);
                let mut bytes = root.to_le_bytes().to_vec();
                bytes.extend(shapes.encode());
                self.text_literal(&bytes)?
            }
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
            Operand::Const(Constant::Tree { .. } | Constant::Wire(_)) => {
                Ty::builtin(self.db, Builtin::Bytes)
            }
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
        if let Some(fresh) = self.fresh.take() {
            if matches!(statement, Statement::Retain(l) if *l == fresh) {
                return Ok(());
            }
            match self.kept.contains(&fresh) {
                true => self.owned.push(fresh),
                false => self.count(fresh, Count::Release)?,
            }
        }
        match statement {
            Statement::Assign(local, rvalue) => {
                let values = self.rvalue(*local, rvalue)?;
                self.assign(*local, values)
            }
            Statement::Retain(local) => self.count(*local, Count::Retain),
            Statement::Release(local) => self.count(*local, Count::Release),
            Statement::Reclaim { local, token, kept } => self.reclaim(*local, *token, kept),
            Statement::Poll => {
                self.push(Inst::Poll);
                Ok(())
            }
            Statement::Step { at, locals } => {
                let step = self.steps.len() as u32;
                let position = at.and_then(|e| self.position(e));
                let mut values = Vec::new();
                let mut named = Vec::new();
                for &local in locals {
                    let decl = &self.mir.locals[local.index()];
                    // A local without a layout has no words to show.
                    if let (Some((_, name)), Some(_)) = (decl.binding, self.layouts[local.index()])
                    {
                        values.extend(self.locals[local.index()].iter().copied());
                        named.push((name, decl.ty, decl.split));
                    }
                }
                let mut inlined = Vec::new();
                let mut scope = self.scope;
                while let Some(k) = scope {
                    inlined.push(self.mir.inlined[k as usize].func);
                    scope = self.mir.inlined[k as usize].parent;
                }
                self.steps.push(StepInfo {
                    position,
                    inlined,
                    locals: named,
                });
                self.push(Inst::Step {
                    func: self.func,
                    step,
                    values,
                    inlined: self.steps[step as usize].inlined.len() as u32,
                });
                Ok(())
            }
        }
    }
}

/// Where the value at a place is.
enum Found<'db> {
    /// In registers: its layout's words, or a split value's.
    Words(Vec<VReg>),
    /// Stored inline in the box or the list element at `ptr`, a record or
    /// a union, as `slots` say.
    Stored {
        ptr: VReg,
        form: Form<'db>,
        slots: Vec<Slot>,
    },
}

/// How `count_form` counts.
#[derive(Clone, Copy)]
enum Count {
    Retain,
    Release,
}

/// Whether a split value's registers are the words of its layout: a
/// union's whose members are a word or none.
fn words_form(f: &Form<'_>) -> bool {
    match f {
        Form::Words(_) => true,
        Form::Fields(_) => false,
        Form::Union(members) => members.iter().all(|(_, m)| {
            matches!(
                m,
                Form::Words(Layout::Zero | Layout::Imm(_) | Layout::Tag | Layout::Box)
            )
        }),
    }
}

/// The registers of a value in a form that hold a reference or nothing,
/// which a trap releases: a box pointer, a string's first word and a
/// function value's environment. A union's register is one when it is for
/// each member that has it, and the others leave it zero; one that holds
/// a number for some member is not.
fn pointer_regs(f: &Form<'_>) -> Vec<usize> {
    match f {
        Form::Words(Layout::Box | Layout::Pair) => vec![0],
        Form::Words(Layout::Closure) => vec![1],
        Form::Words(_) => Vec::new(),
        Form::Fields(fields) => {
            let mut out = Vec::new();
            let mut at = 0;
            for (_, _, inner) in fields {
                out.extend(pointer_regs(inner).into_iter().map(|r| at + r));
                at += inner.words();
            }
            out
        }
        Form::Union(members) => {
            let own: Vec<(usize, Vec<usize>)> = members
                .iter()
                .map(|(_, m)| (m.words(), pointer_regs(m)))
                .collect();
            (0..f.words() - 1)
                .filter(|r| {
                    let mut any = false;
                    for (n, pointers) in &own {
                        if r < n {
                            if !pointers.contains(r) {
                                return false;
                            }
                            any = true;
                        }
                    }
                    any
                })
                .map(|r| r + 1)
                .collect()
        }
    }
}

/// Whether a split value's registers may hold references.
fn counted_form(f: &Form<'_>) -> bool {
    match f {
        Form::Words(l) => !matches!(l, Layout::Zero | Layout::Imm(_) | Layout::Tag),
        Form::Fields(fields) => fields.iter().any(|(_, _, f)| counted_form(f)),
        Form::Union(members) => members.iter().any(|(_, f)| counted_form(f)),
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
