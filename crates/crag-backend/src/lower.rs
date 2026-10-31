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
    BinOp, BlockId, CastOp, ClosurePlacement, CmpOp, Constant, Entry, InstanceKey, Intrinsic,
    Local, LocalDecl, MirBody, Operand, Place, Rvalue, Statement, Terminator, Tier, TrapKind,
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
/// value as `flat_params` and `flat_result` say (Plan §11.10.10).
pub fn lower_to_lir<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    mir: &MirBody<'db>,
    cell: Option<SlotKey>,
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
        mir,
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
        true_index: named("True").map_or(-1, type_index),
        false_index: named("False").map_or(-1, type_index),
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
    mir: &'a MirBody<'db>,
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

    /// The register form of a flat record or union from the words of its
    /// storage form (Compiler Architecture §A11.4).
    fn unpack(&mut self, slots: &[Slot], words: &[VReg], registers: usize) -> Vec<VReg> {
        let mut out: Vec<Option<VReg>> = vec![None; registers];
        self.unpack_into(slots, words, &mut out);
        out.into_iter()
            .map(|r| r.unwrap_or_else(|| self.constant(0)))
            .collect()
    }

    fn unpack_into(&mut self, slots: &[Slot], words: &[VReg], out: &mut [Option<VReg>]) {
        for slot in slots {
            let w = (slot.offset / 8) as usize;
            let byte = slot.offset % 8;
            match &slot.kind {
                SlotKind::Words => {
                    for k in 0..(slot.size / 8) as usize {
                        out[slot.at + k] = Some(words[w + k]);
                    }
                }
                SlotKind::Int { signed } => {
                    let bits = 8 * slot.size;
                    out[slot.at] = Some(match (bits, signed) {
                        (64, _) => words[w],
                        // Up to the field, then down with its sign.
                        (_, true) => {
                            let up = self.constant(i64::from(64 - 8 * byte - bits));
                            let raised = self.bin(LirBin::Shl, words[w], up);
                            let down = self.constant(i64::from(64 - bits));
                            self.bin(LirBin::SShr, raised, down)
                        }
                        (_, false) => self.field_bits(words[w], 8 * byte, bits),
                    });
                }
                SlotKind::Tag(members) => {
                    let (shift, width) = match slot.bits {
                        Some((bit, width)) => (8 * byte + u32::from(bit), u32::from(width)),
                        None => (8 * byte, 8 * slot.size),
                    };
                    let tag = self.field_bits(words[w], shift, width);
                    out[slot.at] = Some(self.type_of_tag(tag, members));
                }
                SlotKind::Union { tag, members } => {
                    // The member's type index, from its tag or the niche.
                    let index = match tag {
                        UnionTag::Bytes { offset, size } => {
                            let word = words[(offset / 8) as usize];
                            let tag = self.field_bits(word, 8 * (offset % 8), 8 * size);
                            let indices: Vec<i64> = members.iter().map(|m| m.0).collect();
                            self.type_of_tag(tag, &indices)
                        }
                        UnionTag::Niche {
                            empty,
                            offset,
                            test,
                        } => {
                            let niche = self.niche(words, *offset, *test);
                            let other = 1 - *empty;
                            let (e, o) = (
                                self.constant(members[*empty].0),
                                self.constant(members[other].0),
                            );
                            let dst = self.reg();
                            self.push(Inst::Select {
                                dst,
                                cond: niche,
                                a: e,
                                b: o,
                            });
                            dst
                        }
                    };
                    out[slot.at] = Some(index);
                    // Each member's registers, where its index is the one.
                    for (m, member) in members {
                        let mut own: Vec<Option<VReg>> = vec![None; out.len()];
                        self.unpack_into(member, words, &mut own);
                        let m = self.constant(*m);
                        let same = self.cmp(Cond::Eq, index, m);
                        for (r, value) in own.into_iter().enumerate() {
                            let Some(value) = value else { continue };
                            let other = out[r].unwrap_or_else(|| self.constant(0));
                            let dst = self.reg();
                            self.push(Inst::Select {
                                dst,
                                cond: same,
                                a: value,
                                b: other,
                            });
                            out[r] = Some(dst);
                        }
                    }
                }
            }
        }
    }

    /// The type index of the member a local tag numbers.
    fn type_of_tag(&mut self, tag: VReg, members: &[i64]) -> VReg {
        let mut index = self.constant(members[0]);
        for (k, &m) in members.iter().enumerate().skip(1) {
            let k = self.constant(k as i64);
            let same = self.cmp(Cond::Eq, tag, k);
            let m = self.constant(m);
            let dst = self.reg();
            self.push(Inst::Select {
                dst,
                cond: same,
                a: m,
                b: index,
            });
            index = dst;
        }
        index
    }

    /// The local tag of the member whose type index a register holds.
    fn tag_of_type(&mut self, index: VReg, members: &[i64]) -> VReg {
        let mut tag = self.constant(0);
        for (k, &m) in members.iter().enumerate().skip(1) {
            let m = self.constant(m);
            let same = self.cmp(Cond::Eq, index, m);
            let k = self.constant(k as i64);
            let dst = self.reg();
            self.push(Inst::Select {
                dst,
                cond: same,
                a: k,
                b: tag,
            });
            tag = dst;
        }
        tag
    }

    /// Puts the low `width` bits of a value at bit `at` of storage words.
    fn or_bits(&mut self, words: &mut [Option<VReg>], value: VReg, at: u32, width: u32) {
        let mut part = value;
        if width < 64 {
            let mask = self.constant(((1u64 << width) - 1) as i64);
            part = self.bin(LirBin::And, part, mask);
        }
        if !at.is_multiple_of(64) {
            let by = self.constant(i64::from(at % 64));
            part = self.bin(LirBin::Shl, part, by);
        }
        let w = (at / 64) as usize;
        words[w] = Some(match words[w] {
            Some(before) => self.bin(LirBin::Or, before, part),
            None => part,
        });
    }

    /// Whether storage words hold a niche: 1 or 0.
    fn niche(&mut self, words: &[VReg], offset: u32, test: NicheTest) -> VReg {
        let word = words[(offset / 8) as usize];
        let shift = 8 * (offset % 8);
        let (bits, value) = match test {
            NicheTest::Value { size, value } => {
                (self.field_bits(word, shift, 8 * u32::from(size)), value)
            }
            NicheTest::Bit(bit) => (self.field_bits(word, shift + u32::from(bit), 1), 1),
        };
        let value = self.constant(value as i64);
        self.cmp(Cond::Eq, bits, value)
    }

    /// The words of a flat record's or union's storage form from its
    /// register form.
    fn pack(&mut self, slots: &[Slot], size: u32, regs: &[VReg]) -> Vec<VReg> {
        let mut words: Vec<Option<VReg>> = vec![None; size.div_ceil(8) as usize];
        self.pack_into(slots, regs, &mut words);
        words
            .into_iter()
            .map(|w| w.unwrap_or_else(|| self.constant(0)))
            .collect()
    }

    fn pack_into(&mut self, slots: &[Slot], regs: &[VReg], words: &mut [Option<VReg>]) {
        for slot in slots {
            let w = (slot.offset / 8) as usize;
            let byte = slot.offset % 8;
            let (value, shift, width) = match &slot.kind {
                SlotKind::Words => {
                    for k in 0..(slot.size / 8) as usize {
                        words[w + k] = Some(regs[slot.at + k]);
                    }
                    continue;
                }
                SlotKind::Int { .. } => (regs[slot.at], 8 * byte, 8 * slot.size),
                SlotKind::Tag(members) => {
                    let tag = self.tag_of_type(regs[slot.at], members);
                    match slot.bits {
                        Some((bit, width)) => (tag, 8 * byte + u32::from(bit), u32::from(width)),
                        None => (tag, 8 * byte, 8 * slot.size),
                    }
                }
                SlotKind::Union { tag, members } => {
                    // Each member's words with its tag or niche, where its
                    // index is the one.
                    let mut chosen: Vec<Option<VReg>> = vec![None; words.len()];
                    for (k, (m, member)) in members.iter().enumerate() {
                        let mut own: Vec<Option<VReg>> = vec![None; words.len()];
                        self.pack_into(member, regs, &mut own);
                        match tag {
                            UnionTag::Bytes { offset, size } => {
                                let k = self.constant(k as i64);
                                self.or_bits(&mut own, k, 8 * offset, 8 * size);
                            }
                            // The member of no words is the other's niche.
                            UnionTag::Niche {
                                empty,
                                offset,
                                test,
                            } if *empty == k => {
                                let (value, at, width) = match *test {
                                    NicheTest::Value { size, value } => {
                                        (value as i64, 8 * offset, 8 * u32::from(size))
                                    }
                                    NicheTest::Bit(bit) => (1, 8 * offset + u32::from(bit), 1),
                                };
                                let value = self.constant(value);
                                self.or_bits(&mut own, value, at, width);
                            }
                            UnionTag::Niche { .. } => {}
                        }
                        let m = self.constant(*m);
                        let same = self.cmp(Cond::Eq, regs[slot.at], m);
                        for (w, value) in own.into_iter().enumerate() {
                            let Some(value) = value else { continue };
                            let other = chosen[w].unwrap_or_else(|| self.constant(0));
                            let dst = self.reg();
                            self.push(Inst::Select {
                                dst,
                                cond: same,
                                a: value,
                                b: other,
                            });
                            chosen[w] = Some(dst);
                        }
                    }
                    for (w, value) in chosen.into_iter().enumerate() {
                        if let Some(value) = value {
                            words[w] = Some(match words[w] {
                                Some(before) => self.bin(LirBin::Or, before, value),
                                None => value,
                            });
                        }
                    }
                    continue;
                }
            };
            self.or_bits(words, value, 64 * w as u32 + shift, width);
        }
    }

    /// The `width` bits of a word from bit `shift` up, zero-extended.
    fn field_bits(&mut self, word: VReg, shift: u32, width: u32) -> VReg {
        let mut value = word;
        if shift > 0 {
            let by = self.constant(i64::from(shift));
            value = self.bin(LirBin::UShr, value, by);
        }
        if width < 64 {
            let mask = self.constant(((1u64 << width) - 1) as i64);
            value = self.bin(LirBin::And, value, mask);
        }
        value
    }

    /// The words of an argument that passes by value: a split local's
    /// registers packed, or a boxed record's fields loaded, which take
    /// references of their own as the call takes the box's.
    fn flat_argument(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        let (size, slots) = storage(self.db, self.program, ty).ok_or("records of this type")?;
        let regs = self.flat_value(op, ty)?;
        Ok(self.pack(&slots, size, &regs))
    }

    /// The registers of a value that passes by value, which takes the
    /// operand's references: a split local's registers, a boxed value's
    /// loaded, or a tag's type index.
    fn flat_value(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        let f = form(self.db, self.program, ty).ok_or("records of this type")?;
        match op {
            Operand::Local(l) if self.forms[l.index()].is_some() => {
                Ok(self.locals[l.index()].clone())
            }
            Operand::Local(l) => {
                let words = self.locals[l.index()].clone();
                self.owned_fields(ty, &f, &words)
            }
            Operand::Const(Constant::Tag(tag)) => {
                let mut regs = vec![self.constant(type_index(self.member_of(*tag, ty)))];
                while regs.len() < f.words() {
                    regs.push(self.constant(0));
                }
                Ok(regs)
            }
            Operand::Const(_) => Err("this conversion"),
        }
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

    /// The words of a split value as its layout has them: a record's box,
    /// a union's two words, or the words as they are.
    fn boxed(
        &mut self,
        ty: Ty<'db>,
        f: &Form<'db>,
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match f {
            Form::Words(_) => Ok(regs.to_vec()),
            Form::Fields(_) => Ok(vec![self.box_split(ty, f, regs)?]),
            Form::Union(members) => self.box_union(members, regs),
        }
    }

    /// The two words of a union split in registers: its type index, and
    /// its member's word, a record boxed and a member of two words in a
    /// member box, which take over the member's references.
    fn box_union(
        &mut self,
        members: &[(Ty<'db>, Form<'db>)],
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        let payload = self.constant(0);
        // A trap unwinding the frame releases the box made, as a boxed
        // local's, when every member's word is a pointer or nothing.
        let pointers = members
            .iter()
            .all(|(_, f)| !matches!(f, Form::Words(Layout::Imm(_))));
        if pointers {
            self.tracked.push(payload);
        }
        let done = self.new_block();
        for (m, f) in members {
            let n = f.words();
            // A record member is a box, even one of no words.
            if let Form::Words(Layout::Zero | Layout::Tag) = f {
                continue;
            }
            let (hit, next) = (self.new_block(), self.new_block());
            let index = self.constant(type_index(*m));
            let same = self.cmp(Cond::Eq, regs[0], index);
            let term = Term::Branch {
                cond: same,
                then: hit,
                otherwise: next,
            };
            self.end(term, Some(hit));
            let words = &regs[1..1 + n];
            let value = match f {
                Form::Words(Layout::Pair | Layout::Closure) => {
                    let header = match f {
                        Form::Words(Layout::Pair) => TEXT_BOX_HEADER,
                        _ => FUNCTION_BOX_HEADER,
                    };
                    let ptr = self.alloc(MEMBER_BOX_SIZE, header as i64);
                    for (k, &src) in words.iter().enumerate() {
                        self.push(Inst::Store {
                            src,
                            addr: ptr,
                            offset: (HEADER_SIZE + 8 * k as u32) as i32,
                        });
                    }
                    ptr
                }
                _ => word(&self.boxed(*m, f, words)?)?,
            };
            self.push(Inst::Move {
                dst: payload,
                src: value,
            });
            self.end(Term::Jump(done), Some(next));
        }
        self.end(Term::Jump(done), Some(done));
        Ok(vec![regs[0], payload])
    }

    /// The registers of a split value from the words its layout has, which
    /// it borrows: a record's fields loaded from its box, a union's member
    /// from its word.
    fn unboxed(
        &mut self,
        ty: Ty<'db>,
        f: &Form<'db>,
        words: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match f {
            Form::Words(_) => Ok(words.to_vec()),
            Form::Fields(_) => self.unbox(ty, f, word(words)?),
            Form::Union(members) => {
                let out: Vec<VReg> = (0..f.words()).map(|_| self.constant(0)).collect();
                self.push(Inst::Move {
                    dst: out[0],
                    src: words[0],
                });
                let done = self.new_block();
                for (m, inner) in members {
                    let n = inner.words();
                    if n == 0 {
                        continue;
                    }
                    let (hit, next) = (self.new_block(), self.new_block());
                    let index = self.constant(type_index(*m));
                    let same = self.cmp(Cond::Eq, words[0], index);
                    let term = Term::Branch {
                        cond: same,
                        then: hit,
                        otherwise: next,
                    };
                    self.end(term, Some(hit));
                    let values = match inner {
                        Form::Words(Layout::Pair | Layout::Closure) => self.member_words(words[1]),
                        _ => self.unboxed(*m, inner, &words[1..2])?,
                    };
                    for (k, src) in values.into_iter().enumerate() {
                        self.push(Inst::Move {
                            dst: out[1 + k],
                            src,
                        });
                    }
                    self.end(Term::Jump(done), Some(next));
                }
                self.end(Term::Jump(done), Some(done));
                Ok(out)
            }
        }
    }

    /// A box holding the registers of a split record, which takes their
    /// references.
    fn box_split(
        &mut self,
        ty: Ty<'db>,
        form: &Form<'db>,
        regs: &[VReg],
    ) -> Result<VReg, Unsupported> {
        let Form::Fields(_) = form else {
            return word(regs);
        };
        let b = box_form(self.db, self.program, ty).ok_or("records of this type")?;
        self.describe(ty)?;
        let regs = self.reform(ty, form, &b.form, regs)?;
        let ptr = self.alloc(b.size, type_index(ty));
        // A trap unwinding the frame releases it, as a boxed local's.
        self.tracked.push(ptr);
        self.store_box(&b, ptr, &regs);
        Ok(ptr)
    }

    /// Writes the registers of a record's fields into its new box.
    fn store_box(&mut self, b: &BoxForm<'db>, ptr: VReg, regs: &[VReg]) {
        let words = self.pack(&b.slots, b.size, regs);
        let header = (HEADER_SIZE / 8) as usize;
        for (k, src) in words.into_iter().enumerate().skip(header) {
            self.push(Inst::Store {
                src,
                addr: ptr,
                offset: 8 * k as i32,
            });
        }
    }

    /// The `n` registers of a value stored as `slots` in the box or the
    /// collection's slot at `ptr`, from the words that hold it. A slot of
    /// fewer bytes need not be aligned, and the collection has room for the
    /// last word read past its end.
    fn load_stored(&mut self, ptr: VReg, slots: &[Slot], n: usize) -> Vec<VReg> {
        let Some((from, to)) = span(slots) else {
            return (0..n).map(|_| self.constant(0)).collect();
        };
        let first = from / 8 * 8;
        let words: Vec<VReg> = (first..to)
            .step_by(8)
            .map(|at| {
                let dst = self.reg();
                self.push(Inst::LoadUnaligned {
                    dst,
                    addr: ptr,
                    offset: at as i32,
                });
                dst
            })
            .collect();
        let slots: Vec<Slot> = slots.iter().map(|s| rebase(s, first)).collect();
        self.unpack(&slots, &words, n)
    }

    /// The registers of a split record loaded from its box, borrowed from
    /// it.
    fn unbox(
        &mut self,
        ty: Ty<'db>,
        form: &Form<'db>,
        ptr: VReg,
    ) -> Result<Vec<VReg>, Unsupported> {
        let Form::Fields(_) = form else {
            return Ok(vec![ptr]);
        };
        let b = box_form(self.db, self.program, ty).ok_or("records of this type")?;
        let regs = self.load_stored(ptr, &b.slots, b.form.words());
        self.lend(ty, &b.form, form, &regs)
    }

    /// The registers of a value in the form `to`, borrowed from its
    /// registers in the form `from`: a record or union in a box loaded
    /// from it.
    fn lend(
        &mut self,
        ty: Ty<'db>,
        from: &Form<'db>,
        to: &Form<'db>,
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match (from, to) {
            _ if from == to => Ok(regs.to_vec()),
            (Form::Words(_), _) => self.unboxed(ty, to, regs),
            (Form::Fields(_), Form::Fields(fields)) => {
                let mut out = Vec::new();
                for (name, t, f) in fields {
                    let (at, _, inner) = from.field(*name).ok_or("records of this type")?;
                    let part = regs[at..at + inner.words()].to_vec();
                    out.extend(self.lend(*t, inner, f, &part)?);
                }
                Ok(out)
            }
            _ => Err("records of this type"),
        }
    }

    /// The registers of a value in the form `to`, from its registers in
    /// the form `from`, which they take the references of.
    fn reform(
        &mut self,
        ty: Ty<'db>,
        from: &Form<'db>,
        to: &Form<'db>,
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match (from, to) {
            _ if from == to => Ok(regs.to_vec()),
            (Form::Fields(_), Form::Fields(fields)) => {
                let mut out = Vec::new();
                for (name, t, f) in fields {
                    let (at, _, inner) = from.field(*name).ok_or("records of this type")?;
                    let part = regs[at..at + inner.words()].to_vec();
                    out.extend(self.reform(*t, inner, f, &part)?);
                }
                Ok(out)
            }
            (_, Form::Words(_)) => self.boxed(ty, from, regs),
            (Form::Words(_), _) => self.owned_fields(ty, to, regs),
            _ => {
                let words = self.boxed(ty, from, regs)?;
                self.owned_fields(ty, to, &words)
            }
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
        if let Some(fresh) = self.fresh.take() {
            if matches!(statement, Statement::Retain(l) if *l == fresh) {
                return Ok(());
            }
            self.count(fresh, Count::Release)?;
        }
        match statement {
            Statement::Assign(local, rvalue) => {
                let values = self.rvalue(*local, rvalue)?;
                self.assign(*local, values)
            }
            Statement::Retain(local) => self.count(*local, Count::Retain),
            Statement::Release(local) => self.count(*local, Count::Release),
            Statement::Reclaim { local, token } => self.reclaim(*local, *token),
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

    /// Retains or releases the box a local holds, if it holds one.
    fn count(&mut self, local: Local, how: Count) -> Result<(), Unsupported> {
        let regs = self.locals[local.index()].clone();
        let ty = self.local_ty(local);
        let form = match self.forms[local.index()].clone() {
            Some(form) => form,
            None => match self.layouts[local.index()] {
                Some(layout) => Form::Words(layout),
                None => return Ok(()),
            },
        };
        self.count_form(&form, ty, &regs, how)
    }

    /// Gives up a record's reference as a release does, but takes apart a
    /// box that no one else holds (Plan §11.10.1): its fields are
    /// released, and the box, empty, goes to the token. A shared box gives
    /// the token a static empty one.
    fn reclaim(&mut self, local: Local, token: Local) -> Result<(), Unsupported> {
        let ty = self.local_ty(local);
        let empty = self.empty_box();
        let t = word(&self.locals[token.index()])?;
        self.push(Inst::Move { dst: t, src: empty });
        let b = match (
            &self.forms[local.index()],
            box_form(self.db, self.program, ty),
        ) {
            (None, Some(b)) => b,
            // A split record has no box.
            _ => return self.count(local, Count::Release),
        };
        let ptr = word(&self.locals[local.index()])?;
        // Fields the runtime closes when it frees the box stay with it, and
        // a token takes only a box of its record's size class.
        let plain = match type_descriptor(self.db, self.program, ty) {
            Some(TypeDescriptor::Record { counted, dispose }) => {
                dispose.is_none()
                    && counted.iter().all(|f| {
                        matches!(
                            f,
                            CountedField::Box(_)
                                | CountedField::Union { .. }
                                | CountedField::Guarded { .. }
                        )
                    })
            }
            _ => false,
        };
        let fits = box_form(self.db, self.program, self.local_ty(token)).is_some_and(|t| {
            size_class(t.size).is_some() && size_class(t.size) == size_class(b.size)
        });
        if !plain || b.dispose.is_some() || !fits {
            self.release(ptr);
            return Ok(());
        }
        let (check, claim, shared, done) = (
            self.new_block(),
            self.new_block(),
            self.new_block(),
            self.new_block(),
        );
        // A count of one is the only reference; a static box's is negative.
        let count = self.load(ptr, COUNT_OFFSET);
        let one = self.constant(1);
        let unique = self.cmp(Cond::Eq, count, one);
        self.end(
            Term::Branch {
                cond: unique,
                then: check,
                otherwise: shared,
            },
            Some(check),
        );
        // A local of a record type may hold a subtype's larger box.
        let header = self.load(ptr, TYPE_INDEX_OFFSET);
        let index = self.constant(type_index(ty));
        let exact = self.cmp(Cond::Eq, header, index);
        self.end(
            Term::Branch {
                cond: exact,
                then: claim,
                otherwise: shared,
            },
            Some(claim),
        );
        let regs = self.load_stored(ptr, &b.slots, b.form.words());
        self.count_form(&b.form, ty, &regs, Count::Release)?;
        // An empty box holds no references: freed by a trap, it is freed
        // as a buffer is.
        let empty = self.constant(BUFFER_HEADER as i64);
        self.push(Inst::Store {
            src: empty,
            addr: ptr,
            offset: TYPE_INDEX_OFFSET,
        });
        self.push(Inst::Move { dst: t, src: ptr });
        self.end(Term::Jump(done), Some(shared));
        self.release(ptr);
        self.end(Term::Jump(done), Some(done));
        Ok(())
    }

    /// A static empty box: a token that holds no box to reuse.
    fn empty_box(&mut self) -> VReg {
        let mut bytes = Vec::with_capacity(16);
        bytes.extend(STATIC_COUNT.to_le_bytes());
        bytes.extend(BUFFER_HEADER.to_le_bytes());
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

    /// Retains or releases what the registers of a split value hold: each
    /// field's, and a union's member's by its type index.
    fn count_form(
        &mut self,
        f: &Form<'db>,
        ty: Ty<'db>,
        regs: &[VReg],
        how: Count,
    ) -> Result<(), Unsupported> {
        match f {
            Form::Words(l) => {
                let op = match how {
                    Count::Retain => Self::retain,
                    // A long chain of boxes is freed between fibers (§13.5).
                    Count::Release if deferred(self.db, self.program, ty) => Self::release_deferred,
                    Count::Release => Self::release,
                };
                self.count_words(Some(*l), ty, regs, op)
            }
            Form::Fields(fields) => {
                let mut at = 0;
                for (_, t, inner) in fields {
                    let n = inner.words();
                    self.count_form(inner, *t, &regs[at..at + n], how)?;
                    at += n;
                }
                Ok(())
            }
            Form::Union(members) => {
                let done = self.new_block();
                for (m, inner) in members {
                    if !counted_form(inner) {
                        continue;
                    }
                    let (hit, next) = (self.new_block(), self.new_block());
                    let index = self.constant(type_index(*m));
                    let same = self.cmp(Cond::Eq, regs[0], index);
                    let term = Term::Branch {
                        cond: same,
                        then: hit,
                        otherwise: next,
                    };
                    self.end(term, Some(hit));
                    self.count_form(inner, *m, &regs[1..1 + inner.words()], how)?;
                    self.end(Term::Jump(done), Some(next));
                }
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
        }
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

    /// A new box as `alloc` makes it, in the empty box a reclaim kept in
    /// `token` when it holds one, whose count is one already; a static box
    /// holds none.
    fn alloc_in(&mut self, token: VReg, size: u32, index: i64) -> VReg {
        let ptr = self.reg();
        let (reuse, fresh, done) = (self.new_block(), self.new_block(), self.new_block());
        let counted = self.counted(token);
        self.end(
            Term::Branch {
                cond: counted,
                then: reuse,
                otherwise: fresh,
            },
            Some(reuse),
        );
        let header = self.constant(index);
        self.push(Inst::Store {
            src: header,
            addr: token,
            offset: TYPE_INDEX_OFFSET,
        });
        self.push(Inst::Move {
            dst: ptr,
            src: token,
        });
        self.end(Term::Jump(done), Some(fresh));
        let new = self.alloc(size, index);
        self.push(Inst::Move { dst: ptr, src: new });
        self.end(Term::Jump(done), Some(done));
        ptr
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

    /// The words a read gives a local, from where the value is: `from` is
    /// its form when it is split in registers. A record or union stored
    /// flat is loaded into a split local, borrowed, and boxed for one that
    /// is not split, a value of its own, as is a split union's member.
    fn take(
        &mut self,
        dst: Local,
        found: Found<'db>,
        from: Option<Form<'db>>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let ty = self.local_ty(dst);
        let (values, from) = match found {
            Found::Words(values) => (values, from),
            Found::Stored { ptr, form, slots } => {
                (self.load_stored(ptr, &slots, form.words()), Some(form))
            }
        };
        match (self.forms[dst.index()].clone(), from) {
            (Some(form), None) => self.unboxed(ty, &form, &values),
            // A cycle's edge has a form of its own.
            (Some(form), Some(f)) if form != f && words_form(&f) => {
                self.unboxed(ty, &form, &values)
            }
            (Some(form), Some(f)) if form != f => {
                self.fresh = Some(dst);
                self.count_form(&f, ty, &values, Count::Retain)?;
                let words = self.boxed(ty, &f, &values)?;
                self.owned_fields(ty, &form, &words)
            }
            (None, Some(f)) if !words_form(&f) => {
                self.fresh = Some(dst);
                self.count_form(&f, ty, &values, Count::Retain)?;
                self.boxed(ty, &f, &values)
            }
            _ => Ok(values),
        }
    }

    fn rvalue(&mut self, dst: Local, rvalue: &Rvalue<'db>) -> Result<Vec<VReg>, Unsupported> {
        let ty = self.local_ty(dst);
        match rvalue {
            Rvalue::Use(op) if self.forms[dst.index()].is_some() => self.split_operand(op, ty),
            Rvalue::Use(op) => self.operand(op, ty),
            // A record read from its box into a split local is loaded. A
            // split union read into a local that is not split has its
            // member boxed, a value of its own.
            Rvalue::Read(place) => {
                let found = self.find(place)?;
                let from = self.split_form(place);
                self.take(dst, found, from)
            }
            Rvalue::Convert(op) => {
                let from = self.operand_ty(op, ty);
                // Into a union split in registers: the member's type index
                // and words.
                if let Some(form @ Form::Union(_)) = self.forms[dst.index()].clone() {
                    if from == ty {
                        return self.split_operand(op, ty);
                    }
                    let member = self.member_of(from, ty);
                    let f = form.member(member).ok_or("this conversion")?.clone();
                    let mut values = vec![self.constant(type_index(member))];
                    values.extend(match f {
                        Form::Words(_) => self.operand(op, from)?,
                        _ => self.split_operand(op, from)?,
                    });
                    while values.len() < form.words() {
                        values.push(self.constant(0));
                    }
                    return Ok(values);
                }
                // Out of a split union, to a member a test established.
                if let Operand::Local(l) = op
                    && let Some(form @ Form::Union(_)) = self.forms[l.index()].clone()
                    && let Some(f) = form.member(ty)
                {
                    let regs = self.locals[l.index()].clone();
                    let payload = regs[1..1 + f.words()].to_vec();
                    return match self.forms[dst.index()] {
                        Some(_) => Ok(payload),
                        None => self.boxed(ty, f, &payload),
                    };
                }
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
            // A split record is its fields' words, and needs no box.
            Rvalue::Record { fields, reuse, .. } if self.forms[dst.index()].is_some() => {
                if let Some(token) = reuse {
                    self.count(*token, Count::Release)?;
                }
                let Some(Form::Fields(places)) = self.forms[dst.index()].clone() else {
                    return Err("records of this type");
                };
                let mut values = Vec::new();
                for (name, ty, form) in places {
                    let (_, op) = fields
                        .iter()
                        .find(|(n, _)| *n == name)
                        .ok_or("records of this type")?;
                    values.extend(match form {
                        Form::Words(_) => self.operand(op, ty)?,
                        _ => self.split_value(op, ty, &form)?,
                    });
                }
                Ok(values)
            }
            Rvalue::Record {
                ty: record,
                fields,
                dispose,
                reuse,
            } => {
                let b = box_form(self.db, self.program, *record).ok_or("records of this type")?;
                self.describe(*record)?;
                let Form::Fields(places) = &b.form else {
                    return Err("records of this type");
                };
                let mut regs = Vec::new();
                for (name, t, f) in places {
                    let (_, op) = fields
                        .iter()
                        .find(|(n, _)| n == name)
                        .ok_or("records of this type")?;
                    regs.extend(match f {
                        Form::Words(_) => self.operand(op, *t)?,
                        _ => self.split_value(op, *t, f)?,
                    });
                }
                let ptr = match reuse {
                    Some(token) => {
                        let token = word(&self.locals[token.index()])?;
                        self.alloc_in(token, b.size, type_index(*record))
                    }
                    None => self.alloc(b.size, type_index(*record)),
                };
                self.store_box(&b, ptr, &regs);
                // The box holds the address of its dispose code, which the
                // runtime gives generated code when the count reaches zero.
                if let Some(code) = dispose {
                    let at = b.dispose.ok_or("records of this type")?;
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
                        .map(|op| self.element_value(op, element))
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut list = self.empty(ty, LIST_SIZE)?;
                    for words in values {
                        let [w0, w1] = self.pass_element(words);
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
                let found = self.element(ptr, list_ty, index)?;
                self.take(dst, found, None)
            }
            Rvalue::MapGet { map, key, boxed } => {
                let map_ty = self.place_ty(map)?;
                let Some((Builtin::Map, &[k, v])) = map_ty.as_builtin(self.db) else {
                    return Err("collections of this type");
                };
                self.describe(map_ty)?;
                let ptr = word(&self.read(map)?)?;
                let [k0, k1] = self.key(key, k)?;
                let at = self.runtime(RuntimeFn::MapGet, vec![ptr, k0, k1]);
                self.option(dst, at, v, ty, *boxed)
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
                let b = box_form(self.db, self.program, *env).ok_or("captures of this type")?;
                let Form::Fields(places) = &b.form else {
                    return Err("captures of this type");
                };
                // An environment on the side stack borrows what it holds.
                let borrows = *placement == ClosurePlacement::SideStack;
                let mut regs = Vec::new();
                for (name, t, f) in places {
                    let i: usize = name
                        .text(self.db)
                        .parse()
                        .map_err(|_| "captures of this type")?;
                    let op = captures.get(i).ok_or("captures of this type")?;
                    regs.extend(match (f, op) {
                        (Form::Words(_), _) => self.operand(op, *t)?,
                        (_, Operand::Local(l)) if borrows => {
                            let own = self.forms[l.index()].clone();
                            let words = self.locals[l.index()].clone();
                            let from = match own {
                                Some(own) => own,
                                None => Form::Words(self.layout_of(*t)?),
                            };
                            self.lend(*t, &from, f, &words)?
                        }
                        _ => self.split_value(op, *t, f)?,
                    });
                }
                let index = type_index(*env);
                let ptr = match placement {
                    ClosurePlacement::Heap => {
                        self.describe(*env)?;
                        self.alloc(b.size, index)
                    }
                    ClosurePlacement::SideStack => {
                        let ptr = self.reg();
                        self.push(Inst::SidePush {
                            dst: ptr,
                            size: b.size,
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
                self.store_box(&b, ptr, &regs);
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
            // The value read from a ref cell, borrowed: found as an element
            // is, stored flat or in its layout's words.
            Rvalue::Intrinsic(Intrinsic::RefValue, _) => {
                let ptr = self.scratch();
                let found = match ref_storage(self.db, self.program, ty) {
                    Some((_, slots)) => {
                        let form = form(self.db, self.program, ty).ok_or("records of this type")?;
                        Found::Stored { ptr, form, slots }
                    }
                    None => {
                        let words = self.layout_of(ty)?.words();
                        Found::Words((0..words).map(|k| self.load(ptr, 8 * k as i32)).collect())
                    }
                };
                self.take(dst, found, None)
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
    /// caller keeps the signal's. The handler runs where the signal is
    /// emitted, so a trap in it goes on from there: to the block returned,
    /// which the caller ends with `pass_trap` once it has released what it
    /// holds.
    fn deliver(&mut self, w0: VReg, info: VReg) -> LirBlockId {
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
        let trapped = self.new_block();
        // A handler of one word takes a record: the signal's box.
        self.retain(w0);
        self.push(Inst::TryCallIndirect {
            callee: code,
            args: vec![env, w0],
            dsts: Vec::new(),
            handlers: vec![(HandlerKind::Trap, trapped)],
        });
        self.end(Term::Jump(left), Some(without));
        self.push(Inst::TryCallIndirect {
            callee: code,
            args: vec![env],
            dsts: Vec::new(),
            handlers: vec![(HandlerKind::Trap, trapped)],
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
        trapped
    }

    /// Ends the block a trap in a signal handler went to: the handler is
    /// left, and the trap goes on to the trap handler around the emitting
    /// code, in this function or past it (§8.3.1).
    fn pass_trap(&mut self, next: LirBlockId) {
        self.push(Inst::CallRuntime {
            func: RuntimeFn::SignalLeave,
            args: Vec::new(),
            dsts: Vec::new(),
        });
        let term = match self.catch {
            Some(handler) => Term::Jump(block(handler)),
            None => Term::Rethrow,
        };
        self.end(term, Some(next));
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

    /// The side-stack words of the C calls' arguments, and of the elements
    /// of more than two words passed to the runtime, at least `words`.
    fn c_buffer(&mut self, words: u32) -> VReg {
        let reg = match self.c_buffer {
            Some((reg, _)) => reg,
            None => self.reg(),
        };
        let most = self.c_buffer.map_or(0, |(_, w)| w).max(words);
        self.c_buffer = Some((reg, most));
        reg
    }

    /// A call of a C function with the arguments of its parameters that
    /// are no out parameters (Specification §16.3): its C result's word,
    /// none for `()`. The out parameters stay in the C buffer and `errno`
    /// in the scratch words.
    fn c_call(
        &mut self,
        item: ItemId<'db>,
        args: &[Operand<'db>],
    ) -> Result<Vec<VReg>, Unsupported> {
        let (db, program) = (self.db, self.program);
        let (params, result) = crag_types::c_signature(db, program, item);
        let info = crag_hir::c_function_info(db, item).ok_or("C functions without an import")?;
        let unsupported = "C parameters or results of this type";
        let result_kind = match CForm::of(db, result) {
            CForm::Void => c_kind::VOID,
            CForm::CStr | CForm::OptionCStr | CForm::Str | CForm::OptionStr => c_kind::PTR,
            CForm::Float(_) => c_kind::F64,
            CForm::Value => c_kind_of(db, result).ok_or(unsupported)?,
            CForm::Invalid => return Err(unsupported),
        };
        let mut desc = vec![params.len() as u8, result_kind];
        // A word per parameter, and `errno`.
        let buffer = self.c_buffer(params.len() as u32 + 1);
        let mut args = args.iter();
        for (i, &ty) in params.iter().enumerate() {
            let offset = 8 * i as i32;
            if let Some(inner) = crag_types::c_out(db, ty) {
                desc.push(c_kind::OUT | c_kind_of(db, inner).ok_or(unsupported)?);
                let zero = self.constant(0);
                self.push(Inst::Store {
                    src: zero,
                    addr: buffer,
                    offset,
                });
                continue;
            }
            let arg = args.next().ok_or("C calls with missing arguments")?;
            let words = self.operand(arg, ty)?;
            let (kind, src) = match CForm::of(db, ty) {
                CForm::CStr => (c_kind::CSTR, word(&words)?),
                // The payload: the box, or zero for `Empty`.
                CForm::OptionCStr => (c_kind::OPT_CSTR, *words.get(1).ok_or(unsupported)?),
                CForm::Float(_) => (c_kind::F64, self.float_word(ty, &words)?),
                CForm::Value => (c_kind_of(db, ty).ok_or(unsupported)?, word(&words)?),
                _ => return Err(unsupported),
            };
            desc.push(kind);
            self.push(Inst::Store {
                src,
                addr: buffer,
                offset,
            });
        }
        let files = program
            .packages(db)
            .native_files(item.module(db).path(db), &info.library)
            .ok_or("C libraries the manifest does not declare")?;
        let desc = self.static_data(desc);
        let native = self.natives.len() as u32;
        self.natives.push(NativeSymbol {
            files,
            symbol: item.name(db).text(db).clone(),
            threading: match info.threading {
                Threading::Unsafe => threading::UNSAFE,
                Threading::Safe => threading::SAFE,
                Threading::Bound => threading::BOUND,
            },
        });
        let [library, func] = [true, false].map(|library| {
            let dst = self.reg();
            self.push(Inst::NativeAddr {
                dst,
                native,
                library,
            });
            dst
        });
        let out = self.runtime2(RuntimeFn::CCall, vec![library, func, desc, buffer]);
        // The class of a float result waits for `CClass`.
        let scratch = self.scratch();
        self.push(Inst::Store {
            src: out[1],
            addr: scratch,
            offset: 0,
        });
        Ok(match result_kind {
            c_kind::VOID => Vec::new(),
            _ => vec![out[0]],
        })
    }

    /// The IEEE 754 bits of a `Float` united with tags of non-finite
    /// values (Specification §3.1.4): the payload, or the bits of the tag
    /// the value is.
    fn float_word(&mut self, ty: Ty<'db>, words: &[VReg]) -> Result<VReg, Unsupported> {
        let db = self.db;
        let [index, payload] = words else {
            return Err("floats united with other values");
        };
        let mut bits = *payload;
        for member in ty.members(db) {
            let TyKind::Named(item, _) = member.kind(db) else {
                continue;
            };
            let value = match item.name(db).text(db).as_str() {
                "NaN" => f64::NAN,
                "PosInfinity" => f64::INFINITY,
                "NegInfinity" => f64::NEG_INFINITY,
                _ => continue,
            };
            let tag = self.constant(type_index(member));
            let is = self.cmp(Cond::Eq, *index, tag);
            let value = self.constant(value.to_bits() as i64);
            let dst = self.reg();
            self.push(Inst::Select {
                dst,
                cond: is,
                a: value,
                b: bits,
            });
            bits = dst;
        }
        Ok(bits)
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
                let words = self.ref_value(value, value_ty)?;
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
                let words = self.ref_value(value, value_ty)?;
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
            (Intrinsic::CCall(item), args) => self.c_call(item, args),
            (Intrinsic::COut(index), []) => {
                let buffer = self.c_buffer(index + 1);
                Ok(vec![self.load(buffer, 8 * index as i32)])
            }
            (Intrinsic::CClass, []) => {
                let scratch = self.scratch();
                Ok(vec![self.load(scratch, 0)])
            }
            (Intrinsic::CStrOf { nul }, [address]) => {
                let address = word(&self.operand(address, int)?)?;
                let nul = self.constant(i64::from(nul));
                Ok(self
                    .runtime2(RuntimeFn::CStrOf, vec![address, nul])
                    .to_vec())
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
                let at = self.position(expr).map_or(NO_POSITION as i64, i64::from);
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
                let words = self.element_value(value, element)?;
                let [w0, w1] = self.pass_element(words);
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
                let [k0, k1] = self.key(key, k)?;
                let [v0, v1] = match (value, v) {
                    ([value], Some(v)) => {
                        let value = self.element_value(value, v)?;
                        self.pass_element(value)
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
                let [k0, k1] = self.key(key, k)?;
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
                let words = self.element_value(value, element)?;
                let [w0, w1] = self.pass_element(words);
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
                let trapped = self.deliver(w0, info);
                self.count_words(signal_layout, signal_ty, &words, Self::release)?;
                self.end(Term::Jump(done), Some(trapped));
                self.count_words(signal_layout, signal_ty, &words, Self::release)?;
                self.pass_trap(done);
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
                let trapped = self.deliver(w0, info);
                self.end(Term::Jump(head), Some(trapped));
                self.pass_trap(done);
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
                let words = self.ref_value(value, ty)?;
                let [w0, w1] = self.pad(words);
                let old = self.runtime2(RuntimeFn::RefSwap, vec![cell, list, w0, w1]);
                // The old value stored flat, with references of its own,
                // goes into a box that takes them.
                if let Some((_, slots)) = ref_storage(self.db, self.program, ty) {
                    let f = form(self.db, self.program, ty).ok_or("records of this type")?;
                    let out = self.scratch();
                    for (k, &src) in old.iter().enumerate() {
                        self.push(Inst::Store {
                            src,
                            addr: out,
                            offset: 8 * k as i32,
                        });
                    }
                    let regs = self.load_stored(out, &slots, f.words());
                    return self.boxed(ty, &f, &regs);
                }
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

    /// The words of the value at a place, borrowed: a record or union
    /// stored inline in a box is none.
    fn read(&mut self, place: &Place<'db>) -> Result<Vec<VReg>, Unsupported> {
        match self.find(place)? {
            Found::Words(values) => Ok(values),
            Found::Stored { ptr, form, slots } if words_form(&form) => {
                Ok(self.load_stored(ptr, &slots, form.words()))
            }
            Found::Stored { .. } => Err("this place"),
        }
    }

    /// Where the value at a place is: in registers, or stored inline in a
    /// box, a record's or a union's form there.
    fn find(&mut self, place: &Place<'db>) -> Result<Found<'db>, Unsupported> {
        let db = self.db;
        let mut ty = self.local_ty(place.local);
        let mut values = self.split_operand(&Operand::Local(place.local), ty)?;
        let mut path = &place.path[..];
        // A split local's fields are its registers.
        if let Some(form) = &self.forms[place.local.index()] {
            let (at, t, f, rest) = place_form(form, ty, path).ok_or("this place")?;
            values = values[at..at + f.words()].to_vec();
            ty = t;
            path = &place.path[place.path.len() - rest.len()..];
        }
        let mut stored: Option<(VReg, Form<'db>, Vec<Slot>)> = None;
        for step in path {
            // Within a box's storage, a field or a member is where its
            // slots say.
            if let Some((ptr, form, slots)) = stored.take() {
                let (t, f, slots) = match step {
                    Step::Field(name) => {
                        let (at, t, f) = form.field(*name).ok_or("this place")?;
                        (t, f.clone(), select(&slots, at, f.words()))
                    }
                    Step::As(t) if *t == ty => (ty, form, slots),
                    Step::As(t) => {
                        let f = form.member(*t).ok_or("this conversion")?.clone();
                        (*t, f, member_slots(&slots, *t).ok_or("this conversion")?)
                    }
                    _ => return Err("this place"),
                };
                ty = t;
                match f {
                    Form::Words(_) => values = self.load_stored(ptr, &slots, f.words()),
                    f => stored = Some((ptr, f, slots)),
                }
                continue;
            }
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
                    let b = box_form(db, self.program, ty).ok_or("records of this type")?;
                    let (at, t, f) = b.form.field(*name).ok_or("records of this type")?;
                    let slots = select(&b.slots, at, f.words());
                    let ptr = word(&values)?;
                    ty = t;
                    match f {
                        Form::Words(_) => values = self.load_stored(ptr, &slots, f.words()),
                        f => stored = Some((ptr, f.clone(), slots)),
                    }
                }
                Step::Elem(_) | Step::ElemBack(_) => {
                    let list = word(&values)?;
                    let index = match step {
                        Step::Elem(i) => self.constant(i64::from(*i)),
                        Step::ElemBack(i) => {
                            let len = self.load(list, LEN_OFFSET);
                            let from_end = self.constant(i64::from(*i) + 1);
                            self.bin(LirBin::Sub, len, from_end)
                        }
                        _ => unreachable!("an element step"),
                    };
                    match self.element(list, ty, index)? {
                        Found::Words(words) => values = words,
                        Found::Stored { ptr, form, slots } => stored = Some((ptr, form, slots)),
                    }
                    ty = element_of(db, ty)?;
                }
                Step::Slice { .. } => return Err("this place"),
            }
        }
        Ok(match stored {
            Some((ptr, form, slots)) => Found::Stored { ptr, form, slots },
            None => Found::Words(values),
        })
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
                    if !word_keys(self.db, self.program, *key) && !is_text(self.db, *key) =>
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

    /// The words of a map or set key, padded to two: as the map stores it,
    /// packed when it takes fewer bytes than its word. A `Float` key -0.0
    /// becomes 0.0, which it equals, so that equal keys have equal words
    /// (Specification §12.2).
    fn key(&mut self, key: &Operand<'db>, ty: Ty<'db>) -> Result<[VReg; 2], Unsupported> {
        let mut words = self.element_value(key, ty)?;
        if matches!(ty.as_builtin(self.db), Some((Builtin::Float, _))) {
            let zero = self.constant(0);
            words[0] = self.bin(LirBin::FAdd, words[0], zero);
        }
        Ok(self.pad(words))
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

    /// The words of a value that goes into a list, map or grid, which take
    /// the operand's references: a value stored flat there packed into its
    /// storage form (`split::element_storage`), anything else in its
    /// layout's words.
    fn element_value(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        let Some((size, slots)) = element_storage(self.db, self.program, ty) else {
            return self.operand(op, ty);
        };
        let regs = match form(self.db, self.program, ty) {
            Some(_) => self.flat_value(op, ty)?,
            None => self.operand(op, ty)?,
        };
        Ok(self.pack(&slots, size, &regs))
    }

    /// The words of a value that goes into a ref cell, which take the
    /// operand's references: a value stored flat there packed into its
    /// storage form (`split::ref_storage`), anything else in its layout's
    /// words.
    fn ref_value(&mut self, op: &Operand<'db>, ty: Ty<'db>) -> Result<Vec<VReg>, Unsupported> {
        match ref_storage(self.db, self.program, ty) {
            Some((size, slots)) => {
                let regs = self.flat_value(op, ty)?;
                Ok(self.pack(&slots, size, &regs))
            }
            None => self.operand(op, ty),
        }
    }

    /// An element's words as the two arguments of a runtime function: as
    /// `pad` gives them, or more than two at the address of side-stack
    /// words that hold them (`crag_abi::ElementLayout`), valid until the
    /// next element is passed.
    fn pass_element(&mut self, words: Vec<VReg>) -> [VReg; 2] {
        if words.len() <= 2 {
            return self.pad(words);
        }
        let buffer = self.c_buffer(words.len() as u32);
        for (k, src) in words.into_iter().enumerate() {
            self.push(Inst::Store {
                src,
                addr: buffer,
                offset: 8 * k as i32,
            });
        }
        [buffer, self.constant(0)]
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
            let k = self.key(k, key)?;
            let v = match (v, value) {
                (Some(v), Some(value)) => self.element_value(v, value)?,
                _ => Vec::new(),
            };
            words.push((k, v));
        }
        let mut map = self.empty(ty, MAP_SIZE)?;
        for ([k0, k1], v) in words {
            let [v0, v1] = self.pass_element(v);
            map = self.runtime(RuntimeFn::MapInsert, vec![map, k0, k1, v0, v1]);
        }
        // A key written twice releases the value it had first.
        self.dispose();
        Ok(map)
    }

    /// Where element `index` of a list of type `ty` is: its words loaded,
    /// borrowed, or a record or union the list stores flat.
    fn element(&mut self, list: VReg, ty: Ty<'db>, index: VReg) -> Result<Found<'db>, Unsupported> {
        let (db, program) = (self.db, self.program);
        let element = element_of(db, ty)?;
        self.describe(ty)?;
        let at = self.runtime(RuntimeFn::ListElem, vec![list, index]);
        if let Some((_, slots)) = element_storage(db, program, element) {
            let form = element_form(db, program, element).ok_or("values of this type")?;
            // A number or a tag is loaded at once, as its word.
            if words_form(&form) {
                return Ok(Found::Words(self.load_stored(at, &slots, form.words())));
            }
            return Ok(Found::Stored {
                ptr: at,
                form,
                slots,
            });
        }
        let words = self.layout_of(element)?.words();
        Ok(Found::Words(
            (0..words).map(|k| self.load(at, 8 * k as i32)).collect(),
        ))
    }

    /// The `Option` of a map's value for `dst`: the value at `at`, or
    /// `Empty` when `at` is null. A `boxed` value gets a reference of its
    /// own, which its member box takes; so does a value the map stores
    /// flat, which is boxed.
    fn option(
        &mut self,
        dst: Local,
        at: VReg,
        value: Ty<'db>,
        ty: Ty<'db>,
        boxed: bool,
    ) -> Result<Vec<VReg>, Unsupported> {
        let db = self.db;
        // Typed as the value itself, the key is known to be there.
        if ty == value && !boxed {
            return self.map_value(dst, at, value);
        }
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
        let found = self.map_value(dst, at, value)?;
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

    /// The words of a map's value at `at` for `dst`: borrowed, or a value
    /// stored flat in a box of its own, which a retain of `dst` takes.
    fn map_value(
        &mut self,
        dst: Local,
        at: VReg,
        value: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let (db, program) = (self.db, self.program);
        let Some((_, slots)) = element_storage(db, program, value) else {
            let words = self.layout_of(value)?.words();
            return Ok((0..words).map(|k| self.load(at, 8 * k as i32)).collect());
        };
        let f = element_form(db, program, value).ok_or("values of this type")?;
        let regs = self.load_stored(at, &slots, f.words());
        if words_form(&f) {
            return Ok(regs);
        }
        self.fresh = Some(dst);
        self.count_form(&f, value, &regs, Count::Retain)?;
        self.boxed(value, &f, &regs)
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
        // A conditioned alias's values and its target's are the same.
        let plain = |ty| crag_types::unrefined(self.db, self.program, ty);
        if f == t && plain(from) == plain(to) && !matches!(f, Layout::Tag | Layout::Union) {
            return Ok(values);
        }
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
        if let Some(fresh) = self.fresh.take() {
            self.count(fresh, Count::Release)?;
        }
        match term {
            Terminator::Jump(b) => self.end(Term::Jump(block(*b)), None),
            Terminator::Guard {
                func,
                inlined,
                fallback,
            } => {
                // The code the slot holds now, and the code loaded with
                // this function, which the copy was made from.
                if !self.calls.contains(func) {
                    self.calls.push(*func);
                }
                let (now, loaded) = (self.reg(), self.reg());
                self.push(Inst::FuncAddr {
                    dst: now,
                    func: self.slot(*func),
                    params: 0,
                    returns: 0,
                });
                self.push(Inst::FuncAddr {
                    dst: loaded,
                    func: CallTarget::Direct(func_id(*func)),
                    params: 0,
                    returns: 0,
                });
                let same = self.cmp(Cond::Eq, now, loaded);
                let term = Term::Branch {
                    cond: same,
                    then: block(*inlined),
                    otherwise: block(*fallback),
                };
                self.end(term, None);
            }
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
                self.layouts[dst.index()].ok_or("values of this type")?;
                let handlers = handlers(unwind, catch);
                match flat_result(self.db, self.program, *func).clone() {
                    None => {
                        let dsts = self.locals[dst.index()].clone();
                        self.call(*func, args, dsts, handlers);
                    }
                    // A record given by value goes into the local's
                    // registers, or into a box.
                    Some((size, slots)) => {
                        let words = self.call_flat(*func, args, size, handlers);
                        let ty = self.local_ty(*dst);
                        let f = form(self.db, self.program, ty).ok_or("records of this type")?;
                        let regs = self.unpack(&slots, &words, f.words());
                        let values = match self.forms[dst.index()] {
                            Some(_) => regs,
                            None => self.boxed(ty, &f, &regs)?,
                        };
                        self.assign(*dst, values)?;
                    }
                }
                self.end(Term::Jump(block(*target)), None);
            }
            Terminator::TailCall { func, args, .. } => {
                let mut args = self.arguments(*func, args)?;
                let callee = flat_result(self.db, self.program, *func).clone();
                if callee == self.result {
                    // A result given by value goes where this function's
                    // caller wants it.
                    args.splice(0..0, self.sret);
                    let term = Term::TailCall {
                        func: self.slot(*func),
                        args,
                    };
                    self.end(term, None);
                    return Ok(());
                }
                // The callee gives its result otherwise: a call, then the
                // result returned as this function gives it.
                let ty = self.mir.result;
                let f = form(self.db, self.program, ty).ok_or("records of this type")?;
                match callee {
                    Some((size, slots)) => {
                        let words = self.call_flat(*func, args, size, Vec::new());
                        let regs = self.unpack(&slots, &words, f.words());
                        let values = self.boxed(ty, &f, &regs)?;
                        self.give(values, true)?;
                    }
                    None => {
                        let words = self.call_boxed(*func, args, ty)?;
                        let regs = self.owned_fields(ty, &f, &words)?;
                        self.give_flat(regs)?;
                    }
                }
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
                // A function value gives a record in its box, which this
                // function may give by value.
                if self.result.is_some() {
                    let ty = self.mir.result;
                    let f = form(self.db, self.program, ty).ok_or("records of this type")?;
                    let words: Vec<VReg> = (0..self.layout_of(ty)?.words())
                        .map(|_| self.reg())
                        .collect();
                    self.push(Inst::CallIndirect {
                        callee: code,
                        args,
                        dsts: words.clone(),
                    });
                    let regs = self.owned_fields(ty, &f, &words)?;
                    return self.give_flat(regs);
                }
                let term = Term::TailCallIndirect { callee: code, args };
                self.end(term, None);
            }
            Terminator::Return(op) => {
                if self.result.is_some() {
                    let regs = self.flat_value(op, self.mir.result)?;
                    return self.give_flat(regs);
                }
                let values = self.operand(op, self.mir.result)?;
                if values.len() != returns {
                    return Err("this conversion");
                }
                self.give(values, matches!(op, Operand::Local(_)))?;
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
                    TrapKind::NotFinite => AbiTrap::NotFinite,
                    TrapKind::ForeignFault => AbiTrap::ForeignFault,
                };
                // The byte offset of the expression in the module's source,
                // with the detail it names in the upper half.
                let position = match site {
                    Some(e) => self.position(*e),
                    None => detail.as_ref().map(|_| self.scope().1),
                };
                let position = position.map(|at| self.origin(at));
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
    /// Returns the words of the result, which a module value's cell keeps
    /// too, with a reference of its own unless they are a constant's.
    fn give(&mut self, values: Vec<VReg>, counted: bool) -> Result<(), Unsupported> {
        if let Some(cell) = self.cell {
            self.keep(cell, counted, &values)?;
        }
        self.end(Term::Return(values), None);
        Ok(())
    }

    /// Returns a record given by value from its registers: its storage
    /// form's words, or in the buffer the caller gave.
    fn give_flat(&mut self, regs: Vec<VReg>) -> Result<(), Unsupported> {
        let (size, slots) = self.result.clone().ok_or("this conversion")?;
        let words = self.pack(&slots, size, &regs);
        let values = match self.sret {
            Some(buffer) => {
                for (k, src) in words.into_iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: buffer,
                        offset: 8 * k as i32,
                    });
                }
                Vec::new()
            }
            None => words,
        };
        self.end(Term::Return(values), None);
        Ok(())
    }

    /// Calls an instance.
    fn call(
        &mut self,
        func: InstanceKey<'db>,
        args: Vec<VReg>,
        dsts: Vec<VReg>,
        handlers: Vec<(HandlerKind, LirBlockId)>,
    ) {
        let func = self.slot(func);
        self.push(match handlers.is_empty() {
            true => Inst::Call { func, args, dsts },
            false => Inst::TryCall {
                func,
                args,
                dsts,
                handlers,
            },
        });
    }

    /// Calls an instance that gives a record of `size` bytes by value:
    /// the words of its storage form, which one of more than two words
    /// writes to a buffer on this function's side stack.
    fn call_flat(
        &mut self,
        func: InstanceKey<'db>,
        mut args: Vec<VReg>,
        size: u32,
        handlers: Vec<(HandlerKind, LirBlockId)>,
    ) -> Vec<VReg> {
        let n = size.div_ceil(8) as usize;
        if n <= 2 {
            let dsts: Vec<VReg> = (0..n).map(|_| self.reg()).collect();
            self.call(func, args, dsts.clone(), handlers);
            return dsts;
        }
        let buffer = *self.results.get_or_insert_with(|| {
            self.vregs += 1;
            VReg(self.vregs - 1)
        });
        args.insert(0, buffer);
        self.call(func, args, Vec::new(), handlers);
        (0..n).map(|k| self.load(buffer, 8 * k as i32)).collect()
    }

    /// The fields of a record in a box the code owns, loaded with
    /// references of their own as it gives up the box's.
    fn owned_fields(
        &mut self,
        ty: Ty<'db>,
        f: &Form<'db>,
        words: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        let regs = self.unboxed(ty, f, words)?;
        self.count_form(f, ty, &regs, Count::Retain)?;
        let layout = self.layout_of(ty)?;
        self.count_form(&Form::Words(layout), ty, words, Count::Release)?;
        Ok(regs)
    }

    /// Calls an instance that gives its result in its layout's words.
    fn call_boxed(
        &mut self,
        func: InstanceKey<'db>,
        args: Vec<VReg>,
        ty: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let dsts: Vec<VReg> = (0..self.layout_of(ty)?.words())
            .map(|_| self.reg())
            .collect();
        self.call(func, args, dsts.clone(), Vec::new());
        Ok(dsts)
    }

    fn keep(&mut self, cell: SlotKey, counted: bool, values: &[VReg]) -> Result<(), Unsupported> {
        let addr = self.reg();
        self.push(Inst::CellAddr { dst: addr, cell });
        for (i, &src) in values.iter().enumerate() {
            let offset = CELL_VALUE_OFFSET + 8 * i as i32;
            self.push(Inst::Store { src, addr, offset });
        }
        // The words returned, a split local boxed among them.
        if counted {
            let ty = self.mir.result;
            let layout = self.layout_of(ty)?;
            self.count_words(Some(layout), ty, values, Self::retain)?;
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
            && crag_hir::c_function(db, item).is_none()
            && !crag_mir::has_derived_code(db, func)
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
        // Records pass by value to the parameters of the callee's body
        // that take them so.
        let flat = flat_params(db, self.program, func);
        let body = crag_mir::mir(db, self.program, func, Tier::Baseline);
        let mut words = Vec::new();
        for (k, (arg, param)) in args.iter().zip(params).enumerate() {
            if flat.get(k) == Some(&true)
                && let Some(body) = body
            {
                let ty = body.locals[k].ty;
                words.extend(self.flat_argument(arg, ty)?);
                continue;
            }
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
        let (values, record) = match self.find(place)? {
            Found::Words(values) => (values, self.split_record(place)),
            Found::Stored {
                form: Form::Fields(_),
                ..
            } => (Vec::new(), true),
            // A union's type index, and its member's words.
            Found::Stored { ptr, form, slots } => {
                (self.load_stored(ptr, &slots, form.words()), false)
            }
        };
        let ty = self.place_ty(place)?;
        // A split or stored record is of its own type alone.
        if record {
            let hit = cases
                .iter()
                .find(|&&(case, _)| crag_types::tested(db, self.program, ty, case));
            let target = hit.map_or(otherwise, |&(_, b)| block(b));
            self.end(Term::Jump(target), None);
            return Ok(());
        }
        let members = ty.members(db);
        let shape = self.layout_of(ty)?;
        for &(case, target) in cases {
            // Every value of the place's type has the case's.
            if crag_types::tested(db, self.program, ty, case) {
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

    /// The form of the value at a place when it is a record or a union
    /// split in registers.
    fn split_form(&self, place: &Place<'db>) -> Option<Form<'db>> {
        let form = self.forms[place.local.index()].as_ref()?;
        let ty = self.local_ty(place.local);
        match place_form(form, ty, &place.path)? {
            (_, _, f @ (Form::Fields(_) | Form::Union(_)), _) => Some(f.clone()),
            _ => None,
        }
    }

    /// Whether the value at a place is a record split in registers.
    fn split_record(&self, place: &Place<'db>) -> bool {
        let Some(form) = &self.forms[place.local.index()] else {
            return false;
        };
        let ty = self.local_ty(place.local);
        matches!(
            place_form(form, ty, &place.path),
            Some((_, _, Form::Fields(_), _))
        )
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
