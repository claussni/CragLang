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

//! Rvalues: each kind of value a statement computes, with signals,
//! cells, handles and calls into C.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    pub(super) fn rvalue(
        &mut self,
        dst: Local,
        rvalue: &Rvalue<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
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
                    let mut values = vec![self.constant(self.index(member))];
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
                        self.alloc_in(token, b.size, self.index(*record))
                    }
                    None => self.alloc(b.size, self.index(*record)),
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
                // An `Expr`'s tree comes before the captures.
                let tree = places
                    .iter()
                    .filter(|(n, ..)| n.text(self.db).starts_with('$'))
                    .count();
                let mut regs = Vec::new();
                for (name, t, f) in places {
                    let i = match name.text(self.db).as_str() {
                        TREE_HASH => 0,
                        TREE => 1,
                        WIRE => 2,
                        BUDGET => 3,
                        n => n.parse::<usize>().map_err(|_| "captures of this type")? + tree,
                    };
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
                let index = self.index(*env);
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
    pub(super) fn cell_value_ty(&self, cell: Ty<'db>) -> Result<Ty<'db>, Unsupported> {
        match cell.as_builtin(self.db) {
            Some((Builtin::Ref | Builtin::Ext, &[value])) => Ok(value),
            _ => Err("cells of this type"),
        }
    }

    /// Static data with the bytes, and its address.
    pub(super) fn static_data(&mut self, bytes: Vec<u8>) -> VReg {
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
    pub(super) fn signal_info(&mut self, ty: Ty<'db>, boxed: bool) -> VReg {
        let name = ty.display(self.db);
        let mut bytes = Vec::new();
        bytes.extend((self.index(ty) as u64).to_le_bytes());
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
    pub(super) fn deliver(&mut self, w0: VReg, info: VReg) -> LirBlockId {
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
    pub(super) fn pass_trap(&mut self, next: LirBlockId) {
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
    pub(super) fn handle_box(
        &mut self,
        ty: Ty<'db>,
        handle: VReg,
    ) -> Result<Vec<VReg>, Unsupported> {
        self.describe(ty)?;
        let ptr = self.alloc(HEADER_SIZE + 8, self.index(ty));
        self.push(Inst::Store {
            src: handle,
            addr: ptr,
            offset: HEADER_SIZE as i32,
        });
        Ok(vec![ptr])
    }

    /// A result of the runtime's sockets as `std.io` takes it: `value`, or
    /// minus the error number when there is one.
    pub(super) fn fd_or_error(&mut self, value: VReg, errno: VReg) -> VReg {
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
    pub(super) fn value_shapes(&mut self, ty: Ty<'db>) -> Result<VReg, Unsupported> {
        let (shapes, root) = crate::shape::shapes(self.db, self.program, ty);
        let mut bytes = root.to_le_bytes().to_vec();
        bytes.extend(shapes.encode());
        let words = self.text_literal(&bytes)?;
        Ok(self.runtime(RuntimeFn::ValueShapes, words))
    }

    /// The two words of a string or bytes operand.
    pub(super) fn text_words(
        &mut self,
        op: &Operand<'db>,
        ty: Ty<'db>,
    ) -> Result<[VReg; 2], Unsupported> {
        let op_ty = self.operand_ty(op, ty);
        match self.operand(op, op_ty)?[..] {
            [w0, w1] => Ok([w0, w1]),
            _ => Err("this operation of the runtime"),
        }
    }

    /// The runtime handle in the box of a `RuntimeStream` or `RuntimeHub`.
    pub(super) fn handle_of(&mut self, handle: &Operand<'db>) -> Result<VReg, Unsupported> {
        let ptr = self.box_of(handle)?;
        Ok(self.load(ptr, HEADER_SIZE as i32))
    }

    /// The box a local of a `Ref` or an `Ext` holds.
    pub(super) fn box_of(&mut self, cell: &Operand<'db>) -> Result<VReg, Unsupported> {
        let Operand::Local(local) = cell else {
            return Err("cells of this type");
        };
        word(&self.locals[local.index()].clone())
    }

    /// The address of the cell in the box a local of a `Ref` holds.
    pub(super) fn cell_addr(&mut self, cell: &Operand<'db>) -> Result<VReg, Unsupported> {
        let Operand::Local(local) = cell else {
            return Err("cells of this type");
        };
        let ptr = word(&self.locals[local.index()].clone())?;
        let header = self.constant(i64::from(HEADER_SIZE));
        Ok(self.bin(LirBin::Add, ptr, header))
    }

    /// The type index of the list of `value`, whose elements the runtime
    /// lays a cell's value out as.
    pub(super) fn cell_list(&mut self, value: Ty<'db>) -> Result<VReg, Unsupported> {
        let list = Ty::new(self.db, TyKind::Builtin(Builtin::List, vec![value]));
        self.describe(list)?;
        Ok(self.constant(self.index(list)))
    }

    /// The index of a type in the descriptor table, as the program the
    /// code is for numbers it (`layout::type_index`).
    pub(super) fn index(&self, ty: Ty<'db>) -> i64 {
        type_index(self.db, self.program, ty)
    }

    /// The scratch words for reads of ref cells.
    pub(super) fn scratch(&mut self) -> VReg {
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
    pub(super) fn c_buffer(&mut self, words: u32) -> VReg {
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
    pub(super) fn c_call(
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
            let tag = self.constant(self.index(member));
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
}
