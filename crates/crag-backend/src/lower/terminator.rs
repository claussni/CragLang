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

//! Terminators: returns, calls and tail calls with their arguments in
//! the forms the callee takes, cells, and switches.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    pub(super) fn terminator(
        &mut self,
        term: &Terminator<'db>,
        returns: usize,
    ) -> Result<(), Unsupported> {
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
    pub(super) fn owned_fields(
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
    pub(super) fn cell_entry(&mut self, cell: SlotKey, returns: usize) {
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
        let Some((params, ..)) = fn_ty.as_fn(self.db) else {
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
                    let index = self.constant(self.index(case));
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
                    let index = self.constant(self.index(member));
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
    pub(super) fn split_form(&self, place: &Place<'db>) -> Option<Form<'db>> {
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
