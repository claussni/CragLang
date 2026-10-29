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

//! The code of the prelude's derived functions for a type whose values hold
//! parts with functions of their own (Specification §19.11).
//!
//! The runtime walks a value by its structure alone and cannot call back
//! into code (Plan §11.6.5). Where a derived `equals`, `compare`, `hash` or
//! `show` meets such a part, `valueEquals[T]` and the others get code for
//! the structure of `T` instead: a record field by field, a union by its
//! member, a list element by element, a map entry by entry. Each part goes
//! to its type's own function where the derived function is called, which
//! the instance carries as its parts and which its walks share, to the
//! code for its structure in turn, or else to the runtime's walk. A record
//! type with subtypes goes by the type of the value's box, as the walk
//! does. Entries of maps and sets are shown in the order the map holds
//! them.

use crag_db::Db;
use crag_hir::{ItemId, ItemKind, Name, Owner, PRELUDE, Program, item_tree, module_index};
use crag_types::{
    Builtin, Derived, Instance, Step, Ty, TyKind, TypeDefKind, derived_parts, fields_of, parent,
    prelude_item, record_subtypes, subst, type_def,
};

use super::{MirBuilder, Start, int};
use crate::ir::{
    BinOp, CmpOp, Constant, Intrinsic, Local, Operand, Place, Rvalue, Statement, Terminator,
    TrapKind,
};
use crate::{Entry, InstanceKey};

/// The expression the calls of derived code name: it has no source.
const SITE: crag_hir::ExprId = crag_hir::ExprId(0);

/// What a hash is multiplied by before the next part is added.
const PRIME: i128 = 0x0100_0000_01b3;

/// The prelude's function without a body that a derived function calls,
/// which walks a value by its structure.
pub(super) fn value_function<'db>(
    db: &'db dyn Db,
    program: Program,
    op: Derived,
) -> Option<ItemId<'db>> {
    let module = *module_index(db, program).modules.get(PRELUDE)?;
    item_tree(db, module)
        .items
        .iter()
        .map(|i| i.id)
        .find(|f| *f.kind(db) == ItemKind::Function && value_op(db, *f) == Some(op))
}

/// Whether an instance is the walk of a derived function that has code for
/// the structure of its type, though the function has no body.
pub fn has_derived_code<'db>(db: &'db dyn Db, instance: InstanceKey<'db>) -> bool {
    match (*instance.owner(db), instance.args(db).as_slice()) {
        (Owner::Item(item), [_]) => {
            *instance.entry(db) == Entry::Body
                && value_op(db, item).is_some()
                && !instance.parts(db).is_empty()
        }
        _ => false,
    }
}

/// The derived function a function of the prelude without a body walks
/// values for, if it is one.
pub(super) fn value_op(db: &dyn Db, function: ItemId<'_>) -> Option<Derived> {
    if function.module(db).path(db) != PRELUDE {
        return None;
    }
    Some(match function.name(db).text(db).as_str() {
        "valueEquals" => Derived::Equals,
        "valueCompare" => Derived::Compare,
        "valueHash" => Derived::Hash,
        "valueShow" => Derived::Show,
        _ => return None,
    })
}

impl<'a, 'db> MirBuilder<'a, 'db> {
    /// The code of `valueEquals[T]` or another for a type that meets a
    /// part with a function of its own: the values, then the code for the
    /// structure of `T`.
    pub(super) fn derived_entry(&mut self, op: Derived, ty: Ty<'db>) -> Option<Start<'a, 'db>> {
        let values: Vec<Local> = (0..op.arity()).map(|_| self.temp(ty)).collect();
        self.params = values.len();
        self.result = self.derived_result(op);
        Some(Box::new(move |b| {
            let values = values.into_iter().map(Operand::Local).collect();
            let out = b.structure(op, ty, values);
            b.terminate(Terminator::Return(out));
        }))
    }

    /// What the walk gives: `Int`, or `Str` for `show`.
    fn derived_result(&self, op: Derived) -> Ty<'db> {
        match op {
            Derived::Show => Ty::builtin(self.db, Builtin::Str),
            _ => self.int(),
        }
    }

    /// What the walk gives for values of a type, which may meet parts with
    /// functions of their own: by code for its structure then.
    pub(super) fn derived(
        &mut self,
        op: Derived,
        ty: Ty<'db>,
        values: Vec<Operand<'db>>,
    ) -> Operand<'db> {
        if !self.reaches(op, ty) {
            return self.walked(op, ty, values);
        }
        let Some(item) = value_function(self.db, self.program, op) else {
            return self.trap(TrapKind::Error, None);
        };
        let code = InstanceKey::new(
            self.db,
            Owner::Item(item),
            vec![ty],
            Vec::new(),
            self.instance.parts(self.db).clone(),
            Entry::Body,
        );
        let result = self.derived_result(op);
        Operand::Local(self.call_code(code, values, result, SITE))
    }

    /// The function of its own a part of a type has where the derived
    /// function was called.
    fn own_part(&self, ty: Ty<'db>) -> Option<Instance<'db>> {
        let parts = self.instance.parts(self.db);
        parts.iter().find(|(t, _)| *t == ty).map(|(_, f)| f.clone())
    }

    /// Whether the derived function of a form, for a type, meets one of
    /// the parts with a function of its own; otherwise the runtime walks
    /// its values by their structure alone.
    pub(super) fn reaches(&self, op: Derived, ty: Ty<'db>) -> bool {
        if self.instance.parts(self.db).is_empty() {
            return false;
        }
        let mut seen = vec![ty];
        let mut pending = derived_parts(self.db, self.program, op, ty);
        while let Some(part) = pending.pop() {
            if seen.contains(&part) {
                continue;
            }
            if self.own_part(part).is_some() {
                return true;
            }
            seen.push(part);
            pending.extend(derived_parts(self.db, self.program, op, part));
        }
        false
    }

    /// What the walk gives for a part: by its type's own function, else as
    /// for the whole.
    fn part(&mut self, op: Derived, ty: Ty<'db>, values: Vec<Operand<'db>>) -> Operand<'db> {
        match self.own_part(ty) {
            Some(own) => self.own(op, &own, ty, values),
            None => self.derived(op, ty, values),
        }
    }

    /// The runtime's walk of values by their structure.
    fn walked(&mut self, op: Derived, ty: Ty<'db>, values: Vec<Operand<'db>>) -> Operand<'db> {
        let intrinsic = match op {
            Derived::Show => Intrinsic::ValueShow { ty },
            Derived::Equals => Intrinsic::ValueOp {
                op: crag_abi::value_op::EQUALS,
                ty,
            },
            Derived::Compare => Intrinsic::ValueOp {
                op: crag_abi::value_op::COMPARE,
                ty,
            },
            Derived::Hash => Intrinsic::ValueOp {
                op: crag_abi::value_op::HASH,
                ty,
            },
        };
        let result = self.derived_result(op);
        self.assign(result, Rvalue::Intrinsic(intrinsic, values))
    }

    /// A call of a type's own function, its result as the walk gives it:
    /// 1 or 0 for `equals`, and 0, 1 or 2 for `compare`.
    fn own(
        &mut self,
        op: Derived,
        own: &Instance<'db>,
        ty: Ty<'db>,
        values: Vec<Operand<'db>>,
    ) -> Operand<'db> {
        let sig = self.instance_signature(own);
        let Some(result) = sig.result else {
            return self.trap(TrapKind::Error, None);
        };
        let args = values
            .into_iter()
            .zip(&sig.params)
            .map(|(v, p)| self.coerce(v, ty, p.ty))
            .collect();
        let code = InstanceKey::of(self.db, own);
        let value = self.call_code(code, args, result, SITE);
        match op {
            Derived::Show | Derived::Hash => {
                let to = self.derived_result(op);
                self.coerce(Operand::Local(value), result, to)
            }
            Derived::Equals => {
                let int_ty = self.int();
                let out = self.temp(int_ty);
                let (yes, no, join) = (self.new_block(), self.new_block(), self.new_block());
                self.terminate(Terminator::Branch {
                    cond: Operand::Local(value),
                    then: yes,
                    otherwise: no,
                });
                for (block, n) in [(yes, 1), (no, 0)] {
                    self.switch_to(block);
                    self.push(Statement::Assign(out, Rvalue::Use(int(n))));
                    self.terminate(Terminator::Jump(join));
                }
                self.switch_to(join);
                Operand::Local(out)
            }
            Derived::Compare => {
                let cases: Vec<Ty<'db>> = ["Less", "Equal", "Greater"]
                    .iter()
                    .filter_map(|n| prelude_item(self.db, self.program, n))
                    .map(|item| Ty::new(self.db, TyKind::Named(item, Vec::new())))
                    .collect();
                let int_ty = self.int();
                let out = self.temp(int_ty);
                let join = self.new_block();
                self.by_type(value, &cases, |b, k, _| {
                    b.push(Statement::Assign(out, Rvalue::Use(int(k as i128))));
                    b.terminate(Terminator::Jump(join));
                });
                self.switch_to(join);
                Operand::Local(out)
            }
        }
    }

    /// Goes by the first of the types the value in the local has, to code
    /// that `case` builds for it by its position; none trapping.
    pub(super) fn by_type(
        &mut self,
        value: Local,
        cases: &[Ty<'db>],
        mut case: impl FnMut(&mut Self, usize, Ty<'db>),
    ) {
        let blocks: Vec<_> = cases.iter().map(|_| self.new_block()).collect();
        let otherwise = self.new_block();
        self.terminate(Terminator::Switch {
            place: Place::local(value),
            cases: cases.iter().copied().zip(blocks.iter().copied()).collect(),
            otherwise,
        });
        for (k, (&ty, block)) in cases.iter().zip(blocks).enumerate() {
            self.switch_to(block);
            case(self, k, ty);
        }
        self.switch_to(otherwise);
        self.trap(TrapKind::Error, None);
    }

    /// The code for the structure of a type.
    fn structure(&mut self, op: Derived, ty: Ty<'db>, values: Vec<Operand<'db>>) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        match ty.kind(db) {
            TyKind::Named(item, args) => {
                match &type_def(db, program, *item).kind {
                    TypeDefKind::Record { .. } => {
                        let mut cases = record_subtypes(db, program, ty);
                        if cases.is_empty() {
                            return self.fields(op, ty, values);
                        }
                        // The most specific first, so each case is the box's
                        // own type.
                        let parents = |t: Ty<'db>| {
                            std::iter::successors(Some(t), |&t| parent(db, program, t)).count()
                        };
                        let key = |t: &Ty<'db>| match t.kind(db) {
                            TyKind::Named(item, _) => (
                                std::cmp::Reverse(parents(*t)),
                                item.name(db).text(db).clone(),
                                item.module(db).path(db).clone(),
                            ),
                            _ => (std::cmp::Reverse(0), String::new(), String::new()),
                        };
                        cases.sort_by_key(key);
                        cases.push(ty);
                        self.by_case(op, ty, &cases, values, |b, op, case, values| {
                            match b.own_part(case).filter(|_| case != ty) {
                                Some(own) => b.own(op, &own, case, values),
                                None => b.fields(op, case, values),
                            }
                        })
                    }
                    TypeDefKind::Refined(target) | TypeDefKind::Alias(target) => {
                        let target = subst(db, program, *target, *item, args);
                        let values = values
                            .into_iter()
                            .map(|v| self.coerce(v, ty, target))
                            .collect();
                        self.part(op, target, values)
                    }
                    _ => self.walked(op, ty, values),
                }
            }
            TyKind::Record { open: false, .. } => self.fields(op, ty, values),
            TyKind::Union(members) => {
                let members = members.clone();
                self.by_case(op, ty, &members, values, |b, op, member, values| {
                    b.part(op, member, values)
                })
            }
            _ => match ty.as_builtin(db) {
                Some((Builtin::List, &[element])) => self.list(op, ty, element, values),
                Some((Builtin::Map, &[key, value])) => {
                    self.entries(op, ty, key, Some(value), values)
                }
                Some((Builtin::Set, &[key])) => self.entries(op, ty, key, None, values),
                _ => self.walked(op, ty, values),
            },
        }
    }

    /// The code for values of a type that has cases, members of a union or
    /// a record type and its subtypes, by the first each value has: values
    /// of different cases differ, ordered as the cases are.
    fn by_case(
        &mut self,
        op: Derived,
        ty: Ty<'db>,
        cases: &[Ty<'db>],
        values: Vec<Operand<'db>>,
        mut each: impl FnMut(&mut Self, Derived, Ty<'db>, Vec<Operand<'db>>) -> Operand<'db>,
    ) -> Operand<'db> {
        let locals: Vec<Local> = values
            .into_iter()
            .map(|v| self.materialize(v, ty))
            .collect();
        let result = self.derived_result(op);
        let out = self.temp(result);
        let join = self.new_block();
        if let [a, b] = locals[..] {
            let int_ty = self.int();
            let [ia, ib] = [a, b].map(|v| {
                let index = self.temp(int_ty);
                let next = self.new_block();
                self.by_type(v, cases, |m, k, _| {
                    m.push(Statement::Assign(index, Rvalue::Use(int(k as i128))));
                    m.terminate(Terminator::Jump(next));
                });
                self.switch_to(next);
                index
            });
            let (same, differ) = (self.new_block(), self.new_block());
            let alike = self.compare(
                CmpOp::Eq,
                Builtin::Int,
                Operand::Local(ia),
                Operand::Local(ib),
            );
            self.terminate(Terminator::Branch {
                cond: alike,
                then: same,
                otherwise: differ,
            });
            self.switch_to(differ);
            match op {
                Derived::Compare => {
                    let less = self.compare(
                        CmpOp::Lt,
                        Builtin::Int,
                        Operand::Local(ia),
                        Operand::Local(ib),
                    );
                    let (yes, no) = (self.new_block(), self.new_block());
                    self.terminate(Terminator::Branch {
                        cond: less,
                        then: yes,
                        otherwise: no,
                    });
                    for (block, n) in [(yes, 0), (no, 2)] {
                        self.switch_to(block);
                        self.push(Statement::Assign(out, Rvalue::Use(int(n))));
                        self.terminate(Terminator::Jump(join));
                    }
                }
                _ => {
                    self.push(Statement::Assign(out, Rvalue::Use(int(0))));
                    self.terminate(Terminator::Jump(join));
                }
            }
            self.switch_to(same);
        }
        self.by_type(locals[0], cases, |m, k, case| {
            let values = locals
                .iter()
                .map(|&v| m.coerce(Operand::Local(v), ty, case))
                .collect();
            let mut r = m.case_part(op, case, values, &mut each);
            if op == Derived::Hash {
                r = m.mix(int(k as i128), r);
            }
            m.assign_to(out, r, result);
            m.terminate(Terminator::Jump(join));
        });
        self.switch_to(join);
        Operand::Local(out)
    }

    /// One case's part: a tag is all there is to its value.
    fn case_part(
        &mut self,
        op: Derived,
        case: Ty<'db>,
        values: Vec<Operand<'db>>,
        each: &mut impl FnMut(&mut Self, Derived, Ty<'db>, Vec<Operand<'db>>) -> Operand<'db>,
    ) -> Operand<'db> {
        let db = self.db;
        if let TyKind::Named(item, _) = case.kind(db)
            && let TypeDefKind::Tag = type_def(db, self.program, *item).kind
            && self.own_part(case).is_none()
        {
            return match op {
                Derived::Show => Operand::Const(Constant::Str(item.name(db).text(db).clone())),
                Derived::Hash => int(0),
                Derived::Equals | Derived::Compare => int(1),
            };
        }
        each(self, op, case, values)
    }

    /// The hash so far with a part's mixed in, as the machine's integers
    /// wrap.
    fn mix(&mut self, h: Operand<'db>, part: Operand<'db>) -> Operand<'db> {
        let int_ty = self.int();
        let scaled = self.assign(
            int_ty,
            Rvalue::Binary {
                op: BinOp::Mul,
                ty: Builtin::Int,
                a: h,
                b: int(PRIME),
                check: None,
            },
        );
        self.assign(
            int_ty,
            Rvalue::Binary {
                op: BinOp::Add,
                ty: Builtin::Int,
                a: scaled,
                b: part,
                check: None,
            },
        )
    }

    /// The code for a record, field by field in the order of declaration:
    /// `show` writes `Name(field: value, …)`.
    fn fields(&mut self, op: Derived, ty: Ty<'db>, values: Vec<Operand<'db>>) -> Operand<'db> {
        let db = self.db;
        let fields = fields_of(db, self.program, ty).unwrap_or_default();
        let locals: Vec<Local> = values
            .into_iter()
            .map(|v| self.materialize(v, ty))
            .collect();
        let read = |b: &mut Self, name: Name<'db>, field_ty: Ty<'db>| -> Vec<Operand<'db>> {
            locals
                .iter()
                .map(|&local| {
                    let place = Place {
                        local,
                        path: vec![Step::Field(name)],
                    };
                    b.assign(field_ty, Rvalue::Read(place))
                })
                .collect()
        };
        match op {
            Derived::Show => {
                let name = match ty.kind(db) {
                    TyKind::Named(item, _) => item.name(db).text(db).clone(),
                    _ => String::new(),
                };
                let mut parts = vec![text(format!("{name}("))];
                for (i, (name, field_ty)) in fields.into_iter().enumerate() {
                    let sep = if i == 0 { "" } else { ", " };
                    parts.push(text(format!("{sep}{}: ", name.text(db))));
                    let values = read(self, name, field_ty);
                    parts.push(self.part(op, field_ty, values));
                }
                parts.push(text(")".to_string()));
                let str_ty = self.derived_result(op);
                self.assign(str_ty, Rvalue::Concat(parts))
            }
            Derived::Hash => {
                let mut h = int(0);
                for (name, field_ty) in fields {
                    let values = read(self, name, field_ty);
                    let part = self.part(op, field_ty, values);
                    h = self.mix(h, part);
                }
                h
            }
            Derived::Equals | Derived::Compare => {
                let int_ty = self.int();
                let out = self.temp(int_ty);
                let done = self.new_block();
                for (name, field_ty) in fields {
                    let values = read(self, name, field_ty);
                    let r = self.part(op, field_ty, values);
                    self.unless_equal(r, out, done);
                }
                self.push(Statement::Assign(out, Rvalue::Use(int(1))));
                self.terminate(Terminator::Jump(done));
                self.switch_to(done);
                Operand::Local(out)
            }
        }
    }

    /// Goes on when a part's result says equal, 1; else it is the result,
    /// in `out`, and the code goes to `done`.
    fn unless_equal(&mut self, r: Operand<'db>, out: Local, done: crate::ir::BlockId) {
        let equal = self.compare(CmpOp::Eq, Builtin::Int, r.clone(), int(1));
        let (next, differ) = (self.new_block(), self.new_block());
        self.terminate(Terminator::Branch {
            cond: equal,
            then: next,
            otherwise: differ,
        });
        self.switch_to(differ);
        let int_ty = self.int();
        self.assign_to(out, r, int_ty);
        self.terminate(Terminator::Jump(done));
        self.switch_to(next);
    }

    /// A loop over the indices below `len`: `body` builds the code for an
    /// index, in a local.
    pub(super) fn each_index(&mut self, len: Operand<'db>, mut body: impl FnMut(&mut Self, Local)) {
        let int_ty = self.int();
        let i = self.temp(int_ty);
        self.push(Statement::Assign(i, Rvalue::Use(int(0))));
        let (head, inside, exit) = (self.new_block(), self.new_block(), self.new_block());
        self.terminate(Terminator::Jump(head));
        self.switch_to(head);
        let more = self.compare(CmpOp::Lt, Builtin::Int, Operand::Local(i), len);
        self.terminate(Terminator::Branch {
            cond: more,
            then: inside,
            otherwise: exit,
        });
        self.switch_to(inside);
        body(self, i);
        let n = self.assign(
            int_ty,
            Rvalue::Binary {
                op: BinOp::Add,
                ty: Builtin::Int,
                a: Operand::Local(i),
                b: int(1),
                check: None,
            },
        );
        self.assign_to(i, n, int_ty);
        self.push(Statement::Poll);
        self.terminate(Terminator::Jump(head));
        self.switch_to(exit);
    }

    /// An element of a list, borrowed.
    pub(super) fn element(&mut self, list: Local, element: Ty<'db>, i: Local) -> Operand<'db> {
        self.assign(
            element,
            Rvalue::Index {
                list: Place::local(list),
                index: Operand::Local(i),
            },
        )
    }

    /// The code for lists, element by element: `show` writes `[a, b]`, and
    /// a shorter list that agrees so far is less.
    fn list(
        &mut self,
        op: Derived,
        ty: Ty<'db>,
        element: Ty<'db>,
        values: Vec<Operand<'db>>,
    ) -> Operand<'db> {
        let int_ty = self.int();
        let lists: Vec<Local> = values
            .into_iter()
            .map(|v| self.materialize(v, ty))
            .collect();
        let lens: Vec<Operand<'db>> = lists
            .iter()
            .map(|&l| self.assign(int_ty, Rvalue::Len(Place::local(l))))
            .collect();
        match op {
            Derived::Show => {
                let list = lists[0];
                self.joined(lens[0].clone(), "[", "]", |b, i| {
                    let value = b.element(list, element, i);
                    vec![b.part(op, element, vec![value])]
                })
            }
            Derived::Hash => {
                let h = self.temp(int_ty);
                let list = lists[0];
                self.assign_to(h, lens[0].clone(), int_ty);
                self.each_index(lens[0].clone(), |b, i| {
                    let value = b.element(list, element, i);
                    let part = b.part(op, element, vec![value]);
                    let mixed = b.mix(Operand::Local(h), part);
                    b.assign_to(h, mixed, int_ty);
                });
                Operand::Local(h)
            }
            Derived::Equals | Derived::Compare => {
                let out = self.temp(int_ty);
                let done = self.new_block();
                let (la, lb) = (lens[0].clone(), lens[1].clone());
                let shorter = self.compare(CmpOp::Lt, Builtin::Int, la.clone(), lb.clone());
                let longer = self.compare(CmpOp::Lt, Builtin::Int, lb.clone(), la.clone());
                // The elements both lists have.
                let common = self.temp(int_ty);
                self.assign_to(common, la.clone(), int_ty);
                let (other, on) = (self.new_block(), self.new_block());
                let cond = match op {
                    Derived::Equals => self.compare(CmpOp::Ne, Builtin::Int, la, lb.clone()),
                    _ => longer.clone(),
                };
                self.terminate(Terminator::Branch {
                    cond,
                    then: other,
                    otherwise: on,
                });
                self.switch_to(other);
                match op {
                    // Lists of different lengths differ.
                    Derived::Equals => {
                        self.push(Statement::Assign(out, Rvalue::Use(int(0))));
                        self.terminate(Terminator::Jump(done));
                    }
                    _ => {
                        self.assign_to(common, lb, int_ty);
                        self.terminate(Terminator::Jump(on));
                    }
                }
                self.switch_to(on);
                let (a, b) = (lists[0], lists[1]);
                self.each_index(Operand::Local(common), |m, i| {
                    let values = vec![m.element(a, element, i), m.element(b, element, i)];
                    let r = m.part(op, element, values);
                    m.unless_equal(r, out, done);
                });
                // The elements agree: the shorter list is less.
                if op == Derived::Compare {
                    for (cond, k) in [(shorter, 0), (longer, 2)] {
                        let (yes, no) = (self.new_block(), self.new_block());
                        self.terminate(Terminator::Branch {
                            cond,
                            then: yes,
                            otherwise: no,
                        });
                        self.switch_to(yes);
                        self.push(Statement::Assign(out, Rvalue::Use(int(k))));
                        self.terminate(Terminator::Jump(done));
                        self.switch_to(no);
                    }
                }
                self.push(Statement::Assign(out, Rvalue::Use(int(1))));
                self.terminate(Terminator::Jump(done));
                self.switch_to(done);
                Operand::Local(out)
            }
        }
    }

    /// Text of parts for each index below `len`, between `open` and
    /// `close` and separated by `, `.
    fn joined(
        &mut self,
        len: Operand<'db>,
        open: &str,
        close: &str,
        mut parts: impl FnMut(&mut Self, Local) -> Vec<Operand<'db>>,
    ) -> Operand<'db> {
        let str_ty = Ty::builtin(self.db, Builtin::Str);
        let out = self.temp(str_ty);
        let sep = self.temp(str_ty);
        self.push(Statement::Assign(out, Rvalue::Use(text(open.to_string()))));
        self.push(Statement::Assign(sep, Rvalue::Use(text(String::new()))));
        self.each_index(len, |b, i| {
            let mut all = vec![Operand::Local(out), Operand::Local(sep)];
            all.extend(parts(b, i));
            let joined = b.assign(str_ty, Rvalue::Concat(all));
            b.assign_to(out, joined, str_ty);
            b.push(Statement::Assign(sep, Rvalue::Use(text(", ".to_string()))));
        });
        let all = vec![Operand::Local(out), text(close.to_string())];
        self.assign(str_ty, Rvalue::Concat(all))
    }

    /// The code for maps and sets: `show` writes their entries, `[k: v]`
    /// or `[k]`, and `[:]` or `[]` when there are none. Their keys are
    /// found by their structure, so only a map's values meet `equals` and
    /// `hash`; entries in any order hash alike.
    fn entries(
        &mut self,
        op: Derived,
        ty: Ty<'db>,
        key: Ty<'db>,
        value: Option<Ty<'db>>,
        values: Vec<Operand<'db>>,
    ) -> Operand<'db> {
        let db = self.db;
        let int_ty = self.int();
        let maps: Vec<Local> = values
            .into_iter()
            .map(|v| self.materialize(v, ty))
            .collect();
        let list_of = |t: Ty<'db>| Ty::new(db, TyKind::Builtin(Builtin::List, vec![t]));
        let keys = self.assign(
            list_of(key),
            Rvalue::Intrinsic(Intrinsic::MapKeys, vec![Operand::Local(maps[0])]),
        );
        let keys = self.materialize(keys, list_of(key));
        let listed = value.map(|v| {
            let vs = self.assign(
                list_of(v),
                Rvalue::Intrinsic(Intrinsic::MapValues, vec![Operand::Local(maps[0])]),
            );
            (self.materialize(vs, list_of(v)), v)
        });
        let len = self.assign(int_ty, Rvalue::Len(Place::local(keys)));
        match (op, listed) {
            (Derived::Show, _) => {
                let str_ty = self.derived_result(op);
                let out = self.temp(str_ty);
                let empty = self.compare(CmpOp::Eq, Builtin::Int, len.clone(), int(0));
                let (none, some, join) = (self.new_block(), self.new_block(), self.new_block());
                self.terminate(Terminator::Branch {
                    cond: empty,
                    then: none,
                    otherwise: some,
                });
                self.switch_to(none);
                let nothing = if value.is_some() { "[:]" } else { "[]" };
                self.push(Statement::Assign(
                    out,
                    Rvalue::Use(text(nothing.to_string())),
                ));
                self.terminate(Terminator::Jump(join));
                self.switch_to(some);
                let shown = self.joined(len, "[", "]", |b, i| {
                    let k = b.element(keys, key, i);
                    let mut parts = vec![b.part(op, key, vec![k])];
                    if let Some((vs, v)) = listed {
                        let x = b.element(vs, v, i);
                        parts.push(text(": ".to_string()));
                        parts.push(b.part(op, v, vec![x]));
                    }
                    parts
                });
                self.assign_to(out, shown, str_ty);
                self.terminate(Terminator::Jump(join));
                self.switch_to(join);
                Operand::Local(out)
            }
            (Derived::Hash, Some((vs, v))) => {
                let sum = self.temp(int_ty);
                self.push(Statement::Assign(sum, Rvalue::Use(int(0))));
                self.each_index(len, |b, i| {
                    let k = b.element(keys, key, i);
                    let kh = b.walked(Derived::Hash, key, vec![k]);
                    let x = b.element(vs, v, i);
                    let vh = b.part(Derived::Hash, v, vec![x]);
                    let entry = b.mix(kh, vh);
                    let added = b.assign(
                        int_ty,
                        Rvalue::Binary {
                            op: BinOp::Add,
                            ty: Builtin::Int,
                            a: Operand::Local(sum),
                            b: entry,
                            check: None,
                        },
                    );
                    b.assign_to(sum, added, int_ty);
                });
                Operand::Local(sum)
            }
            (Derived::Equals, Some((vs, v))) => {
                let out = self.temp(int_ty);
                let done = self.new_block();
                let other = self.assign(
                    int_ty,
                    Rvalue::Intrinsic(Intrinsic::CollCount, vec![Operand::Local(maps[1])]),
                );
                let same = self.compare(CmpOp::Eq, Builtin::Int, len.clone(), other);
                let (on, differ) = (self.new_block(), self.new_block());
                self.terminate(Terminator::Branch {
                    cond: same,
                    then: on,
                    otherwise: differ,
                });
                self.switch_to(differ);
                self.push(Statement::Assign(out, Rvalue::Use(int(0))));
                self.terminate(Terminator::Jump(done));
                self.switch_to(on);
                let other = maps[1];
                self.each_index(len, |b, i| {
                    let k = b.element(keys, key, i);
                    // A key the other map lacks makes them differ.
                    let has = b.assign(
                        int_ty,
                        Rvalue::Intrinsic(
                            Intrinsic::SetContains,
                            vec![Operand::Local(other), k.clone()],
                        ),
                    );
                    b.unless_equal(has, out, done);
                    let theirs = b.assign(
                        v,
                        Rvalue::MapGet {
                            map: Place::local(other),
                            key: k,
                            boxed: false,
                        },
                    );
                    let mine = b.element(vs, v, i);
                    let r = b.part(Derived::Equals, v, vec![mine, theirs]);
                    b.unless_equal(r, out, done);
                });
                self.push(Statement::Assign(out, Rvalue::Use(int(1))));
                self.terminate(Terminator::Jump(done));
                self.switch_to(done);
                Operand::Local(out)
            }
            _ => {
                let values = maps.into_iter().map(Operand::Local).collect();
                self.walked(op, ty, values)
            }
        }
    }
}

/// A string constant.
fn text<'db>(s: String) -> Operand<'db> {
    Operand::Const(Constant::Str(s))
}
