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

//! Conversions that rebuild a value (Specification §3.13.3): an immutable
//! generic type fits one whose arguments its own fit, `List[Int]` fits
//! `List[Int | Str]`, but the parts of the two are laid out differently, as
//! a member is from its union. Such a value is built anew with each part
//! converted: a list element by element, a set by its members, a map by its
//! entries, a record field by field, and a union by its member. A record
//! that is held as its parent, or one whose fields are the same, keeps its
//! box.

use crag_types::{
    Builtin, Step, Ty, TyKind, TypeDefKind, fields_of, is_subtype, type_def, unrefined,
};

use super::MirBuilder;
use crate::ir::{Intrinsic, Local, Operand, Place, Rvalue, Statement, Terminator, TrapKind};

impl<'a, 'db> MirBuilder<'a, 'db> {
    /// Whether a value of `from` is one of `to` as it is laid out.
    fn same_layout(&self, from: Ty<'db>, to: Ty<'db>) -> bool {
        let (db, program) = (self.db, self.program);
        if from == to || from.is_error(db) || to.is_error(db) || from.is_never(db) {
            return true;
        }
        let all = |a: &[Ty<'db>], b: &[Ty<'db>]| {
            a.len() == b.len() && a.iter().zip(b).all(|(&x, &y)| self.same_layout(x, y))
        };
        match (from.kind(db), to.kind(db)) {
            (TyKind::Builtin(a, xs), TyKind::Builtin(b, ys)) if a == b => all(xs, ys),
            // A tag is its type alone, whatever its level.
            (TyKind::Named(a, xs), TyKind::Named(b, ys)) if a == b => {
                matches!(type_def(db, program, *a).kind, TypeDefKind::Tag) || all(xs, ys)
            }
            // A subtype's box starts as its parent's.
            (TyKind::Named(a, xs), TyKind::Named(_, ys)) => {
                xs.is_empty()
                    && ys.is_empty()
                    && matches!(type_def(db, program, *a).kind, TypeDefKind::Record { .. })
            }
            (TyKind::Record { fields: a, .. }, TyKind::Record { fields: b, .. }) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|((n, x), (m, y))| n == m && self.same_layout(*x, *y))
            }
            // A union's members are known by their types wherever they are.
            (TyKind::Union(xs), TyKind::Union(ys)) => xs.iter().all(|x| ys.contains(x)),
            _ => unrefined(db, program, from) == unrefined(db, program, to),
        }
    }

    /// The member of `to` a value of `from` goes to, or `to` itself when it
    /// is no union; none when the value cannot be one of `to`, as a member
    /// a test has ruled out.
    fn target(&self, from: Ty<'db>, to: Ty<'db>) -> Option<Ty<'db>> {
        match to.kind(self.db) {
            // A member of the value's own type first, as of its own level.
            TyKind::Union(members) if members.contains(&from) => Some(from),
            TyKind::Union(_) => to
                .members(self.db)
                .into_iter()
                .find(|&m| is_subtype(self.db, self.program, from, m)),
            _ => is_subtype(self.db, self.program, from, to).then_some(to),
        }
    }

    /// Whether the backend converts a value of `from` to one of `to` as it
    /// is: it puts members into unions and takes them out, so each member
    /// must be laid out as the one it goes to.
    fn kept(&self, from: Ty<'db>, to: Ty<'db>) -> bool {
        self.same_layout(from, to)
            || from
                .members(self.db)
                .into_iter()
                .all(|m| self.target(m, to).is_none_or(|t| self.same_layout(m, t)))
    }

    /// The value as one of `to`, built anew when its parts are laid out
    /// differently; none when it is kept as it is.
    pub(super) fn rebuilt(
        &mut self,
        op: Operand<'db>,
        from: Ty<'db>,
        to: Ty<'db>,
    ) -> Option<Operand<'db>> {
        let db = self.db;
        if matches!(from.kind(db), TyKind::Fn { .. }) || self.kept(from, to) {
            return None;
        }
        let value = self.materialize(op, from);
        let members = from.members(db);
        if members.len() > 1 {
            // Each member on its own.
            let out = self.temp(to);
            let join = self.new_block();
            self.by_type(value, &members, |b, _, member| {
                let part = b.coerce(Operand::Local(value), from, member);
                let part = b.coerce(part, member, to);
                b.assign_to(out, part, to);
                b.terminate(Terminator::Jump(join));
            });
            self.switch_to(join);
            return Some(Operand::Local(out));
        }
        // Into the member of a union it goes to, then into the union.
        if let Some(target) = self.target(from, to).filter(|&t| t != to) {
            let part = self.coerce(Operand::Local(value), from, target);
            return Some(self.coerce(part, target, to));
        }
        Some(match (from.as_builtin(db), to.as_builtin(db)) {
            (Some((Builtin::List, &[a])), Some((Builtin::List, &[b]))) => {
                self.rebuilt_list(value, a, to, b)
            }
            (Some((Builtin::Set, &[a])), Some((Builtin::Set, &[b]))) => {
                self.rebuilt_set(value, a, to, b)
            }
            (Some((Builtin::Map, &[k, v])), Some((Builtin::Map, &[l, w]))) => {
                self.rebuilt_map(value, (k, v), to, (l, w))
            }
            _ => self.rebuilt_record(value, from, to),
        })
    }

    /// A record with each field converted.
    fn rebuilt_record(&mut self, record: Local, from: Ty<'db>, to: Ty<'db>) -> Operand<'db> {
        let db = self.db;
        let (Some(have), Some(want)) = (
            fields_of(db, self.program, from),
            fields_of(db, self.program, to),
        ) else {
            return self.trap(TrapKind::Error, None);
        };
        let mut values = Vec::new();
        for (name, ty) in want {
            let Some(&(_, of)) = have.iter().find(|(n, _)| *n == name) else {
                return self.trap(TrapKind::Error, None);
            };
            let place = Place {
                local: record,
                path: vec![Step::Field(name)],
            };
            let part = self.assign(of, Rvalue::Read(place));
            values.push((name, self.coerce(part, of, ty)));
        }
        let dispose = self.dispose_code(to);
        self.assign(
            to,
            Rvalue::Record {
                ty: to,
                fields: values,
                dispose,
            },
        )
    }

    /// A list with each element converted.
    fn rebuilt_list(
        &mut self,
        list: Local,
        from: Ty<'db>,
        to: Ty<'db>,
        element: Ty<'db>,
    ) -> Operand<'db> {
        let int_ty = self.int();
        let len = self.assign(int_ty, Rvalue::Len(Place::local(list)));
        let out = self.temp(to);
        self.push(Statement::Assign(out, Rvalue::List(Vec::new())));
        self.each_index(len, |b, i| {
            let item = b.element(list, from, i);
            let item = b.coerce(item, from, element);
            let grown = b.assign(
                to,
                Rvalue::Intrinsic(Intrinsic::ListAppend, vec![Operand::Local(out), item]),
            );
            b.assign_to(out, grown, to);
        });
        Operand::Local(out)
    }

    /// A set with each member converted.
    fn rebuilt_set(&mut self, set: Local, a: Ty<'db>, to: Ty<'db>, b: Ty<'db>) -> Operand<'db> {
        let db = self.db;
        let list_of = |t: Ty<'db>| Ty::new(db, TyKind::Builtin(Builtin::List, vec![t]));
        let keys = self.assign(
            list_of(a),
            Rvalue::Intrinsic(Intrinsic::MapKeys, vec![Operand::Local(set)]),
        );
        let keys = self.materialize(keys, list_of(a));
        let int_ty = self.int();
        let len = self.assign(int_ty, Rvalue::Len(Place::local(keys)));
        let out = self.temp(to);
        self.push(Statement::Assign(out, Rvalue::List(Vec::new())));
        self.each_index(len, |m, i| {
            let key = m.element(keys, a, i);
            let key = m.coerce(key, a, b);
            let grown = m.assign(
                to,
                Rvalue::Intrinsic(Intrinsic::SetInsert, vec![Operand::Local(out), key]),
            );
            m.assign_to(out, grown, to);
        });
        Operand::Local(out)
    }

    /// A map with each entry converted.
    fn rebuilt_map(
        &mut self,
        map: Local,
        (k, v): (Ty<'db>, Ty<'db>),
        to: Ty<'db>,
        (l, w): (Ty<'db>, Ty<'db>),
    ) -> Operand<'db> {
        let db = self.db;
        let list_of = |t: Ty<'db>| Ty::new(db, TyKind::Builtin(Builtin::List, vec![t]));
        let keys = self.assign(
            list_of(k),
            Rvalue::Intrinsic(Intrinsic::MapKeys, vec![Operand::Local(map)]),
        );
        let keys = self.materialize(keys, list_of(k));
        let values = self.assign(
            list_of(v),
            Rvalue::Intrinsic(Intrinsic::MapValues, vec![Operand::Local(map)]),
        );
        let values = self.materialize(values, list_of(v));
        let int_ty = self.int();
        let len = self.assign(int_ty, Rvalue::Len(Place::local(keys)));
        let out = self.temp(to);
        self.push(Statement::Assign(out, Rvalue::Map(Vec::new())));
        self.each_index(len, |m, i| {
            let key = m.element(keys, k, i);
            let key = m.coerce(key, k, l);
            let value = m.element(values, v, i);
            let value = m.coerce(value, v, w);
            let grown = m.assign(
                to,
                Rvalue::Intrinsic(Intrinsic::MapInsert, vec![Operand::Local(out), key, value]),
            );
            m.assign_to(out, grown, to);
        });
        Operand::Local(out)
    }
}
