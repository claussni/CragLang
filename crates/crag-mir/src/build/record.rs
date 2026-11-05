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

//! Constructions: a record with its fields and their defaults, a record
//! transformed field by field, and a value rebuilt with a field changed.

use super::*;

impl<'a, 'db> MirBuilder<'a, 'db> {
    pub(super) fn construct(
        &mut self,
        expr: ExprId,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Operand<'db> {
        let db = self.db;
        if let TyKind::Named(item, _) = ty.kind(db)
            && let TypeDefKind::Tag = type_def(db, self.program, *item).kind
        {
            return Operand::Const(Constant::Tag(ty));
        }
        // `List[T]()` and the others build an empty collection (§6.5).
        match ty.as_builtin(db) {
            Some((Builtin::List | Builtin::Set, _)) => {
                return self.assign(ty, Rvalue::List(Vec::new()));
            }
            Some((Builtin::Map, _)) => return self.assign(ty, Rvalue::Map(Vec::new())),
            _ => {}
        }
        if fields_of(db, self.program, ty).is_none() {
            return self.unsupported(expr, "constructions of collections");
        }
        self.record(expr, ty, positional, fields.unwrap_or(&[]))
    }

    pub(super) fn record(
        &mut self,
        expr: ExprId,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> Operand<'db> {
        if ty == Ty::unit(self.db) {
            return self.unit();
        }
        self.record_value(expr, ty, positional, fields)
    }

    /// The fields of a record in the order of `fields_of`, each written,
    /// or taken from a spread.
    fn record_slots(
        &self,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> Option<Vec<Slot<'db>>> {
        let db = self.db;
        let all = fields_of(db, self.program, ty)?;
        let declared: Vec<_> = match declared_fields(db, self.program, ty) {
            Some(declared) => declared.into_iter().map(|(n, ..)| n).collect(),
            None => all.iter().map(|(n, _)| *n).collect(),
        };
        let mut slots = Vec::new();
        for &(name, field_ty) in &all {
            let given = positional
                .iter()
                .zip(&declared)
                .find(|(_, n)| **n == name)
                .map(|(e, _)| *e)
                .or_else(|| {
                    fields.iter().find_map(|f| match f {
                        FieldArg::Field { path, value } if path == &[name] => Some(*value),
                        _ => None,
                    })
                });
            let spread = fields.iter().rev().find_map(|f| match f {
                FieldArg::Spread(e) => fields_of(db, self.program, self.ty(*e))?
                    .iter()
                    .any(|(n, _)| *n == name)
                    .then_some(*e),
                _ => None,
            });
            let paths = fields
                .iter()
                .filter_map(|f| match f {
                    FieldArg::Field { path, value } if path.len() > 1 && path[0] == name => {
                        Some((path[1..].to_vec(), *value))
                    }
                    _ => None,
                })
                .collect();
            let default = self.field_default(ty, name, field_ty);
            slots.push(Slot {
                name,
                ty: field_ty,
                given,
                paths,
                spread,
                default,
            });
        }
        Some(slots)
    }

    pub(super) fn record_fits(
        &self,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> bool {
        self.record_slots(ty, positional, fields)
            .is_some_and(|slots| {
                slots
                    .iter()
                    .all(|s| s.given.is_some() || s.spread.is_some() || s.default.is_some())
            })
    }

    /// The default of a field of a named record type, as the type that
    /// declares the field last gives it.
    fn field_default(
        &self,
        ty: Ty<'db>,
        name: crag_hir::Name<'db>,
        field_ty: Ty<'db>,
    ) -> Option<FieldDefault<'db>> {
        let db = self.db;
        let mut current = Some(ty);
        while let Some(t) = current {
            let TyKind::Named(item, args) = t.kind(db) else {
                return None;
            };
            let body = hir_body(db, self.program, Owner::Item(*item));
            if let Some(field) = body
                .type_decl
                .as_ref()?
                .fields
                .iter()
                .find(|f| f.name == name)
            {
                let default = field.default?;
                if let Expr::Literal(literal) = body.expr(default) {
                    let constant = self.literal(literal, field_ty, body.is_negative(default));
                    return Some(FieldDefault::Constant(constant));
                }
                let code = InstanceKey::new(
                    db,
                    Owner::Item(*item),
                    args.clone(),
                    Vec::new(),
                    Vec::new(),
                    Entry::Default(default),
                );
                return Some(FieldDefault::Code(code));
            }
            current = crag_types::parent(db, self.program, t);
        }
        None
    }

    /// Builds a record: the written values in their order, then the
    /// fields spreads give, then the defaults of the rest.
    pub(super) fn record_value(
        &mut self,
        site: ExprId,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> Operand<'db> {
        let Some(slots) = self.record_slots(ty, positional, fields) else {
            return self.trap(TrapKind::Error, Some(site));
        };
        let written = positional
            .iter()
            .copied()
            .chain(fields.iter().map(|f| match f {
                FieldArg::Field { value, .. } | FieldArg::Spread(value) => *value,
            }));
        let mut values: HashMap<ExprId, Operand<'db>> = HashMap::new();
        for e in written.collect::<Vec<_>>() {
            let op = self.expr(e);
            values.insert(e, op);
        }
        let mut spreads: HashMap<ExprId, Local> = HashMap::new();
        let mut out = Vec::new();
        for Slot {
            name,
            ty: field_ty,
            given,
            paths,
            spread,
            default,
        } in slots
        {
            // The field's current value, from the last spread that has it.
            let mut current = |this: &mut Self| -> Option<(Operand<'db>, Ty<'db>)> {
                let s = spread?;
                let local = match spreads.get(&s) {
                    Some(&l) => l,
                    None => {
                        let l = this.materialize(values[&s].clone(), this.ty(s));
                        spreads.insert(s, l);
                        l
                    }
                };
                let from = fields_of(this.db, this.program, this.ty(s))
                    .and_then(|fs| fs.into_iter().find(|(n, _)| *n == name))
                    .map_or(field_ty, |(_, t)| t);
                let place = Place {
                    local,
                    path: vec![Step::Field(name)],
                };
                Some((this.assign(from, Rvalue::Read(place)), from))
            };
            let op = match (given, spread) {
                (Some(e), _) if self.transforms(e, field_ty) => {
                    let Some((old, from)) = current(self) else {
                        return self.trap(TrapKind::Error, Some(site));
                    };
                    let f = values[&e].clone();
                    self.transform(f, self.ty(e), old, from, field_ty, e)
                }
                (Some(e), _) => {
                    let op = values[&e].clone();
                    self.coerce(op, self.ty(e), field_ty)
                }
                (None, Some(_)) if !paths.is_empty() => {
                    let Some((old, from)) = current(self) else {
                        return self.trap(TrapKind::Error, Some(site));
                    };
                    let old = self.coerce(old, from, field_ty);
                    self.rebuild(field_ty, old, &paths, &values, site)
                }
                (None, Some(_)) => {
                    let Some((op, from)) = current(self) else {
                        return self.trap(TrapKind::Error, Some(site));
                    };
                    self.coerce(op, from, field_ty)
                }
                (None, None) => match default {
                    Some(FieldDefault::Constant(constant)) => Operand::Const(constant),
                    // The type that declares the field last gives it the
                    // type it has here.
                    Some(FieldDefault::Code(code)) => {
                        Operand::Local(self.call_code(code, Vec::new(), field_ty, site))
                    }
                    None => return self.trap(TrapKind::Error, Some(site)),
                },
            };
            out.push((name, op));
        }
        let dispose = self.dispose_code(ty);
        let built = self.assign(
            ty,
            Rvalue::Record {
                ty,
                fields: out,
                dispose,
                reuse: None,
            },
        );
        self.check_conditions(built, ty, site)
    }

    /// Whether the value `e` given for a field of type `field_ty`
    /// transforms its current value: a function, where the field holds
    /// none (§6.7).
    fn transforms(&self, e: ExprId, field_ty: Ty<'db>) -> bool {
        let db = self.db;
        self.ty(e).is_fn(db) && !field_ty.is_fn(db)
    }

    /// Calls the transform `f` on the current value `old` of a field.
    fn transform(
        &mut self,
        f: Operand<'db>,
        f_ty: Ty<'db>,
        old: Operand<'db>,
        from: Ty<'db>,
        field_ty: Ty<'db>,
        site: ExprId,
    ) -> Operand<'db> {
        let Some((params, result, _)) = f_ty.as_fn(self.db) else {
            return self.trap(TrapKind::Error, Some(site));
        };
        let param = params[0];
        let callee = self.typed(f, f_ty);
        let arg = self.coerce(old, from, param);
        let dst = self.temp(result);
        let target = self.new_block();
        self.terminate(Terminator::CallValue {
            callee,
            args: vec![arg],
            dst,
            target,
            site,
            unwind: None,
            catch: None,
        });
        self.switch_to(target);
        self.coerce(Operand::Local(dst), result, field_ty)
    }

    /// The record `old` of type `ty` with the changes the paths below it
    /// make, each path's value already evaluated (§6.7).
    fn rebuild(
        &mut self,
        ty: Ty<'db>,
        old: Operand<'db>,
        paths: &[(Vec<crag_hir::Name<'db>>, ExprId)],
        values: &HashMap<ExprId, Operand<'db>>,
        site: ExprId,
    ) -> Operand<'db> {
        let Some(fields) = fields_of(self.db, self.program, ty) else {
            return self.trap(TrapKind::Error, Some(site));
        };
        let local = self.materialize(old, ty);
        let mut out = Vec::new();
        for (name, field_ty) in fields {
            let place = Place {
                local,
                path: vec![Step::Field(name)],
            };
            let whole = paths
                .iter()
                .find(|(p, _)| p.len() == 1 && p[0] == name)
                .map(|(_, e)| *e);
            let below: Vec<_> = paths
                .iter()
                .filter(|(p, _)| p.len() > 1 && p[0] == name)
                .map(|(p, e)| (p[1..].to_vec(), *e))
                .collect();
            let op = match whole {
                Some(e) if self.transforms(e, field_ty) => {
                    let current = self.assign(field_ty, Rvalue::Read(place));
                    let f = values[&e].clone();
                    self.transform(f, self.ty(e), current, field_ty, field_ty, e)
                }
                Some(e) => {
                    let op = values[&e].clone();
                    self.coerce(op, self.ty(e), field_ty)
                }
                None if !below.is_empty() => {
                    let current = self.assign(field_ty, Rvalue::Read(place));
                    self.rebuild(field_ty, current, &below, values, site)
                }
                None => self.assign(field_ty, Rvalue::Read(place)),
            };
            out.push((name, op));
        }
        let dispose = self.dispose_code(ty);
        let built = self.assign(
            ty,
            Rvalue::Record {
                ty,
                fields: out,
                dispose,
                reuse: None,
            },
        );
        self.check_conditions(built, ty, site)
    }

    // Statements.
}
