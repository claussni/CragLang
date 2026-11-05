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

//! Constructions and what is read out of them: records, grids,
//! collections and maps as written, fields, indexing, optional access,
//! method calls and updates.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    /// A call of a type: the construction of a record, or of an empty
    /// collection with its type arguments (§6.5, §6.7).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn construct(
        &mut self,
        id: ExprId,
        callee: ExprId,
        name: Name<'db>,
        item: ItemId<'db>,
        targs: Option<Vec<Ty<'db>>>,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let program = self.program;
        let header = type_header(db, program, item);
        let arity = header.params.len();
        let ty = match header.kind {
            HeaderKind::Builtin(builtin @ (Builtin::List | Builtin::Map | Builtin::Set))
                if args.is_empty() && fields.is_none() =>
            {
                let targs = targs.or_else(|| {
                    let (b, a) = expected.and_then(|e| self.member_builtin(e, &[builtin]))?;
                    (b == builtin).then_some(a)
                });
                match targs {
                    Some(targs) if targs.len() == arity => self.builtin_of(builtin, targs),
                    _ => {
                        self.error(Site::Expr(id), ErrorKind::CannotInfer);
                        self.err_ty()
                    }
                }
            }
            HeaderKind::Nominal | HeaderKind::Alias => {
                let identity = type_identity(db, program, item);
                let target = match header.kind {
                    HeaderKind::Alias => match (alias_target(db, program, item), &targs) {
                        (Some(t), Some(targs)) => {
                            Some(crate::relate::subst(db, program, t, item, targs))
                        }
                        (Some(t), None) if arity == 0 => Some(t),
                        _ => None,
                    },
                    _ => {
                        let targs = targs.clone().or_else(|| {
                            expected?
                                .members(db)
                                .into_iter()
                                .find_map(|m| match m.kind(db) {
                                    TyKind::Named(i, a) if *i == identity => Some(a.clone()),
                                    _ => None,
                                })
                        });
                        match targs {
                            Some(targs) if targs.len() == arity => {
                                Some(Ty::new(db, TyKind::Named(identity, targs)))
                            }
                            None if arity == 0 => {
                                Some(Ty::new(db, TyKind::Named(identity, Vec::new())))
                            }
                            None if fields.is_some() => {
                                let fields = fields.unwrap_or_default();
                                let targs = self.construction_args(id, item, identity, fields);
                                Some(Ty::new(db, TyKind::Named(identity, targs)))
                            }
                            _ => None,
                        }
                    }
                };
                let Some(ty) = target else {
                    let kind = ErrorKind::Unsupported("inferred type arguments of constructions");
                    self.error(Site::Expr(id), kind);
                    self.synth_args(args, fields);
                    return self.err_ty();
                };
                if let ([arg], None) = (args, fields) {
                    return self.conversion(id, callee, ty, *arg, expected);
                }
                if declared_fields(db, program, ty).is_none() {
                    self.error(Site::Expr(id), ErrorKind::NotAValue { name });
                    self.synth_args(args, fields);
                    return self.err_ty();
                }
                if !args.is_empty() {
                    let kind = ErrorKind::ArgCount {
                        expected: 0,
                        found: args.len(),
                    };
                    self.error(Site::Expr(id), kind);
                    self.synth_args(args, None);
                }
                self.build_record(id, ty, fields.unwrap_or_default());
                self.known_conditions(id, ty, fields.unwrap_or_default());
                ty
            }
            HeaderKind::Refined if matches!((args, fields), ([_], None)) => {
                return self.refine_alias(id, callee, item, targs, args[0]);
            }
            HeaderKind::Builtin(builtin) if matches!((args, fields), ([_], None)) => {
                let target = match targs {
                    Some(targs) => self.builtin_of(builtin, targs),
                    None if arity == 0 => self.builtin_of(builtin, Vec::new()),
                    None => {
                        self.error(Site::Expr(id), ErrorKind::CannotInfer);
                        self.synth_args(args, fields);
                        return self.err_ty();
                    }
                };
                return self.conversion(id, callee, target, args[0], expected);
            }
            _ => {
                self.error(Site::Expr(id), ErrorKind::NotAValue { name });
                self.synth_args(args, fields);
                return self.err_ty();
            }
        };
        // The type arguments must fit the type's bounds (§4.7).
        if let TyKind::Named(identity, targs) = ty.kind(db)
            && !targs.is_empty()
            && !targs.iter().any(|t| t.is_error(db))
            && let Err(fit) = instantiate(db, self.program, *identity, targs, self.call_site())
        {
            self.error(Site::Expr(id), ErrorKind::Unfit(fit));
        }
        self.exprs[callee.index()] = Some(ty);
        self.callees.push((id, Callee::Construct(ty)));
        ty
    }

    /// An interpolated value is written by the `show` its type has where
    /// the string is, unless the runtime's walk writes it; a string or a
    /// code point is written as it is (§19.11).
    pub(super) fn interpolated(&mut self, id: ExprId, ty: Ty<'db>) {
        let (db, program) = (self.db, self.program);
        // A union's members that are text are written as they are too, and
        // the rest by their `show`.
        let rest: Vec<Ty<'db>> = ty
            .members(db)
            .into_iter()
            .filter(|&m| !is_text(db, program, m))
            .collect();
        if rest.is_empty() {
            return;
        }
        let shown = self.join_all(rest);
        if let Some(filling) = crate::generic::written_show(db, program, shown, self.call_site()) {
            self.shows.push((id, filling));
        }
    }

    /// A construction whose fields are literals that fails a condition of
    /// its type or of a parent's: a failure the compiler can see is a
    /// compile error (§3.10.1). A condition it cannot decide is checked
    /// when the value is built.
    fn known_conditions(&mut self, id: ExprId, ty: Ty<'db>, fields: &[FieldArg<'db>]) {
        let (db, program, body) = (self.db, self.program, self.body);
        if self.in_type {
            return;
        }
        let known: Vec<(String, crate::refine::Known)> = fields
            .iter()
            .filter_map(|field| {
                let FieldArg::Field { path, value } = field else {
                    return None;
                };
                let [name] = path.as_slice() else {
                    return None;
                };
                let literal = match body.expr(*value) {
                    Expr::Literal(literal) => literal.clone(),
                    Expr::Str(parts) => match parts.as_slice() {
                        [crag_hir::StrPart::Text(text)] => Literal::Str(text.clone()),
                        [] => Literal::Str(String::new()),
                        _ => return None,
                    },
                    _ => return None,
                };
                let k = crate::refine::known(&literal, body.is_negative(*value))?;
                Some((name.text(db).to_string(), k))
            })
            .collect();
        if known.is_empty() {
            return;
        }
        let value = crate::refine::Known::Record(known);
        let mut checked = Some(ty);
        while let Some(t) = checked {
            checked = crate::relate::parent(db, program, t);
            let TyKind::Named(item, _) = t.kind(db) else {
                continue;
            };
            if let crate::refine::Verdict::Fails(condition) =
                crate::refine::verdict(db, program, *item, &value)
            {
                let kind = ErrorKind::ConditionNotMet {
                    alias: t,
                    condition,
                };
                self.error(Site::Expr(id), kind);
                return;
            }
        }
    }

    /// `A(x)` for a conditioned alias `A`: `x` as the alias's target,
    /// checked when it runs, giving an `A` or `Invalid` (§3.10.1).
    fn refine_alias(
        &mut self,
        id: ExprId,
        callee: ExprId,
        item: ItemId<'db>,
        targs: Option<Vec<Ty<'db>>>,
        arg: ExprId,
    ) -> Ty<'db> {
        let db = self.db;
        let program = self.program;
        let identity = type_identity(db, program, item);
        let arity = type_header(db, program, item).params.len();
        let generic_target = alias_target(db, program, item).unwrap_or_else(|| Ty::error(db));
        let args = match targs {
            Some(targs) => targs,
            None if arity == 0 => Vec::new(),
            None => {
                let found = self.synth(arg);
                self.typed.insert(arg, found);
                let mut args = vec![None; arity];
                bind(db, program, item, generic_target, found, &mut args);
                args.into_iter()
                    .map(|a| a.unwrap_or_else(|| Ty::error(db)))
                    .collect()
            }
        };
        let ty = Ty::new(db, TyKind::Named(identity, args.clone()));
        let target = crate::relate::subst(db, program, generic_target, item, &args);
        self.check(arg, target);
        self.exprs[callee.index()] = Some(ty);
        self.callees.push((id, Callee::Refine(ty)));
        let invalid = prelude_type(db, program, "Invalid");
        self.join(ty, invalid)
    }

    /// `T(x)`: a call of the `convert` that takes `x` and whose success
    /// type is `T`, as `T.convert(x)` would make (§5.6).
    fn conversion(
        &mut self,
        id: ExprId,
        callee: ExprId,
        target: Ty<'db>,
        arg: ExprId,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let name = Name::new(db, "convert".to_string());
        let functions = match module_scope(db, self.program, self.module).resolve(name) {
            Some(Resolution::Value { functions, .. }) => functions.clone(),
            _ => Vec::new(),
        };
        self.exprs[callee.index()] = Some(target);
        if functions.is_empty() {
            let from = self.synth(arg);
            self.error(Site::Expr(id), ErrorKind::NoConversion { from, to: target });
            return self.err_ty();
        }
        self.resolve(
            id,
            None,
            name,
            &functions,
            None,
            None,
            &[arg],
            None,
            expected,
            Some(target),
        )
    }

    /// The type arguments of a construction of the generic type
    /// `identity`, from the values its fields are given; closures are
    /// left to the record's check, against the types found. An argument
    /// nothing fixes is an error.
    fn construction_args(
        &mut self,
        id: ExprId,
        item: ItemId<'db>,
        identity: ItemId<'db>,
        fields: &[FieldArg<'db>],
    ) -> Vec<Ty<'db>> {
        let db = self.db;
        let program = self.program;
        let names = type_header(db, program, item).params.clone();
        let params = (0..names.len())
            .map(|i| Ty::new(db, TyKind::Param(Some(identity), i as u32, names[i])))
            .collect();
        let generic = Ty::new(db, TyKind::Named(identity, params));
        let declared = declared_fields(db, program, generic).unwrap_or_default();
        let mut args = vec![None; names.len()];
        for field in fields {
            let found: Vec<(Name<'db>, Ty<'db>)> = match field {
                FieldArg::Field { path, value } if path.len() == 1 => {
                    if matches!(self.body.expr(*value), Expr::Closure { .. }) {
                        continue;
                    }
                    let ty = self.synth(*value);
                    self.typed.insert(*value, ty);
                    vec![(path[0], ty)]
                }
                // What the list gives anew says nothing of the spread's.
                FieldArg::Spread(value) => {
                    let ty = self.synth(*value);
                    self.typed.insert(*value, ty);
                    let given = |name: Name<'db>| {
                        fields.iter().any(
                            |f| matches!(f, FieldArg::Field { path, .. } if path.len() == 1 && path[0] == name),
                        )
                    };
                    fields_of(db, program, ty)
                        .unwrap_or_default()
                        .into_iter()
                        .filter(|(n, _)| !given(*n))
                        .collect()
                }
                FieldArg::Field { .. } => continue,
            };
            for (name, ty) in found {
                if let Some((_, pattern, _)) = declared.iter().find(|(n, ..)| *n == name) {
                    bind(db, program, identity, *pattern, ty, &mut args);
                }
            }
        }
        args.into_iter()
            .zip(names)
            .map(|(arg, name)| {
                arg.unwrap_or_else(|| {
                    let kind = ErrorKind::UninferredTypeArg {
                        function: item,
                        name,
                    };
                    self.error(Site::Expr(id), kind);
                    self.err_ty()
                })
            })
            .collect()
    }

    /// Checks a field list that builds a record of type `ty`: each field
    /// given once, by name, by a spread or by its default (§6.7).
    pub(super) fn build_record(&mut self, site: ExprId, ty: Ty<'db>, fields: &[FieldArg<'db>]) {
        let db = self.db;
        let program = self.program;
        let declared: Vec<(Name<'db>, Ty<'db>, bool)> = match declared_fields(db, program, ty) {
            Some(fields) => fields,
            None => fields_of(db, program, ty)
                .unwrap_or_default()
                .into_iter()
                .map(|(n, t)| (n, t, false))
                .collect(),
        };
        let mut given = vec![false; declared.len()];
        for field in fields {
            match field {
                FieldArg::Spread(value) => {
                    let spread = self.synth(*value);
                    let Some(supplied) = fields_of(db, program, spread) else {
                        if !spread.is_error(db) {
                            let kind = ErrorKind::Unsupported("spreads of non-records");
                            self.error(Site::Expr(*value), kind);
                        }
                        given.iter_mut().for_each(|g| *g = true);
                        continue;
                    };
                    for (i, (name, field_ty, _)) in declared.iter().enumerate() {
                        if let Some((_, t)) = supplied.iter().find(|(n, _)| n == name) {
                            given[i] = true;
                            // A field the list gives anew need not fit.
                            let replaced = fields.iter().any(|f| {
                                matches!(f, FieldArg::Field { path, .. } if path.len() == 1 && path[0] == *name)
                            });
                            if !replaced {
                                self.expect(Site::Expr(*value), *t, *field_ty);
                            }
                        }
                    }
                }
                FieldArg::Field { path, value } => {
                    let name = path[0];
                    let Some(i) = declared.iter().position(|(n, ..)| *n == name) else {
                        self.error(Site::Expr(*value), ErrorKind::UnknownField { name });
                        self.synth(*value);
                        continue;
                    };
                    let current = self.current_field(fields, name);
                    // A field is given once, whole or by distinct paths
                    // into it.
                    let again = fields
                        .iter()
                        .take_while(|f| !std::ptr::eq(*f, field))
                        .any(|f| {
                            matches!(f, FieldArg::Field { path: p, .. }
                                if p[0] == name && (p.len() == 1 || path.len() == 1 || p == path))
                        });
                    if again {
                        self.error(Site::Expr(*value), ErrorKind::DuplicateField { name });
                    }
                    given[i] = true;
                    let field_ty = declared[i].1;
                    if path.len() > 1 {
                        match current {
                            Some(_) => self.path_value(&path[1..], *value, field_ty),
                            None => {
                                self.error(Site::Expr(*value), ErrorKind::NoCurrentValue { name });
                                self.synth(*value);
                            }
                        }
                        continue;
                    }
                    self.field_value(name, *value, field_ty, current.is_some(), true);
                    // A transform takes the spread's value, which must fit.
                    let transforms = |t: Option<Ty<'db>>| t.is_some_and(|t| t.is_fn(db));
                    if let Some(current) = current
                        && transforms(self.exprs[value.index()])
                        && !transforms(Some(field_ty))
                    {
                        self.expect(Site::Expr(*value), current, field_ty);
                    }
                }
            }
        }
        for (i, (name, _, default)) in declared.iter().enumerate() {
            if !given[i] && !default {
                self.error(Site::Expr(site), ErrorKind::MissingField { name: *name });
            }
        }
    }

    /// The type of the field `name` the last spread of the list that has
    /// it gives: its current value, which an override may change (§6.7).
    fn current_field(&self, fields: &[FieldArg<'db>], name: Name<'db>) -> Option<Ty<'db>> {
        fields.iter().rev().find_map(|f| match f {
            FieldArg::Spread(value) => self.exprs[value.index()]
                .and_then(|t| fields_of(self.db, self.program, t))?
                .into_iter()
                .find(|(n, _)| *n == name)
                .map(|(_, t)| t),
            _ => None,
        })
    }

    /// An override of a field of type `field_ty`: a new value, or a
    /// function from the field's type to itself that transforms the
    /// current value, if there is one (§6.7). A field that holds a
    /// function takes a new value. A `strict` field keeps its type; one
    /// of an anonymous record takes a new value's. Gives the field's new
    /// type.
    fn field_value(
        &mut self,
        name: Name<'db>,
        value: ExprId,
        field_ty: Ty<'db>,
        current: bool,
        strict: bool,
    ) -> Ty<'db> {
        let db = self.db;
        if field_ty.is_error(db) || field_ty.is_fn(db) {
            return if strict {
                self.check(value, field_ty);
                field_ty
            } else {
                self.infer(value, Some(field_ty))
            };
        }
        let transform = Ty::new(
            db,
            TyKind::Fn {
                params: vec![field_ty],
                result: field_ty,
                pure: false,
            },
        );
        let found = if matches!(self.body.expr(value), Expr::Closure { .. }) {
            self.check(value, transform)
        } else {
            self.infer(value, Some(field_ty))
        };
        if !found.is_fn(db) {
            if !strict {
                return found;
            }
            self.expect(Site::Expr(value), found, field_ty);
        } else if !current {
            self.error(Site::Expr(value), ErrorKind::NoCurrentValue { name });
        } else {
            self.expect(Site::Expr(value), found, transform);
        }
        field_ty
    }

    /// `a.b.c: value` below a field of type `ty` whose current value a
    /// spread gives: the record is rebuilt with the change (§6.7).
    fn path_value(&mut self, path: &[Name<'db>], value: ExprId, ty: Ty<'db>) {
        let db = self.db;
        let name = path[0];
        let field =
            fields_of(db, self.program, ty).and_then(|fs| fs.into_iter().find(|(n, _)| *n == name));
        let Some((_, field_ty)) = field else {
            if !ty.is_error(db) {
                self.error(Site::Expr(value), ErrorKind::NoField { ty, name });
            }
            self.synth(value);
            return;
        };
        if path.len() > 1 {
            self.path_value(&path[1..], value, field_ty);
        } else {
            self.field_value(name, value, field_ty, true, true);
        }
    }

    /// An anonymous record literal, against the record type expected if
    /// there is one (§3.4).
    pub(super) fn record_literal(
        &mut self,
        fields: &[FieldArg<'db>],
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let wanted: Vec<(Name<'db>, Ty<'db>)> = expected
            .and_then(|e| {
                e.members(db)
                    .into_iter()
                    .find(|m| matches!(m.kind(db), TyKind::Record { .. }))
            })
            .and_then(|r| fields_of(db, self.program, r))
            .unwrap_or_default();
        let mut built: Vec<(Name<'db>, Ty<'db>)> = Vec::new();
        for field in fields {
            match field {
                FieldArg::Spread(value) => {
                    let spread = self.synth(*value);
                    match fields_of(db, self.program, spread) {
                        Some(supplied) => {
                            for (name, ty) in supplied {
                                if !built.iter().any(|(n, _)| *n == name) {
                                    built.push((name, ty));
                                }
                            }
                        }
                        None if spread.is_error(db) => {}
                        None => {
                            let kind = ErrorKind::Unsupported("spreads of non-records");
                            self.error(Site::Expr(*value), kind);
                        }
                    }
                }
                FieldArg::Field { path, value } => {
                    let name = path[0];
                    let spread = built.iter().position(|(n, _)| *n == name);
                    let explicit =
                        fields
                            .iter()
                            .take_while(|f| !std::ptr::eq(*f, field))
                            .any(|f| {
                                matches!(f, FieldArg::Field { path: p, .. }
                                if p[0] == name && (p.len() == 1 || path.len() == 1 || p == path))
                            });
                    if explicit {
                        self.error(Site::Expr(*value), ErrorKind::DuplicateField { name });
                    }
                    let current = spread.map(|i| built[i].1);
                    if path.len() > 1 {
                        match current {
                            Some(ty) => self.path_value(&path[1..], *value, ty),
                            None => {
                                self.error(Site::Expr(*value), ErrorKind::NoCurrentValue { name });
                                self.synth(*value);
                            }
                        }
                        continue;
                    }
                    // A transform keeps the field's type; a new value
                    // gives its own.
                    let ty = match current {
                        Some(current) => self.field_value(name, *value, current, true, false),
                        None => {
                            let field_expected =
                                wanted.iter().find(|(n, _)| *n == name).map(|(_, t)| *t);
                            self.infer(*value, field_expected)
                        }
                    };
                    match spread {
                        Some(i) => built[i].1 = ty,
                        None => built.push((name, ty)),
                    }
                }
            }
        }
        Ty::record(db, built, false)
    }

    /// The prelude's `Grid` (§12.3).
    pub(super) fn grid_item(&self) -> Option<ItemId<'db>> {
        prelude_item(self.db, self.program, "Grid").map(|g| type_identity(self.db, self.program, g))
    }

    /// A grid literal: rows of one width, the cell type from the expected
    /// grid type or the union of the cells (§12.3).
    pub(super) fn grid(
        &mut self,
        id: ExprId,
        rows: &[Vec<ExprId>],
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let Some(grid) = self.grid_item() else {
            return self.err_ty();
        };
        if let Some(first) = rows.first() {
            for (k, row) in rows.iter().enumerate().skip(1) {
                if row.len() != first.len() {
                    let kind = ErrorKind::RaggedGrid {
                        row: k,
                        width: first.len(),
                        found: row.len(),
                    };
                    self.error(Site::Expr(id), kind);
                }
            }
        }
        let items: Vec<ExprId> = rows.iter().flatten().copied().collect();
        let wanted = expected.and_then(|e| {
            e.members(db).into_iter().find_map(|m| match m.kind(db) {
                TyKind::Named(i, args) if *i == grid => args.first().copied(),
                _ => None,
            })
        });
        let cell = match wanted {
            Some(cell) => {
                for &item in &items {
                    self.check(item, cell);
                }
                cell
            }
            None if items.is_empty() => {
                self.error(Site::Expr(id), ErrorKind::CannotInfer);
                return self.err_ty();
            }
            None => {
                let types = items.iter().map(|&i| self.synth(i)).collect();
                self.join_all(types)
            }
        };
        Ty::new(db, TyKind::Named(grid, vec![cell]))
    }

    /// A list, set or grid literal: the element type comes from the
    /// expected collection type, or is the union of the elements.
    pub(super) fn collection(
        &mut self,
        id: ExprId,
        items: &[ExprId],
        expected: Option<Ty<'db>>,
        kinds: &[Builtin],
    ) -> Ty<'db> {
        if let Some((builtin, args)) = expected.and_then(|e| self.member_builtin(e, kinds))
            && args.len() == 1
        {
            for &item in items {
                self.check(item, args[0]);
            }
            return self.builtin_of(builtin, args);
        }
        if items.is_empty() {
            self.error(Site::Expr(id), ErrorKind::CannotInfer);
            return self.err_ty();
        }
        let types = items.iter().map(|&i| self.synth(i)).collect();
        let element = self.join_all(types);
        self.builtin_of(kinds[0], vec![element])
    }

    pub(super) fn map_literal(
        &mut self,
        id: ExprId,
        entries: &[(ExprId, ExprId)],
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        if let Some((_, args)) = expected.and_then(|e| self.member_builtin(e, &[Builtin::Map]))
            && args.len() == 2
        {
            for &(key, value) in entries {
                self.check(key, args[0]);
                self.check(value, args[1]);
            }
            return self.builtin_of(Builtin::Map, args);
        }
        if entries.is_empty() {
            self.error(Site::Expr(id), ErrorKind::CannotInfer);
            return self.err_ty();
        }
        let keys = entries.iter().map(|&(k, _)| self.synth(k)).collect();
        let values = entries.iter().map(|&(_, v)| self.synth(v)).collect();
        let (keys, values) = (self.join_all(keys), self.join_all(values));
        self.builtin_of(Builtin::Map, vec![keys, values])
    }

    /// The one member of `ty` that is one of the builtins, with its
    /// arguments.
    pub(super) fn member_builtin(
        &self,
        ty: Ty<'db>,
        kinds: &[Builtin],
    ) -> Option<(Builtin, Vec<Ty<'db>>)> {
        let db = self.db;
        let found: Vec<(Builtin, Vec<Ty<'db>>)> = ty
            .members(db)
            .into_iter()
            .filter_map(|m| match m.kind(db) {
                TyKind::Builtin(b, args) if kinds.contains(b) => Some((*b, args.clone())),
                _ => None,
            })
            .collect();
        match <[_; 1]>::try_from(found) {
            Ok([one]) => Some(one),
            Err(_) => None,
        }
    }

    fn field_ty(&self, ty: Ty<'db>, name: Name<'db>) -> Option<Ty<'db>> {
        fields_of(self.db, self.program, ty)?
            .into_iter()
            .find(|(n, _)| *n == name)
            .map(|(_, t)| t)
    }

    /// `e[i]`: a list element, or a map value as an option (§6.5).
    pub(super) fn index(&mut self, id: ExprId, base: ExprId, args: &[ExprId]) -> Ty<'db> {
        let db = self.db;
        let base_ty = self.synth(base);
        match (base_ty.kind(db), args) {
            (TyKind::Builtin(Builtin::List, element), [i]) => {
                let element = element[0];
                let int = self.builtin(Builtin::Int);
                self.check(*i, int);
                element
            }
            (TyKind::Builtin(Builtin::Map, kv), [key]) => {
                let (k, v) = (kv[0], kv[1]);
                self.check(*key, k);
                self.option(v)
            }
            // `g[row, column]` (§19.11).
            (TyKind::Named(item, cell), [row, column]) if Some(*item) == self.grid_item() => {
                let cell = cell[0];
                let int = self.builtin(Builtin::Int);
                self.check(*row, int);
                self.check(*column, int);
                cell
            }
            _ => {
                if !base_ty.is_error(db) {
                    self.error(Site::Expr(id), ErrorKind::NotIndexable { ty: base_ty });
                }
                for &arg in args {
                    self.synth(arg);
                }
                self.err_ty()
            }
        }
    }

    /// `?.`: the access on the members of the receiver that are not
    /// `Empty`, and `Empty` for the rest, so the result is `V | Empty[V]`
    /// for the access's result `V` without its own `Empty` members
    /// (§6.8).
    pub(super) fn optional(
        &mut self,
        id: ExprId,
        receiver_ty: Ty<'db>,
        access: impl FnOnce(&mut Self, Ty<'db>) -> Ty<'db>,
    ) -> Ty<'db> {
        let db = self.db;
        if receiver_ty.is_error(db) {
            return access(self, receiver_ty);
        }
        let empty = self.empty;
        let is_empty = |t: &Ty<'db>| matches!(t.kind(db), TyKind::Named(i, _) if Some(*i) == empty);
        let members = receiver_ty.members(db);
        if !members.iter().any(is_empty) {
            self.error(Site::Expr(id), ErrorKind::NeverEmpty { ty: receiver_ty });
            return access(self, receiver_ty);
        }
        let present = members
            .into_iter()
            .filter(|m| !is_empty(m))
            .fold(Ty::never(db), |a, m| self.join(a, m));
        let result = access(self, present);
        if result.is_error(db) {
            return result;
        }
        let value = result
            .members(db)
            .into_iter()
            .filter(|m| !is_empty(m))
            .fold(Ty::never(db), |a, m| self.join(a, m));
        let empty = match self.empty {
            Some(item) => Ty::new(db, TyKind::Named(item, vec![value])),
            None => return self.err_ty(),
        };
        self.optional.push((
            id,
            Optional {
                present,
                result,
                empty,
            },
        ));
        self.join(result, empty)
    }

    /// `receiver.name(args)` with the receiver of type `receiver_ty`: a
    /// function-valued field called, or a call through UFCS (§6.3).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn method_call(
        &mut self,
        id: ExprId,
        receiver: ExprId,
        receiver_ty: Ty<'db>,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        if let Some(field) = self.field_ty(receiver_ty, name)
            && field.is_fn(db)
        {
            self.callees.push((id, Callee::Value));
            return self.call_value(id, field, args, fields);
        }
        if name.text(db) == "update"
            && args.is_empty()
            && let Some(fields) = fields
            && self.updates_value(receiver_ty, functions)
        {
            return self.update_value(id, receiver_ty, fields);
        }
        if functions.is_empty() {
            self.error(
                Site::Expr(id),
                ErrorKind::NoField {
                    ty: receiver_ty,
                    name,
                },
            );
            self.synth_args(args, fields);
            return self.err_ty();
        }
        let receiver = Some(Arg::Receiver(receiver, receiver_ty));
        self.resolve(
            id, None, name, functions, None, receiver, args, fields, expected, None,
        )
    }

    /// Whether `v.update(list)` rebuilds the value (§6.7.1): `v` is a
    /// record, and no function `update` takes it.
    fn updates_value(&self, receiver_ty: Ty<'db>, functions: &[ItemId<'db>]) -> bool {
        let db = self.db;
        fields_of(db, self.program, receiver_ty).is_some()
            && !functions.iter().any(|&f| {
                signature(db, self.program, f)
                    .params
                    .first()
                    .is_some_and(|p| {
                        matches!(p.ty.kind(db), TyKind::Param(..))
                            || is_subtype(db, self.program, receiver_ty, p.ty)
                    })
            })
    }

    /// `v.update(list)`: `v` rebuilt as its own type, each path of the
    /// list a new value or a transform of the current one (§6.7.1).
    fn update_value(&mut self, id: ExprId, ty: Ty<'db>, fields: &[FieldArg<'db>]) -> Ty<'db> {
        for (k, field) in fields.iter().enumerate() {
            match field {
                FieldArg::Spread(value) => {
                    self.error(Site::Expr(*value), ErrorKind::SpreadInUpdate);
                    self.synth(*value);
                }
                FieldArg::Field { path, value } => {
                    let again = fields[..k].iter().any(|f| {
                        matches!(f, FieldArg::Field { path: p, .. }
                            if p[0] == path[0] && (p.len() == 1 || path.len() == 1 || p == path))
                    });
                    if again {
                        let kind = ErrorKind::DuplicateField { name: path[0] };
                        self.error(Site::Expr(*value), kind);
                    }
                    self.path_value(path, *value, ty);
                }
            }
        }
        self.callees.push((id, Callee::Update(ty)));
        ty
    }

    /// `receiver.name` with the receiver of type `receiver_ty`: a field,
    /// or a call through UFCS (§6.3).
    pub(super) fn field(
        &mut self,
        id: ExprId,
        receiver: ExprId,
        receiver_ty: Ty<'db>,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        if let Some(field) = self.field_ty(receiver_ty, name) {
            return field;
        }
        if receiver_ty.is_error(db) {
            return receiver_ty;
        }
        if functions.is_empty() {
            let kind = ErrorKind::NoField {
                ty: receiver_ty,
                name,
            };
            self.error(Site::Expr(id), kind);
            return self.err_ty();
        }
        let receiver = Some(Arg::Receiver(receiver, receiver_ty));
        self.resolve(
            id,
            None,
            name,
            functions,
            None,
            receiver,
            &[],
            None,
            expected,
            None,
        )
    }

    /// `Option[T]`, which is `T | Empty[T]` (§3.6.1).
    fn option(&self, ty: Ty<'db>) -> Ty<'db> {
        match self.empty {
            Some(empty) => {
                let empty = Ty::new(self.db, TyKind::Named(empty, vec![ty]));
                self.join(ty, empty)
            }
            None => self.err_ty(),
        }
    }
}
