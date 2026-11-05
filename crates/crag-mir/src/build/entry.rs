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

//! The entries of a body: the code of a function's or value's body, of
//! a C function's call, of the checks of a type's conditions, of a part,
//! a closure, a default, an adapter, the dispose code of a type and a
//! function used as a value, with the environment a closure captures.

use super::*;

impl<'a, 'db> MirBuilder<'a, 'db> {
    /// The body of the owner itself.
    pub(super) fn body_entry(&mut self, root: ExprId) -> Option<Start<'a, 'db>> {
        let body = self.body;
        for param in &body.params {
            self.binding(param.binding);
        }
        self.params = body.params.len();
        self.test = self.types.result.is_none();
        self.result = match self.types.result {
            Some(result) => self.subst(result),
            None => Ty::unit(self.db),
        };
        if let Owner::Item(item) = *self.instance.owner(self.db)
            && item.kind(self.db).is_value()
        {
            // The code of a value keeps what it gives (§11.6.2), so it ends
            // in no tail call.
            return Some(Box::new(move |b| {
                let value = b.temp(b.result);
                b.eval(root, Dest::Value(value));
                b.terminate(Terminator::Return(Operand::Local(value)));
            }));
        }
        Some(Box::new(move |b| b.eval(root, Dest::Return)))
    }

    /// The code of a C function (§16.3): the call, its result as the
    /// import declares it, then the record of the result, its out
    /// parameters and `errno`, if it gives one.
    pub(super) fn c_entry(&mut self, item: ItemId<'db>) -> Option<Start<'a, 'db>> {
        let db = self.db;
        let sig = signature(db, self.program, item);
        let (c_params, c_result) = crag_types::c_signature(db, self.program, item);
        let args: Vec<Local> = sig.params.iter().map(|p| self.temp(p.ty)).collect();
        self.params = args.len();
        self.result = sig.result?;
        let errno = crag_hir::c_function_info(db, item).is_some_and(|c| c.errno);
        let record = errno || c_params.iter().any(|&t| crag_types::c_out(db, t).is_some());
        // The type the C result has in a call: the record's `result`.
        let value_ty = match (record, self.result.kind(db)) {
            (true, TyKind::Record { fields, .. }) => fields
                .iter()
                .find(|(name, _)| name.text(db) == "result")
                .map(|&(_, t)| t)?,
            _ => self.result,
        };
        Some(Box::new(move |b| {
            // A plain float is checked too: only a finite one may come.
            let form = match (CForm::of(db, c_result), c_result.as_builtin(db)) {
                (CForm::Value, Some((Builtin::Float | Builtin::CF32, _))) => {
                    CForm::Float([false; 3])
                }
                (form, _) => form,
            };
            let raw_ty = match form {
                CForm::Value | CForm::Void | CForm::Invalid => c_result,
                _ => Ty::builtin(db, Builtin::UInt64),
            };
            let ops = args.into_iter().map(Operand::Local).collect();
            let raw = b.assign(raw_ty, Rvalue::Intrinsic(Intrinsic::CCall(item), ops));
            let mut value = match form {
                CForm::Value | CForm::Void | CForm::Invalid => raw,
                _ => b.c_value(form, raw, value_ty),
            };
            if record {
                let mut fields = vec![(Name::new(db, "result".to_string()), value)];
                let body = b.body;
                for (index, (param, &ty)) in body.params.iter().zip(&c_params).enumerate() {
                    let (Some(out), Some(name)) =
                        (crag_types::c_out(db, ty), body.binding(param.binding).name)
                    else {
                        continue;
                    };
                    let op = b.assign(
                        out,
                        Rvalue::Intrinsic(Intrinsic::COut(index as u32), vec![]),
                    );
                    fields.push((name, op));
                }
                if errno {
                    let int32 = Ty::builtin(db, Builtin::Int32);
                    let at = c_params.len() as u32;
                    let op = b.assign(int32, Rvalue::Intrinsic(Intrinsic::COut(at), vec![]));
                    fields.push((Name::new(db, "errno".to_string()), op));
                }
                fields.sort_by(|(x, _), (y, _)| x.text(db).cmp(y.text(db)));
                let ty = b.result;
                let record = Rvalue::Record {
                    ty,
                    fields,
                    dispose: None,
                    reuse: None,
                };
                value = b.assign(ty, record);
            }
            b.terminate(Terminator::Return(value));
        }))
    }

    /// A C result as its import declares it, from the word the call gave
    /// (Specification §16.1, §3.1.4): a pointer becomes a `CStr` or text,
    /// or `Empty` when it is null and the type allows it; a float becomes
    /// a `Float` or the tag of what it is. What the type does not allow
    /// is a `Fault`.
    fn c_value(&mut self, form: CForm, raw: Operand<'db>, ty: Ty<'db>) -> Operand<'db> {
        let db = self.db;
        let dst = self.temp(ty);
        let join = self.new_block();
        let tag = |name: &str| {
            ty.members(db).into_iter().find(|m| match m.kind(db) {
                TyKind::Named(item, _) => item.name(db).text(db) == name,
                _ => false,
            })
        };
        match form {
            CForm::Float(_) => {
                let class = self.assign(self.int(), Rvalue::Intrinsic(Intrinsic::CClass, vec![]));
                for (k, name) in ["", "NaN", "PosInfinity", "NegInfinity"]
                    .into_iter()
                    .enumerate()
                {
                    let code = Operand::Const(Constant::Int(k as i128));
                    let is = self.compare(CmpOp::Eq, Builtin::Int, class.clone(), code);
                    let (this, next) = (self.new_block(), self.new_block());
                    self.terminate(Terminator::Branch {
                        cond: is,
                        then: this,
                        otherwise: next,
                    });
                    self.switch_to(this);
                    let float = ty
                        .members(db)
                        .into_iter()
                        .find(|m| {
                            matches!(m.as_builtin(db), Some((Builtin::Float | Builtin::CF32, _)))
                        })
                        .unwrap_or(ty);
                    match (k, tag(name)) {
                        (0, _) => {
                            let x = self.assign(
                                float,
                                Rvalue::Intrinsic(Intrinsic::Word, vec![raw.clone()]),
                            );
                            self.assign_to(dst, x, float);
                        }
                        (_, Some(t)) => self.assign_to(dst, Operand::Const(Constant::Tag(t)), t),
                        (_, None) => {
                            self.c_fault(form);
                            self.switch_to(next);
                            continue;
                        }
                    }
                    self.terminate(Terminator::Jump(join));
                    self.switch_to(next);
                }
                self.c_fault(form);
            }
            _ => {
                let zero = Operand::Const(Constant::Int(0));
                let null = self.compare(CmpOp::Eq, Builtin::UInt64, raw.clone(), zero);
                let (empty, present) = (self.new_block(), self.new_block());
                self.terminate(Terminator::Branch {
                    cond: null,
                    then: empty,
                    otherwise: present,
                });
                self.switch_to(empty);
                match tag("Empty") {
                    Some(t) => {
                        self.assign_to(dst, Operand::Const(Constant::Tag(t)), t);
                        self.terminate(Terminator::Jump(join));
                    }
                    None => {
                        self.c_fault(form);
                    }
                }
                self.switch_to(present);
                let bytes_ty = Ty::builtin(db, Builtin::Bytes);
                let text = matches!(form, CForm::Str | CForm::OptionStr);
                let of = Intrinsic::CStrOf { nul: !text };
                let bytes = self.assign(bytes_ty, Rvalue::Intrinsic(of, vec![raw]));
                if text {
                    self.c_text(bytes, dst, join);
                } else {
                    let cstr = ty
                        .members(db)
                        .into_iter()
                        .find(|&m| crag_types::is_cstr(db, m))
                        .unwrap_or(ty);
                    let record = Rvalue::Record {
                        ty: cstr,
                        fields: vec![(Name::new(db, "bytes".to_string()), bytes)],
                        dispose: None,
                        reuse: None,
                    };
                    let value = self.assign(cstr, record);
                    self.assign_to(dst, value, cstr);
                    self.terminate(Terminator::Jump(join));
                }
            }
        }
        self.switch_to(join);
        Operand::Local(dst)
    }

    /// The `ForeignFault` of a C result its import does not allow, naming what
    /// came.
    fn c_fault(&mut self, form: CForm) {
        let what = match form {
            CForm::Float(_) => "a C function gave a float that its import does not allow",
            _ => "a C function gave a null pointer where its import allows none",
        };
        self.terminate(Terminator::Trap {
            kind: TrapKind::ForeignFault,
            site: None,
            detail: Some(what.to_string()),
            catch: None,
        });
    }

    /// The bytes as a `Str` in `dst`, or `NotUtf8`, then on to `join`.
    fn c_text(&mut self, bytes: Operand<'db>, dst: Local, join: BlockId) {
        let db = self.db;
        let int = self.int();
        let valid = self.assign(
            int,
            Rvalue::Intrinsic(Intrinsic::TextUtf8, vec![bytes.clone()]),
        );
        let zero = Operand::Const(Constant::Int(0));
        let invalid = self.compare(CmpOp::Eq, Builtin::Int, valid, zero);
        let (bad, good) = (self.new_block(), self.new_block());
        self.terminate(Terminator::Branch {
            cond: invalid,
            then: bad,
            otherwise: good,
        });
        self.switch_to(bad);
        if let Some(item) = prelude_item(db, self.program, "NotUtf8") {
            let not_utf8 = Ty::new(db, TyKind::Named(item, Vec::new()));
            let record = Rvalue::Record {
                ty: not_utf8,
                fields: Vec::new(),
                dispose: None,
                reuse: None,
            };
            let value = self.assign(not_utf8, record);
            self.assign_to(dst, value, not_utf8);
        }
        self.terminate(Terminator::Jump(join));
        self.switch_to(good);
        let str_ty = Ty::builtin(db, Builtin::Str);
        let text = self.assign(str_ty, Rvalue::Intrinsic(Intrinsic::TextCast, vec![bytes]));
        self.assign_to(dst, text, str_ty);
        self.terminate(Terminator::Jump(join));
    }

    /// The value conditions of a type, against the value it is called
    /// with: the number of the first that fails, from one, or zero
    /// (§3.10.1).
    pub(super) fn check_entry(&mut self) -> Option<Start<'a, 'db>> {
        let decl = self.body.type_decl.as_ref()?;
        let this = decl.this?;
        let ty = self.binding_ty(this)?;
        let value = self.local(ty, None);
        self.params = 1;
        let int_ty = self.int();
        self.result = int_ty;
        let fields = decl.field_bindings.clone();
        let conditions: Vec<ExprId> = decl.conditions.iter().map(|c| c.value).collect();
        Some(Box::new(move |b| {
            let local = b.binding(this);
            b.push(Statement::Assign(local, Rvalue::Use(Operand::Local(value))));
            for (name, binding) in fields {
                let local = b.binding(binding);
                let place = Place {
                    local: value,
                    path: vec![Step::Field(name)],
                };
                b.push(Statement::Assign(local, Rvalue::Read(place)));
            }
            for (k, condition) in conditions.into_iter().enumerate() {
                let (holds, fails) = (b.new_block(), b.new_block());
                b.branch_on(condition, holds, fails);
                b.switch_to(fails);
                b.terminate(Terminator::Return(int(k as i128 + 1)));
                b.switch_to(holds);
            }
            b.terminate(Terminator::Return(int(0)));
        }))
    }

    /// Checks a value just built against the conditions of its type and of
    /// its parents, which trap with `ConditionFailed` naming the one that
    /// fails (§3.10.1).
    pub(super) fn check_conditions(
        &mut self,
        value: Operand<'db>,
        ty: Ty<'db>,
        site: ExprId,
    ) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        let mut checked = Some(ty);
        let mut value_local: Option<Local> = None;
        while let Some(t) = checked {
            checked = crag_types::parent(db, program, t);
            let TyKind::Named(item, args) = t.kind(db) else {
                continue;
            };
            let body = hir_body(db, program, Owner::Item(*item));
            let Some(decl) = body.type_decl.as_ref().filter(|d| !d.conditions.is_empty()) else {
                continue;
            };
            let labels: Vec<String> = decl.conditions.iter().map(|c| c.label(db)).collect();
            let local = *value_local.get_or_insert_with(|| self.materialize(value.clone(), ty));
            let as_t = self.coerce(Operand::Local(local), ty, t);
            let code = InstanceKey::new(
                db,
                Owner::Item(*item),
                args.clone(),
                Vec::new(),
                Vec::new(),
                Entry::Check,
            );
            let int_ty = self.int();
            let failed = self.call_code(code, vec![as_t], int_ty, site);
            for (k, label) in labels.into_iter().enumerate() {
                let (this, next) = (self.new_block(), self.new_block());
                let is = self.compare(
                    CmpOp::Eq,
                    Builtin::Int,
                    Operand::Local(failed),
                    int(k as i128 + 1),
                );
                self.terminate(Terminator::Branch {
                    cond: is,
                    then: this,
                    otherwise: next,
                });
                self.switch_to(this);
                self.terminate(Terminator::Trap {
                    kind: TrapKind::ConditionFailed,
                    site: Some(site),
                    detail: Some(label),
                    catch: None,
                });
                self.switch_to(next);
            }
        }
        match value_local {
            Some(local) => Operand::Local(local),
            None => value,
        }
    }

    /// `A(x)` for a conditioned alias `A`: `x` checked against the alias's
    /// conditions, an `A` when all hold, else `Invalid` naming the first
    /// that fails and where the conversion is written (§3.10.1).
    pub(super) fn refine(&mut self, expr: ExprId, ty: Ty<'db>, arg: ExprId) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        let TyKind::Named(item, args) = ty.kind(db) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let target = crag_types::unrefined(db, program, ty);
        let op = self.expr(arg);
        let op = self.coerce(op, self.ty(arg), target);
        let value = self.materialize(op, target);
        let int_ty = self.int();
        let code = InstanceKey::new(
            db,
            Owner::Item(*item),
            args.clone(),
            Vec::new(),
            Vec::new(),
            Entry::Check,
        );
        let failed = self.call_code(code, vec![Operand::Local(value)], int_ty, expr);
        let result = self.ty(expr);
        let out = self.temp(result);
        let (ok, fails, join) = (self.new_block(), self.new_block(), self.new_block());
        let passed = self.compare(CmpOp::Eq, Builtin::Int, Operand::Local(failed), int(0));
        self.terminate(Terminator::Branch {
            cond: passed,
            then: ok,
            otherwise: fails,
        });
        self.switch_to(ok);
        let checked = self.temp(ty);
        self.assign_to(checked, Operand::Local(value), target);
        self.assign_to(out, Operand::Local(checked), ty);
        self.terminate(Terminator::Jump(join));
        self.switch_to(fails);
        let body = hir_body(db, program, Owner::Item(*item));
        let labels: Vec<String> = body
            .type_decl
            .as_ref()
            .map(|d| d.conditions.iter().map(|c| c.label(db)).collect())
            .unwrap_or_default();
        let invalid_item = prelude_item(db, program, "Invalid");
        let origin_item = prelude_item(db, program, "Origin");
        let (Some(invalid_item), Some(origin_item)) = (invalid_item, origin_item) else {
            self.trap(TrapKind::Error, Some(expr));
            self.switch_to(join);
            return Operand::Local(out);
        };
        let invalid = Ty::new(db, TyKind::Named(invalid_item, Vec::new()));
        let origin_ty = Ty::new(db, TyKind::Named(origin_item, Vec::new()));
        let (module, line, column) = self.origin_of(expr);
        for (k, label) in labels.into_iter().enumerate() {
            let (this, next) = (self.new_block(), self.new_block());
            let is = self.compare(
                CmpOp::Eq,
                Builtin::Int,
                Operand::Local(failed),
                int(k as i128 + 1),
            );
            self.terminate(Terminator::Branch {
                cond: is,
                then: this,
                otherwise: next,
            });
            self.switch_to(this);
            let name = |n: &str| crag_hir::Name::new(db, n.to_string());
            let origin = self.assign(
                origin_ty,
                Rvalue::Record {
                    ty: origin_ty,
                    fields: vec![
                        (
                            name("module"),
                            Operand::Const(Constant::Str(module.clone())),
                        ),
                        (name("line"), int(line)),
                        (name("column"), int(column)),
                    ],
                    dispose: None,
                    reuse: None,
                },
            );
            let error = self.assign(
                invalid,
                Rvalue::Record {
                    ty: invalid,
                    fields: vec![
                        (name("condition"), Operand::Const(Constant::Str(label))),
                        (name("origin"), origin),
                    ],
                    dispose: None,
                    reuse: None,
                },
            );
            self.assign_to(out, error, invalid);
            self.terminate(Terminator::Jump(join));
            self.switch_to(next);
        }
        self.trap(TrapKind::Error, Some(expr));
        self.switch_to(join);
        Operand::Local(out)
    }

    /// The module, line and column, from one, where an expression is
    /// written.
    fn origin_of(&self, expr: ExprId) -> (String, i128, i128) {
        let db = self.db;
        let module = self.owner.module(db);
        let source = module.file(db).text(db);
        let at = lower_body(db, self.program, self.owner)
            .source_map
            .exprs
            .get(expr.index())
            .map_or(0, |r| r.start as usize)
            .min(source.len());
        let before = &source[..at];
        let line = before.matches('\n').count() as i128 + 1;
        let start = before.rfind('\n').map_or(0, |i| i + 1);
        let column = before[start..].chars().count() as i128 + 1;
        (module.path(db).clone(), line, column)
    }

    /// The part of a module-level `let` with a pattern bound to the item's
    /// name: its value, which the value's code keeps, matched.
    pub(super) fn part_entry(&mut self) -> Option<Start<'a, 'db>> {
        let db = self.db;
        let body = self.body;
        let Owner::Item(item) = *self.instance.owner(db) else {
            return None;
        };
        let (pat, _) = body.pattern?;
        let binding = (0..body.bindings.len() as u32)
            .map(BindingId)
            .find(|&b| body.binding(b).name == Some(*item.name(db)))?;
        let whole = self.types.result.map(|t| self.subst(t))?;
        self.result = self.binding_ty(binding)?;
        Some(Box::new(move |b| {
            let code = InstanceKey::body(db, Owner::Item(item));
            let value = b.call_code(code, Vec::new(), whole, b.body.root.unwrap_or(ExprId(0)));
            b.matched(pat, Operand::Local(value), whole, None);
            let part = b.binding(binding);
            b.terminate(Terminator::Return(Operand::Local(part)));
        }))
    }

    /// The code of a closure literal or a local function: the environment
    /// and the parameters, then the captured values read out of it.
    pub(super) fn closure_entry(&mut self, frame: ExprId) -> Option<Start<'a, 'db>> {
        let db = self.db;
        let body = self.body;
        let local_fn = local_fn_of(body, frame);
        let own = local_fn.map(|(binding, _)| binding);
        let ty = match local_fn {
            Some((binding, _)) => self.binding_ty(binding)?,
            None => self.expr_ty(frame)?,
        };
        // A `lazy` expression is the code of a function without
        // parameters.
        let (param_tys, result) = match (ty.kind(db), body.expr(frame)) {
            (_, Expr::Lazy(_)) => match ty.as_builtin(db) {
                Some((Builtin::Lazy, &[value])) => (Vec::new(), value),
                _ => return None,
            },
            _ => match ty.as_fn(db) {
                Some((params, result, _)) => (params.to_vec(), result),
                None => return None,
            },
        };
        let param_tys = &param_tys;
        self.result = result;
        let (captures, env_ty) = self.environment(frame, own);
        // The code reads its captures out of the environment as it is
        // made, an `Expr`'s tree before them and its module values after.
        let env_ty = self.with_module_values(frame, env_ty, captures.len());
        let (env_ty, _) = self.with_tree(frame, env_ty, Vec::new());
        let env = self.temp(env_ty);
        self.env = true;
        // Parameters that are patterns are matched once all are in place.
        let mut patterns = Vec::new();
        let inner = match (local_fn, body.expr(frame)) {
            (Some((_, function)), _) => {
                for param in &function.params {
                    self.binding(param.binding);
                }
                frame
            }
            (
                None,
                Expr::Closure {
                    params,
                    body: inner,
                },
            ) => {
                for (param, &param_ty) in params.iter().zip(param_tys) {
                    match body.pat(param.pat) {
                        Pat::Bind { binding, sub: None } => {
                            self.binding(*binding);
                        }
                        _ => patterns.push((param.pat, self.temp(param_ty), param_ty)),
                    }
                }
                *inner
            }
            (None, Expr::Lazy(inner)) => *inner,
            _ => return None,
        };
        self.params = self.locals.len();
        for (i, &binding) in captures.iter().enumerate() {
            let local = self.binding(binding);
            let place = Place {
                local: env,
                path: vec![Step::Field(capture_name(db, i))],
            };
            self.push(Statement::Assign(local, Rvalue::Read(place)));
        }
        for (k, (value, at)) in self.module_captures(frame).into_iter().enumerate() {
            let local = self.temp(self.ty(at));
            let place = Place {
                local: env,
                path: vec![Step::Field(capture_name(db, captures.len() + k))],
            };
            self.push(Statement::Assign(local, Rvalue::Read(place)));
            self.module_locals.push((value, local));
        }
        // A local function calls itself through its own environment.
        if let Some(own) = own {
            let local = self.binding(own);
            let code = self.closure_code(frame);
            let value = Rvalue::FnValue {
                code,
                env: Operand::Local(env),
            };
            self.push(Statement::Assign(local, value));
        }
        Some(Box::new(move |b| {
            for (pat, local, ty) in patterns {
                b.matched(pat, Operand::Local(local), ty, None);
            }
            b.eval(inner, Dest::Return)
        }))
    }

    /// The code of a default: the parameters before it, when it is a
    /// parameter's, then the default's value.
    pub(super) fn default_entry(&mut self, default: ExprId) -> Option<Start<'a, 'db>> {
        let body = self.body;
        let field = |f: &&crag_hir::FieldDecl<'db>| f.default == Some(default);
        self.result = match body.params.iter().position(|p| p.default == Some(default)) {
            Some(i) => {
                for param in &body.params[..i] {
                    self.binding(param.binding);
                }
                self.binding_ty(body.params[i].binding)?
            }
            None => self.type_ref(body.type_decl.as_ref()?.fields.iter().find(field)?.ty)?,
        };
        self.params = self.locals.len();
        Some(Box::new(move |b| b.eval(default, Dest::Return)))
    }

    /// The code of an adapter: the environment holding the function value
    /// and the parameters of the type it is called as, then a call of the
    /// value with the arguments converted to its parameters.
    pub(super) fn adapter_entry(&mut self) -> Option<Start<'a, 'db>> {
        let db = self.db;
        let [from, to] = self.instance.args(db)[..] else {
            return None;
        };
        let (Some((from_params, from_result, _)), Some((to_params, to_result, _))) =
            (from.as_fn(db), to.as_fn(db))
        else {
            return None;
        };
        self.result = to_result;
        let env_ty = Ty::record(db, vec![(capture_name(db, 0), from)], false);
        let env = self.temp(env_ty);
        self.env = true;
        let args: Vec<(Local, Ty<'db>)> = to_params.iter().map(|&t| (self.temp(t), t)).collect();
        self.params = self.locals.len();
        let from_params = from_params.to_vec();
        Some(Box::new(move |b| {
            let place = Place {
                local: env,
                path: vec![Step::Field(capture_name(db, 0))],
            };
            let callee = b.assign(from, Rvalue::Read(place));
            let ops = args
                .iter()
                .zip(&from_params)
                .map(|(&(local, ty), &param)| b.coerce(Operand::Local(local), ty, param))
                .collect();
            let dst = b.temp(from_result);
            let target = b.new_block();
            b.terminate(Terminator::CallValue {
                callee,
                args: ops,
                dst,
                target,
                site: ExprId(0),
                unwind: None,
                catch: None,
            });
            b.switch_to(target);
            b.finish_dest(Operand::Local(dst), from_result, Dest::Return);
        }))
    }

    /// The function value as one of another function type, through an
    /// adapter when the two lay out parameters or results differently.
    pub(super) fn adapted(
        &mut self,
        op: Operand<'db>,
        from: Ty<'db>,
        to: Ty<'db>,
    ) -> Option<Operand<'db>> {
        let db = self.db;
        let (Some((a, r, _)), Some((b, s, _))) = (from.as_fn(db), to.as_fn(db)) else {
            return None;
        };
        if a == b && r == s {
            return None;
        }
        let value = self.materialize(op, from);
        let code = InstanceKey::new(
            db,
            self.owner,
            vec![from, to],
            Vec::new(),
            Vec::new(),
            Entry::Adapter,
        );
        let env = Ty::record(db, vec![(capture_name(db, 0), from)], false);
        Some(self.assign(
            to,
            Rvalue::Closure {
                code,
                env,
                captures: vec![Operand::Local(value)],
                placement: ClosurePlacement::Heap,
            },
        ))
    }

    /// The dispose code of the type: the box, whose count reached zero and
    /// which the runtime gave a reference again, then a call of the
    /// handler, which takes it.
    pub(super) fn dispose_entry(&mut self) -> Option<Start<'a, 'db>> {
        let db = self.db;
        let Owner::Item(item) = self.owner else {
            return None;
        };
        let ty = Ty::new(db, TyKind::Named(item, self.instance.args(db).clone()));
        let handler = lifecycle_handler(db, self.program, ty, "Dispose")?;
        let value = self.temp(ty);
        self.params = self.locals.len();
        Some(Box::new(move |b| {
            let param = match handler.ty.kind(db) {
                TyKind::Fn { params, .. } => params.first().copied().unwrap_or(ty),
                _ => ty,
            };
            let arg = b.coerce(Operand::Local(value), ty, param);
            let site = handler.clause;
            if b.call_handler(&handler, vec![arg], site).is_none() {
                b.trap(TrapKind::Error, Some(site));
                return;
            }
            b.terminate(Terminator::Return(b.unit()));
        }))
    }

    /// The dispose code a box of a record type holds: that of the nearest
    /// type it is or spreads with a handler.
    pub(super) fn dispose_code(&self, ty: Ty<'db>) -> Option<InstanceKey<'db>> {
        let db = self.db;
        let (declaring, _) = dispose_handler(db, self.program, ty)?;
        let TyKind::Named(item, args) = declaring.kind(db) else {
            return None;
        };
        Some(InstanceKey::new(
            db,
            Owner::Item(*item),
            args.clone(),
            Vec::new(),
            Vec::new(),
            Entry::Dispose,
        ))
    }

    /// The code of a declared function used as a value at `expr`: an empty
    /// environment and the parameters, then the call, split by the
    /// members of union parameters when the value is lifted (§11.5.5).
    pub(super) fn function_entry(&mut self, expr: ExprId) -> Option<Start<'a, 'db>> {
        let db = self.db;
        let ty = self.expr_ty(expr)?;
        let (params, result, _) = ty.as_fn(db)?;
        let callee = self.types.callee(expr)?.clone();
        let instance = self.callee_instance(&callee);
        self.result = result;
        self.temp(Ty::unit(db));
        self.env = true;
        let args: Vec<(Local, Ty<'db>)> = params.iter().map(|&t| (self.temp(t), t)).collect();
        self.params = self.locals.len();
        Some(Box::new(move |b| match (callee, instance) {
            (_, Some(instance)) => b.forward(expr, &instance, &args),
            (Callee::Dispatch(dispatch), _) => {
                let positional = vec![expr; args.len()];
                let functions = match b.dispatch_functions(expr, &dispatch, &positional) {
                    Ok(functions) => functions,
                    Err(op) => {
                        let result = b.result;
                        return b.finish_dest(op, result, Dest::Return);
                    }
                };
                let dst = b.temp(b.result);
                let join = b.new_block();
                b.dispatch_arms(
                    expr,
                    &dispatch,
                    &functions,
                    (&args, &Named::Params(Vec::new())),
                    &mut Vec::new(),
                    dst,
                    join,
                );
                b.switch_to(join);
                let result = b.result;
                b.finish_dest(Operand::Local(dst), result, Dest::Return);
            }
            _ => {
                let op = b.trap(TrapKind::Error, Some(expr));
                let result = b.result;
                b.finish_dest(op, result, Dest::Return);
            }
        }))
    }

    /// Calls a function with the parameters of a value's code.
    fn forward(&mut self, expr: ExprId, instance: &Instance<'db>, args: &[(Local, Ty<'db>)]) {
        let db = self.db;
        let ops: Vec<Operand<'db>> = args.iter().map(|&(l, _)| Operand::Local(l)).collect();
        let result = self.result;
        if let Some(primitive) = self.primitive_of(instance) {
            let op = self.primitive_ops(expr, primitive, result, ops);
            return self.finish_dest(op, result, Dest::Return);
        }
        let Some(func) = self.callable(expr, instance) else {
            return self.finish_dest(self.unit(), result, Dest::Return);
        };
        let sig = self.instance_signature(instance);
        if sig.params.len() != args.len() {
            let op = self.unsupported(expr, "default arguments");
            return self.finish_dest(op, result, Dest::Return);
        }
        let ops: Vec<Operand<'db>> = args
            .iter()
            .zip(&sig.params)
            .map(|(&(l, ty), p)| self.coerce(Operand::Local(l), ty, p.ty))
            .collect();
        let ty = sig.result.unwrap_or_else(|| Ty::unit(db));
        if ty == result {
            self.terminate(Terminator::TailCall {
                func,
                args: ops,
                site: expr,
            });
            return;
        }
        let dst = self.temp(ty);
        let target = self.new_block();
        self.terminate(Terminator::Call {
            func,
            args: ops,
            dst,
            target,
            site: expr,
            unwind: None,
            catch: None,
        });
        self.switch_to(target);
        self.finish_dest(Operand::Local(dst), ty, Dest::Return);
    }

    /// The bindings a closure's environment holds, all it captures but a
    /// local function's own name, and the environment's type.
    pub(super) fn environment(
        &self,
        frame: ExprId,
        own: Option<BindingId>,
    ) -> (Vec<BindingId>, Ty<'db>) {
        let db = self.db;
        let captures: Vec<BindingId> = self
            .types
            .escapes
            .captures
            .iter()
            .find(|(f, _)| *f == frame)
            .map(|(_, c)| c.iter().copied().filter(|&b| Some(b) != own).collect())
            .unwrap_or_default();
        let fields = captures
            .iter()
            .enumerate()
            .map(|(i, &b)| {
                let ty = self.binding_ty(b).unwrap_or_else(|| Ty::error(db));
                (capture_name(db, i), ty)
            })
            .collect();
        (captures, Ty::record(db, fields, false))
    }

    /// The module values a closure literal that becomes an `Expr` reads,
    /// which it captures after its bindings (§18.6).
    pub(super) fn module_captures(&self, frame: ExprId) -> Vec<(ItemId<'db>, ExprId)> {
        match self.types.sent.contains(&frame)
            && matches!(self.body.expr(frame), Expr::Closure { .. })
        {
            true => crag_types::module_values(self.body, frame),
            false => Vec::new(),
        }
    }

    /// The environment with a field for each module value the closure
    /// captures, after its `bound` captured bindings.
    pub(super) fn with_module_values(&self, frame: ExprId, env: Ty<'db>, bound: usize) -> Ty<'db> {
        let values = self.module_captures(frame);
        if values.is_empty() {
            return env;
        }
        let db = self.db;
        let mut fields = fields_of(db, self.program, env).unwrap_or_default();
        for (k, (_, at)) in values.into_iter().enumerate() {
            fields.push((capture_name(db, bound + k), self.ty(at)));
        }
        Ty::record(db, fields, false)
    }

    /// The environment of a closure or function value that becomes an
    /// `Expr`, with its tree's hash and bytes before the captures, which
    /// `e.treeHash` and `e.tree` read (Plan §11.10.13), then the shapes it
    /// travels by and its budget, none (Plan §11.10.9); any other as it
    /// is.
    pub(super) fn with_tree(
        &self,
        expr: ExprId,
        env: Ty<'db>,
        ops: Vec<Operand<'db>>,
    ) -> (Ty<'db>, Vec<Operand<'db>>) {
        let db = self.db;
        if !self.types.sent.contains(&expr) {
            return (env, ops);
        }
        let bytes = Ty::builtin(db, Builtin::Bytes);
        let mut fields = fields_of(db, self.program, env).unwrap_or_default();
        let int = Ty::builtin(db, Builtin::Int);
        fields.push((Name::new(db, TREE_HASH.to_string()), bytes));
        fields.push((Name::new(db, TREE.to_string()), bytes));
        fields.push((Name::new(db, WIRE.to_string()), bytes));
        fields.push((Name::new(db, BUDGET.to_string()), int));
        let env = Ty::record(db, fields, false);
        let tree = |hash| {
            Operand::Const(Constant::Tree {
                owner: self.owner,
                expr,
                hash,
            })
        };
        let hidden = [
            tree(true),
            tree(false),
            Operand::Const(Constant::Wire(env)),
            Operand::Const(Constant::Int(0)),
        ];
        let ops = hidden.into_iter().chain(ops).collect();
        (env, ops)
    }

    pub(super) fn closure_code(&self, frame: ExprId) -> InstanceKey<'db> {
        self.instance.with_entry(self.db, Entry::Closure(frame))
    }

    // Instances.
}
