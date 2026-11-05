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

//! Values written as they are: literals, names, references, and a
//! function or a type used as a value, with the type arguments given.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    /// The type of a literal, from the context when it gives one (§2.6).
    /// The content of an `embed`'s resource, of its written type: `Bytes`
    /// without one, and `Str` only when it is UTF-8 (§18.4.1). Any other
    /// type needs an `on Embed` handler, which turns the resource into a
    /// value of it, from the content as `Str` when its form says so.
    pub(super) fn embed(&mut self, id: ExprId, expected: Option<Ty<'db>>) -> Ty<'db> {
        let db = self.db;
        let bytes = self.builtin(Builtin::Bytes);
        let Some(expected) = expected else {
            return bytes;
        };
        let handler = crate::handler::lifecycle_handler(db, self.program, expected, "Embed");
        let text = match expected.as_builtin(db) {
            _ if expected.is_error(db) => false,
            Some((Builtin::Bytes, _)) => false,
            Some((Builtin::Str, _)) => true,
            _ => match handler.map(|h| h.form.kind(db)) {
                Some(TyKind::Fn { params, .. }) => {
                    params.first() == Some(&self.builtin(Builtin::Str))
                }
                _ => {
                    self.error(Site::Expr(id), ErrorKind::EmbedHandler { ty: expected });
                    return self.err_ty();
                }
            },
        };
        let content = self
            .embed
            .map(|e| crag_hir::embed_content(db, self.program, e));
        // A resource that cannot be read was reported.
        if text
            && let Some(Ok(content)) = content
            && let Err(e) = std::str::from_utf8(content)
        {
            let at = e.valid_up_to();
            self.error(Site::Expr(id), ErrorKind::NotUtf8 { ty: expected, at });
        }
        expected
    }

    pub(super) fn literal(
        &mut self,
        id: ExprId,
        literal: &Literal,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        if let Some(refined) = self.refined_literal(id, literal, expected) {
            return refined;
        }
        let ty = self.literal_ty(literal, expected);
        if !self.literal_fits(literal, ty) {
            self.error(Site::Expr(id), ErrorKind::Literal { ty });
        }
        ty
    }

    /// A literal where only a conditioned alias of its kind is expected:
    /// of the alias, once its conditions hold for it (§3.10.1).
    pub(super) fn refined_literal(
        &mut self,
        id: ExprId,
        literal: &Literal,
        expected: Option<Ty<'db>>,
    ) -> Option<Ty<'db>> {
        let db = self.db;
        let program = self.program;
        let members = expected?.members(db);
        let plain = self.literal_ty(literal, expected);
        if members.contains(&plain) {
            return None;
        }
        let refined = members.into_iter().find(|&m| {
            let TyKind::Named(item, _) = m.kind(db) else {
                return false;
            };
            matches!(
                crate::type_def(db, program, *item).kind,
                crate::def::TypeDefKind::Refined(_)
            ) && {
                let target = crate::relate::unrefined(db, program, m);
                let ty = self.literal_ty(literal, Some(target));
                ty == target && self.literal_fits(literal, ty)
            }
        })?;
        let TyKind::Named(item, _) = refined.kind(db) else {
            return None;
        };
        let value = crate::refine::known(literal, self.negative)?;
        match crate::refine::verdict(db, program, *item, &value) {
            crate::refine::Verdict::Holds => {}
            crate::refine::Verdict::Fails(condition) => {
                let kind = ErrorKind::ConditionNotMet {
                    alias: refined,
                    condition,
                };
                self.error(Site::Expr(id), kind);
            }
            crate::refine::Verdict::Undecided(condition) => {
                let kind = ErrorKind::ConditionUndecided {
                    alias: refined,
                    condition,
                };
                self.error(Site::Expr(id), kind);
            }
        }
        Some(refined)
    }

    pub(super) fn literal_ty(&self, literal: &Literal, expected: Option<Ty<'db>>) -> Ty<'db> {
        let db = self.db;
        let numeric = |b: Builtin, int: bool| match b {
            Builtin::Float | Builtin::Fixed(_) => true,
            _ => int && b.int_range().is_some(),
        };
        let pick = |int: bool, default: Builtin| {
            let candidates: Vec<Builtin> = expected
                .map(|e| e.members(db))
                .unwrap_or_default()
                .into_iter()
                .filter_map(|m| match m.kind(db) {
                    TyKind::Builtin(b, _) if numeric(*b, int) => Some(*b),
                    _ => None,
                })
                .collect();
            match candidates.as_slice() {
                [one] => *one,
                _ => default,
            }
        };
        match literal {
            Literal::Int(_) => self.builtin(pick(true, Builtin::Int)),
            Literal::Float(_) => self.builtin(pick(false, Builtin::Float)),
            Literal::Str(_) => self.builtin(Builtin::Str),
            Literal::Bytes(_) => self.builtin(Builtin::Bytes),
            Literal::CodePoint(_) => self.builtin(Builtin::CodePoint),
        }
    }

    pub(super) fn literal_fits(&self, literal: &Literal, ty: Ty<'db>) -> bool {
        let Some((builtin, _)) = ty.as_builtin(self.db) else {
            return true;
        };
        let sign = if self.negative { -1 } else { 1 };
        match (literal, builtin) {
            (Literal::Int(n), Builtin::Fixed(scale)) => i128::try_from(*n)
                .ok()
                .and_then(|n| n.checked_mul(10i128.pow(scale)))
                .is_some_and(|n| i64::try_from(sign * n).is_ok()),
            (Literal::Int(_), Builtin::Float) => true,
            (Literal::Int(n), b) => match (b.int_range(), i128::try_from(*n)) {
                (Some((least, greatest)), Ok(n)) => (least..=greatest).contains(&(sign * n)),
                _ => false,
            },
            (Literal::Float(_), Builtin::Float) => true,
            (Literal::Float(text), Builtin::Fixed(scale)) => fixed_fits(text, scale, sign),
            (Literal::Float(_), _) => false,
            _ => true,
        }
    }

    pub(super) fn name(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        local: Option<BindingId>,
        item: &Option<Resolution<'db>>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        if let Some(binding) = local {
            if let Some(ty) = self.narrowed[binding.index()] {
                return ty;
            }
            return match self.bindings[binding.index()] {
                Some(ty) => ty,
                None => {
                    // A local function used before its success type is
                    // known, or a binding whose pattern failed.
                    if self.body.binding(binding).kind == crag_hir::BindingKind::Fn {
                        self.error(Site::Expr(id), ErrorKind::CannotInfer);
                    }
                    self.err_ty()
                }
            };
        }
        match item {
            Some(Resolution::Value {
                value: Some(value), ..
            }) => match value_type(self.db, self.program, *value) {
                Some(ty) => ty,
                None => {
                    self.error(Site::Expr(id), ErrorKind::ValueCycle { value: *value });
                    self.err_ty()
                }
            },
            Some(Resolution::Value {
                value: None,
                functions,
            }) => match self.sent_as(expected, None) {
                Some(f) => self.function_sent(id, name, functions, f),
                None => self.function_value(id, name, functions, None, expected),
            },
            Some(Resolution::Type(item)) => self.type_value(id, name, *item, Vec::new(), expected),
            Some(Resolution::Form(_)) => {
                self.error(Site::Expr(id), ErrorKind::NotAValue { name });
                self.err_ty()
            }
            None => self.err_ty(),
        }
    }

    /// The function type `F` of the `Expr[F]` the context asks for, with
    /// `arity` parameters if given; none when it asks for no `Expr`.
    pub(super) fn sent_as(
        &self,
        expected: Option<Ty<'db>>,
        arity: Option<usize>,
    ) -> Option<Ty<'db>> {
        let db = self.db;
        expected?.members(db).into_iter().find_map(|m| {
            let m = crate::relate::unrefined(db, self.program, m);
            match m.as_builtin(db) {
                Some((Builtin::Expr, &[f]))
                    if f.as_fn(db)
                        .is_some_and(|(p, ..)| arity.is_none_or(|n| p.len() == n)) =>
                {
                    Some(f)
                }
                _ => None,
            }
        })
    }

    /// Whether `id` names a function, typed `ty` before it was known that
    /// `expected` asks for an `Expr` of it, as an argument is.
    pub(super) fn sendable(&self, id: ExprId, ty: Ty<'db>, expected: Ty<'db>) -> bool {
        matches!(ty.kind(self.db), TyKind::Fn { .. })
            && matches!(
                self.body.expr(id),
                Expr::Name {
                    local: None,
                    item: Some(Resolution::Value { value: None, .. }),
                    ..
                }
            )
            && self
                .sent_as(Some(expected), None)
                .is_some_and(|f| self.fits(ty, f))
    }

    /// A named function passed where an `Expr[F]` is expected: a `pub`
    /// one travels as a reference (§18.6).
    fn function_sent(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        f: Ty<'db>,
    ) -> Ty<'db> {
        let ty = self.function_value(id, name, functions, None, Some(f));
        self.reference(id, ty)
    }

    /// The `Expr` of a named function of type `ty`, whose callee `id`
    /// recorded, when it is `pub`.
    pub(super) fn reference(&mut self, id: ExprId, ty: Ty<'db>) -> Ty<'db> {
        let db = self.db;
        let function = self.callees.iter().rev().find_map(|(e, c)| match c {
            _ if *e != id => None,
            Callee::Function(function) => Some(*function),
            Callee::Instance(instance) => Some(instance.function),
            _ => None,
        });
        match function {
            _ if ty.is_error(db) => ty,
            Some(function) if !crate::def::is_public(db, function) => {
                self.error(Site::Expr(id), ErrorKind::PrivateExpr { function });
                self.err_ty()
            }
            Some(_) => {
                self.sent.push(id);
                self.builtin_of(Builtin::Expr, vec![ty])
            }
            None => ty,
        }
    }

    /// The type of a function as a value.
    fn fn_ty(&mut self, id: ExprId, function: ItemId<'db>) -> Ty<'db> {
        let db = self.db;
        let params = signature(db, self.program, function)
            .params
            .iter()
            .map(|p| p.ty)
            .collect();
        let result = self.success(id, function);
        // A function without effects is Pure as a value (§3.14).
        let pure = self.effects_of(function).is_empty();
        Ty::new(
            db,
            TyKind::Fn {
                params,
                result,
                pure,
            },
        )
    }

    /// A closure's type, Pure when its body has no effects and it captures
    /// only Solid values.
    pub(super) fn pure_if_effectless(
        &mut self,
        closure: ExprId,
        ty: Ty<'db>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let TyKind::Fn { params, result, .. } = ty.kind(db) else {
            return ty;
        };
        let effects_of = |f: ItemId<'db>| self.effects_of(f);
        let mut walker = Walker::new(
            db,
            self.program,
            self.body,
            &self.exprs,
            &self.bindings,
            &self.callees,
            &effects_of,
        );
        let mut pure = walker.closure(closure).is_empty();
        // A closure that captures what is not Solid is never Pure, so that
        // every Pure function value is Solid (§3.11). Where it must be, the
        // capture is the error.
        if pure
            && let Some((name, ty, why)) =
                crate::marker::unsolid_capture(db, self.program, self.body, &self.bindings, closure)
        {
            let wanted = expected.map(|e| crate::relate::unrefined(db, self.program, e));
            if wanted.is_some_and(|w| matches!(w.kind(db), TyKind::Fn { pure: true, .. })) {
                self.error(
                    Site::Expr(closure),
                    ErrorKind::PureCapture { name, ty, why },
                );
            } else {
                pure = false;
            }
        }
        Ty::new(
            db,
            TyKind::Fn {
                params: params.clone(),
                result: *result,
                pure,
            },
        )
    }

    /// A call of a function whose success type is unknown. One of a
    /// recursive group is reported once for the group (§11.5.6).
    pub(super) fn missing_success(&mut self, id: ExprId, function: ItemId<'db>) {
        if !group_of(self.db, self.program, function).recursive {
            self.error(Site::Expr(id), ErrorKind::RecursiveSuccess { function });
        }
    }

    pub(super) fn success(&mut self, id: ExprId, function: ItemId<'db>) -> Ty<'db> {
        match self.result_of(function) {
            Some(ty) => ty,
            None => {
                self.missing_success(id, function);
                self.err_ty()
            }
        }
    }

    /// An overloaded name used as a value: the function whose type fits
    /// the expected one, or the only one (§5.6.1). A generic function
    /// takes its type arguments from `targs` or from the expected type.
    pub(super) fn function_value(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        targs: Option<Vec<Ty<'db>>>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let program = self.program;
        let mut candidates = self.candidates(functions);
        if let Some(targs) = &targs {
            self.with_type_args(id, &mut candidates, targs.len());
        }
        // Each candidate's type, if its type arguments are known.
        let typed: Vec<(usize, Ty<'db>, Vec<Ty<'db>>)> = candidates
            .iter()
            .enumerate()
            .filter_map(|(i, c)| {
                let params: Vec<Ty<'db>> = c.params.iter().map(|p| p.ty).collect();
                let result = match c.kind {
                    CandidateKind::Slot(k) => self.slots()[k as usize].result,
                    _ => self.result_of(c.function).unwrap_or_else(|| self.err_ty()),
                };
                let ty = Ty::new(
                    db,
                    TyKind::Fn {
                        params,
                        result,
                        pure: false,
                    },
                );
                if c.kind != CandidateKind::Generic {
                    return Some((i, ty, Vec::new()));
                }
                let args = match &targs {
                    Some(targs) => targs.clone(),
                    None => {
                        let count = signature(db, program, c.function).type_params;
                        let mut args = vec![None; count];
                        for member in expected.into_iter().flat_map(|e| e.members(db)) {
                            if matches!(member.kind(db), TyKind::Fn { .. }) {
                                bind(db, program, c.function, ty, member, &mut args);
                            }
                        }
                        args.into_iter().collect::<Option<Vec<_>>>()?
                    }
                };
                let ty = crate::relate::subst(db, program, ty, c.function, &args);
                Some((i, ty, args))
            })
            .collect();
        let fitting: Vec<&(usize, Ty<'db>, Vec<Ty<'db>>)> = match expected {
            Some(expected) if typed.len() > 1 => typed
                .iter()
                .filter(|(_, ty, _)| self.fits(*ty, expected))
                .collect(),
            _ => typed.iter().collect(),
        };
        if fitting.is_empty()
            && let Some(ty) = self.lift_value(id, &candidates, targs.as_deref(), expected)
        {
            return ty;
        }
        match fitting.as_slice() {
            [(i, ty, args)] => {
                let candidate = &candidates[*i];
                match candidate.kind {
                    CandidateKind::Plain => {
                        let function = candidate.function;
                        self.callees.push((id, Callee::Function(function)));
                        self.fn_ty(id, function)
                    }
                    CandidateKind::Slot(k) => {
                        self.callees.push((id, Callee::Slot(k)));
                        *ty
                    }
                    CandidateKind::Generic => {
                        let function = candidate.function;
                        if self.result_of(function).is_none() {
                            self.missing_success(id, function);
                            return self.err_ty();
                        }
                        match instantiate(db, program, function, args, self.call_site()) {
                            Ok(instance) => self.callees.push((id, Callee::Instance(instance))),
                            Err(fit) => self.error(Site::Expr(id), ErrorKind::Unfit(fit)),
                        }
                        *ty
                    }
                }
            }
            [] => {
                let generic = candidates.iter().find(|c| c.kind == CandidateKind::Generic);
                let kind = match generic {
                    Some(c) if typed.is_empty() => ErrorKind::UninferredTypeArg {
                        function: c.function,
                        name: type_param_names(db, program, c.function)[0],
                    },
                    _ => ErrorKind::NoMatch {
                        name,
                        args: Vec::new(),
                    },
                };
                self.error(Site::Expr(id), kind);
                self.err_ty()
            }
            several => {
                let kind = ErrorKind::Ambiguous {
                    name,
                    candidates: several
                        .iter()
                        .map(|(i, ..)| candidates[*i].function)
                        .collect(),
                };
                self.error(Site::Expr(id), kind);
                self.err_ty()
            }
        }
    }

    /// An overloaded function used as a value whose expected parameters
    /// are unions no candidate takes whole: a function that dispatches on
    /// their members (§4.6.1).
    fn lift_value(
        &mut self,
        id: ExprId,
        candidates: &[Candidate<'db>],
        targs: Option<&[Ty<'db>]>,
        expected: Option<Ty<'db>>,
    ) -> Option<Ty<'db>> {
        let db = self.db;
        let TyKind::Fn { params, result, .. } = expected?.kind(db) else {
            return None;
        };
        let (params, result) = (params.clone(), *result);
        let positional: Vec<Arg<'db>> = params.iter().map(|&p| Arg::Typed(id, p)).collect();
        let wanted = (!result.is_error(db)).then_some(result);
        let split = self.split(candidates, &positional, &[], false, targs, wanted, None)?;
        let (args, members, chosen) = match split {
            Ok(split) => split,
            Err(kind) => {
                self.error(Site::Expr(id), kind);
                return Some(self.err_ty());
            }
        };
        let mut arms = Vec::new();
        for (i, at) in &chosen {
            let Some((callee, _, result)) = self.arm(id, &candidates[*i], at, &[], false, targs)
            else {
                return Some(self.err_ty());
            };
            arms.push(DispatchArm { callee, result });
        }
        let result = self.join_all(arms.iter().map(|a| a.result).collect());
        let dispatch = Dispatch {
            args,
            members,
            arms,
        };
        self.callees.push((id, Callee::Dispatch(dispatch)));
        Some(Ty::new(
            db,
            TyKind::Fn {
                params,
                result,
                pure: false,
            },
        ))
    }

    /// A type named where a value is expected: a tag, whose type
    /// arguments the context may give (§3.6.1), or a unit record, a record
    /// type without fields, which has one value like a tag (§3.3).
    pub(super) fn type_value(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        item: ItemId<'db>,
        args: Vec<Ty<'db>>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let header = type_header(db, self.program, item);
        let identity = type_identity(db, self.program, item);
        let is_value = header.kind == HeaderKind::Nominal
            && match crate::def::type_def(db, self.program, item).kind {
                crate::def::TypeDefKind::Tag => true,
                crate::def::TypeDefKind::Record { .. } => {
                    let args = vec![self.err_ty(); header.params.len()];
                    let ty = Ty::new(db, TyKind::Named(identity, args));
                    fields_of(db, self.program, ty).is_some_and(|f| f.is_empty())
                }
                _ => false,
            };
        if !is_value {
            self.error(Site::Expr(id), ErrorKind::NotAValue { name });
            return self.err_ty();
        }
        if header.params.is_empty() || !args.is_empty() {
            if args.len() != header.params.len() {
                let kind = ErrorKind::TypeArgCount {
                    expected: header.params.len(),
                    found: args.len(),
                };
                self.error(Site::Expr(id), kind);
                return self.err_ty();
            }
            return Ty::new(db, TyKind::Named(identity, args));
        }
        let levels: Vec<Ty<'db>> = expected
            .map(|e| e.members(db))
            .unwrap_or_default()
            .into_iter()
            .filter(|m| matches!(m.kind(db), TyKind::Named(i, _) if *i == identity))
            .collect();
        match levels.as_slice() {
            [one] => *one,
            _ => {
                self.error(Site::Expr(id), ErrorKind::CannotInfer);
                self.err_ty()
            }
        }
    }

    /// The type arguments written at `id` for `item`, each a type: a
    /// number of digits is one only of `Fixed`, whose conversions are
    /// left to the call, and an `is` clause none of a value.
    pub(super) fn type_args(
        &mut self,
        id: ExprId,
        item: Option<ItemId<'db>>,
        args: &[TypeArg],
    ) -> Vec<Ty<'db>> {
        let fixed = item.is_some_and(|item| {
            matches!(
                type_header(self.db, self.program, item).kind,
                HeaderKind::Builtin(Builtin::Fixed(_))
            )
        });
        args.iter()
            .map(|arg| match arg {
                TypeArg::Type(t) => self.lower_type(*t),
                TypeArg::Int(_) if fixed => Ty::error(self.db),
                TypeArg::Int(_) | TypeArg::Is(_) => {
                    self.error(Site::Expr(id), ErrorKind::TypeArgKind);
                    Ty::error(self.db)
                }
            })
            .collect()
    }

    // Calls.
}
