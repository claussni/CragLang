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

//! Calls: the arguments against the candidates, generic calls with the
//! type arguments inferred, and the plan a resolved call is checked by.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    pub(super) fn call(
        &mut self,
        id: ExprId,
        callee: ExprId,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let body = self.body;
        match body.expr(callee) {
            Expr::Name {
                name,
                local: None,
                item:
                    Some(Resolution::Value {
                        value: None,
                        functions,
                    }),
            } => self.resolve(
                id,
                Some(callee),
                *name,
                functions,
                None,
                None,
                args,
                fields,
                expected,
                None,
            ),
            Expr::Name {
                name,
                local: None,
                item: Some(Resolution::Type(item)),
            } => self.construct(id, callee, *name, *item, None, args, fields, expected),
            Expr::TypeArgs { base, args: targs } => match body.expr(*base) {
                Expr::Name {
                    name,
                    local: None,
                    item: Some(Resolution::Type(item)),
                } => {
                    let targs = self.type_args(callee, Some(*item), targs);
                    let ty = self.construct(
                        id,
                        *base,
                        *name,
                        *item,
                        Some(targs),
                        args,
                        fields,
                        expected,
                    );
                    self.exprs[callee.index()] = self.exprs[base.index()];
                    ty
                }
                Expr::Name {
                    name,
                    local: None,
                    item:
                        Some(Resolution::Value {
                            value: None,
                            functions,
                        }),
                } => {
                    let targs = self.type_args(callee, None, targs);
                    let ty = self.resolve(
                        id,
                        Some(*base),
                        *name,
                        functions,
                        Some(targs),
                        None,
                        args,
                        fields,
                        expected,
                        None,
                    );
                    self.exprs[callee.index()] = self.exprs[base.index()];
                    ty
                }
                _ => {
                    let kind = ErrorKind::Unsupported("type arguments of values");
                    self.error(Site::Expr(callee), kind);
                    self.synth_args(args, fields);
                    self.err_ty()
                }
            },
            _ => {
                let ty = self.synth(callee);
                self.callees.push((id, Callee::Value));
                self.call_value(id, ty, args, fields)
            }
        }
    }

    pub(super) fn synth_args(&mut self, args: &[ExprId], fields: Option<&[FieldArg<'db>]>) {
        for &arg in args {
            self.synth(arg);
        }
        for field in fields.unwrap_or_default() {
            self.synth(field_value(field));
        }
    }

    /// A call of a function value: positional arguments, and named ones
    /// that build its last parameter, a record (§5.6.2). Its parameters
    /// have no names of their own.
    pub(super) fn call_value(
        &mut self,
        id: ExprId,
        ty: Ty<'db>,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Ty<'db> {
        let db = self.db;
        let Some((params, result, _)) = ty.as_fn(db) else {
            if !ty.is_error(db) {
                self.error(Site::Expr(id), ErrorKind::NotCallable { ty });
            }
            self.synth_args(args, fields);
            return self.err_ty();
        };
        if let Some(fields) = fields {
            let record = params.get(args.len()).copied().filter(|&p| {
                params.len() == args.len() + 1 && fields_of(db, self.program, p).is_some()
            });
            if let Some(record) = record {
                for (&arg, &param) in args.iter().zip(params) {
                    self.check(arg, param);
                }
                self.build_record(id, record, fields);
                return result;
            }
            for field in fields {
                let value = field_value(field);
                if let FieldArg::Field { path, .. } = field {
                    let kind = ErrorKind::UnknownParam { name: path[0] };
                    self.error(Site::Expr(value), kind);
                }
                self.synth(value);
            }
        }
        if args.len() != params.len() {
            let kind = ErrorKind::ArgCount {
                expected: params.len(),
                found: args.len(),
            };
            self.error(Site::Expr(id), kind);
        }
        for (i, &arg) in args.iter().enumerate() {
            match params.get(i) {
                Some(&param) => {
                    self.check(arg, param);
                }
                None => {
                    self.synth(arg);
                }
            }
        }
        result
    }

    /// Whether an expression takes its type from the context, so an
    /// argument is typed only once its parameter is known.
    pub(super) fn is_pending(&self, id: ExprId) -> bool {
        match self.body.expr(id) {
            // A string without interpolation may be a conditioned alias's
            // (§3.10.1).
            Expr::Str(parts) => matches!(parts.as_slice(), [crag_hir::StrPart::Text(_)]),
            Expr::Literal(Literal::Int(_) | Literal::Float(_) | Literal::Str(_))
            | Expr::Hole
            | Expr::Closure { .. }
            | Expr::List(_)
            | Expr::Map(_)
            | Expr::Grid(_)
            | Expr::Record(_)
            | Expr::Lazy(_) => true,
            Expr::Range { start, end } => {
                self.is_pending(*start) && end.is_none_or(|end| self.is_pending(end))
            }
            Expr::Name {
                local: None,
                item: Some(Resolution::Type(item)),
                ..
            } => !type_header(self.db, self.program, *item).params.is_empty(),
            // An overloaded or generic function takes the parameter's
            // function type to choose or instantiate (§5.6.1).
            Expr::Name {
                local: None,
                item:
                    Some(Resolution::Value {
                        value: None,
                        functions,
                    }),
                ..
            } => {
                let candidates = self.candidates(functions);
                candidates.len() > 1 || candidates.iter().any(|c| c.kind == CandidateKind::Generic)
            }
            Expr::Call { callee, args, .. } => {
                args.len() == 1
                    && self.is_negation(*callee)
                    && matches!(
                        self.body.expr(args[0]),
                        Expr::Literal(Literal::Int(_) | Literal::Float(_))
                    )
            }
            _ => false,
        }
    }

    pub(super) fn is_negation(&self, callee: ExprId) -> bool {
        matches!(self.body.expr(callee), Expr::Name { name, local: None, .. } if name.text(self.db) == "negate")
    }

    /// Whether a pending argument could take the type `param`.
    fn could_fit(&self, id: ExprId, param: Ty<'db>) -> bool {
        let db = self.db;
        // A literal may stand for a conditioned alias of its type (§3.10.1).
        let members: Vec<Ty<'db>> = param
            .members(db)
            .into_iter()
            .map(|m| crate::relate::unrefined(db, self.program, m))
            .collect();
        let any = |f: &dyn Fn(&TyKind<'db>) -> bool| {
            members.iter().any(|m| m.is_error(db) || f(m.kind(db)))
        };
        let builtin =
            |wanted: &[Builtin]| any(&|k| matches!(k, TyKind::Builtin(b, _) if wanted.contains(b)));
        match self.body.expr(id) {
            Expr::Literal(literal @ (Literal::Int(_) | Literal::Float(_))) => {
                let int = matches!(literal, Literal::Int(_));
                any(&|k| match k {
                    TyKind::Builtin(Builtin::Float | Builtin::Fixed(_), _) => true,
                    TyKind::Builtin(b, _) => int && b.int_range().is_some(),
                    _ => false,
                })
            }
            // A negated literal; any other call is typed on its own.
            Expr::Call { callee, args, .. } if args.len() == 1 && self.is_negation(*callee) => {
                self.could_fit(args[0], param)
            }
            // A construction of a declared type cannot give a builtin one.
            Expr::Call { callee, .. }
                if matches!(
                    self.body.expr(*callee),
                    Expr::Name { item: Some(Resolution::Type(item)), .. }
                        if *item.module(db).path(db) != crag_hir::PRELUDE
                ) =>
            {
                any(&|k| !matches!(k, TyKind::Builtin(..)))
            }
            Expr::Hole => true,
            Expr::Closure { params, .. } => members.iter().any(|m| {
                m.is_error(db) || m.as_fn(db).is_some_and(|(p, ..)| p.len() == params.len())
            }),
            Expr::Str(_) | Expr::Literal(Literal::Str(_)) => builtin(&[Builtin::Str]),
            Expr::Literal(Literal::Bytes(_)) => builtin(&[Builtin::Bytes]),
            Expr::Literal(Literal::CodePoint(_)) => builtin(&[Builtin::CodePoint]),
            // A list literal fits when its items could fit the element
            // type.
            Expr::List(items) => any(&|k| match k {
                TyKind::Builtin(Builtin::List | Builtin::Set, args) => {
                    items.iter().all(|&item| self.could_fit(item, args[0]))
                }
                _ => false,
            }),
            Expr::Map(_) => builtin(&[Builtin::Map]),
            Expr::Grid(_) => {
                let grid = self.grid_item();
                any(&|k| matches!(k, TyKind::Named(i, _) if Some(*i) == grid))
            }
            Expr::Lazy(_) => builtin(&[Builtin::Lazy]),
            Expr::Record(_) => any(&|k| matches!(k, TyKind::Record { .. })),
            Expr::Range { start, end } => {
                let range = if end.is_some() {
                    self.range
                } else {
                    self.range_from
                };
                any(
                    &|k| matches!(k, TyKind::Named(i, args) if Some(*i) == range && self.could_fit(*start, args[0])),
                )
            }
            Expr::Name {
                item: Some(Resolution::Type(item)),
                ..
            } => {
                let identity = type_identity(db, self.program, *item);
                any(&|k| matches!(k, TyKind::Named(i, _) if *i == identity))
            }
            Expr::Name {
                item: Some(Resolution::Value { value: None, .. }),
                ..
            } => members.iter().any(|m| m.is_error(db) || m.is_fn(db)),
            _ => true,
        }
    }

    /// The type a number literal has when nothing else fixes it.
    pub(super) fn default_type(&self, id: ExprId) -> Option<Ty<'db>> {
        match self.body.expr(id) {
            Expr::Literal(Literal::Int(_)) => Some(self.builtin(Builtin::Int)),
            Expr::Literal(Literal::Float(_)) => Some(self.builtin(Builtin::Float)),
            _ => None,
        }
    }

    /// Whether a pending argument takes the type `param` without help of
    /// the context: a literal of its default type (§2.6).
    fn default_fits(&self, id: ExprId, param: Ty<'db>) -> bool {
        let db = self.db;
        match self.body.expr(id) {
            Expr::Literal(Literal::Int(_)) => {
                param.members(db).contains(&self.builtin(Builtin::Int))
            }
            Expr::Literal(Literal::Float(_)) => {
                param.members(db).contains(&self.builtin(Builtin::Float))
            }
            Expr::Call { args, .. } => args.first().is_none_or(|&a| self.default_fits(a, param)),
            // A list literal fits a list whose element its items fit.
            Expr::List(items) => param
                .members(db)
                .into_iter()
                .any(|m| match m.as_builtin(db) {
                    Some((Builtin::List | Builtin::Set, [element])) => {
                        items.iter().all(|&item| self.default_fits(item, *element))
                    }
                    _ => false,
                }),
            Expr::Range { start, .. } => param
                .members(db)
                .into_iter()
                .filter_map(|m| self.range_element(m))
                .any(|element| match self.written_scale(*start) {
                    Some(scale) => fixed_scale(db, element) == Some(scale),
                    None => self.default_fits(*start, element),
                }),
            _ => true,
        }
    }

    /// Resolves a call of one of `functions` (§5.6.1) and checks its
    /// arguments: the candidates that fit, filtered by the success and the
    /// expected type, the most specific of one module (§11.5.4), and of
    /// those the ones the literals' default types fit. A generic function takes its
    /// type arguments from `targs` or infers them (§11.5.3); a slot of the
    /// generic function being checked is a candidate like a function.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn resolve(
        &mut self,
        id: ExprId,
        callee: Option<ExprId>,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        targs: Option<Vec<Ty<'db>>>,
        receiver: Option<Arg<'db>>,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        expected: Option<Ty<'db>>,
        success: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let mut positional: Vec<Arg<'db>> = receiver.into_iter().collect();
        for &arg in args {
            positional.push(if self.is_pending(arg) {
                Arg::Pending(arg)
            } else {
                Arg::Typed(arg, self.synth(arg))
            });
        }
        // Named arguments, typed like positional ones when they name a
        // parameter; spreads and paths only build records.
        let named: Vec<(Name<'db>, Arg<'db>)> = fields
            .unwrap_or_default()
            .iter()
            .filter_map(|f| match f {
                FieldArg::Field { path, value } if path.len() == 1 => Some((path[0], *value)),
                _ => None,
            })
            .map(|(n, v)| (n, Arg::Pending(v)))
            .collect();
        let builds_record = fields.is_some_and(|f| f.len() != named.len());
        let mut candidates = self.candidates(functions);
        if let Some(targs) = &targs {
            self.with_type_args(id, &mut candidates, targs.len());
        }
        let selection = self.select(
            &candidates,
            &positional,
            &named,
            builds_record,
            targs.as_deref(),
            expected,
            success,
        );
        if matches!(selection, Selection::NoneViable)
            && let Some(ty) = self.lift(
                id,
                callee,
                name,
                &candidates,
                &positional,
                fields,
                &named,
                builds_record,
                targs.as_deref(),
                expected,
                success,
            )
        {
            return ty;
        }
        let chosen = match selection {
            Selection::One(i) => Some(i),
            // A lone candidate is checked, to say what is wrong.
            _ if candidates.len() == 1 => Some(0),
            Selection::NoneViable => {
                let args = positional
                    .iter()
                    .map(|&a| match a {
                        Arg::Typed(_, t) | Arg::Receiver(_, t) => t,
                        Arg::Pending(e) => self.synth(e),
                    })
                    .collect();
                if !self.any_error(&positional) && !candidates.is_empty() {
                    self.error(Site::Expr(id), ErrorKind::NoMatch { name, args });
                }
                None
            }
            Selection::Several(several) => {
                let kind = ErrorKind::Ambiguous {
                    name,
                    candidates: several.iter().map(|&i| candidates[i].function).collect(),
                };
                self.error(Site::Expr(id), kind);
                None
            }
        };
        let Some(chosen) = chosen else {
            self.unresolved(&positional, fields);
            return self.err_ty();
        };
        let candidate = candidates.swap_remove(chosen);
        let fields = fields.unwrap_or_default();
        let (params, result) = match candidate.kind {
            CandidateKind::Plain => {
                let function = candidate.function;
                self.apply(
                    id,
                    name,
                    &candidate.params,
                    &positional,
                    fields,
                    &named,
                    builds_record,
                );
                self.callees.push((id, Callee::Function(function)));
                (candidate.params, self.success(id, function))
            }
            CandidateKind::Slot(k) => {
                self.apply(
                    id,
                    name,
                    &candidate.params,
                    &positional,
                    fields,
                    &named,
                    builds_record,
                );
                self.callees.push((id, Callee::Slot(k)));
                let result = self.slots()[k as usize].result;
                (candidate.params, result)
            }
            CandidateKind::Generic => self.generic_call(
                id,
                name,
                &candidate,
                targs,
                positional,
                fields,
                named,
                builds_record,
                expected,
            ),
        };
        if let Some(callee) = callee {
            let params = params.iter().map(|p| p.ty).collect();
            self.exprs[callee.index()] = Some(Ty::new(
                db,
                TyKind::Fn {
                    params,
                    result,
                    pure: false,
                },
            ));
        }
        result
    }

    /// Types the arguments of a call that failed to resolve.
    pub(super) fn unresolved(&mut self, positional: &[Arg<'db>], fields: Option<&[FieldArg<'db>]>) {
        for &arg in positional {
            if let Arg::Pending(e) = arg {
                self.unchecked(e);
            }
        }
        for field in fields.unwrap_or_default() {
            if self.exprs[field_value(field).index()].is_none() {
                self.synth(field_value(field));
            }
        }
    }

    /// A call of a generic function: infers its type arguments from the
    /// typed arguments, the context, and then the arguments that take
    /// their type from the context, checks the arguments, and instantiates
    /// the function where the call is written. Returns the parameters and
    /// the result with the type arguments.
    #[allow(clippy::too_many_arguments)]
    fn generic_call(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        candidate: &Candidate<'db>,
        targs: Option<Vec<Ty<'db>>>,
        mut positional: Vec<Arg<'db>>,
        fields: &[FieldArg<'db>],
        mut named: Vec<(Name<'db>, Arg<'db>)>,
        builds_record: bool,
        expected: Option<Ty<'db>>,
    ) -> (Vec<SigParam<'db>>, Ty<'db>) {
        let db = self.db;
        let program = self.program;
        let function = candidate.function;
        let plan = self.plan(&candidate.params, &positional, &named, builds_record);
        let mut args =
            self.provisional_args(candidate, plan.as_ref(), targs.as_deref(), &positional);
        let result = self.result_of(function);
        if args.iter().any(Option::is_none)
            && let (Some(expected), Some(result)) = (expected, result)
        {
            let mut from_context = args.clone();
            bind(db, program, function, result, expected, &mut from_context);
            for (arg, context) in args.iter_mut().zip(from_context) {
                if arg.is_none() {
                    *arg = context;
                }
            }
        }
        // The arguments that take their type from the context, in order,
        // closures and function names last: a closure gets the parameter
        // types known so far, which a literal argument may give, and gives
        // its result.
        let order = plan.as_ref().map_or(Vec::new(), |plan| match plan {
            Plan::Params(given) => {
                let late = |g: &Option<usize>| {
                    let arg = g.and_then(|g| match g < positional.len() {
                        true => Some(&positional[g]),
                        false => named.get(g - positional.len()).map(|(_, a)| a),
                    });
                    matches!(arg, Some(Arg::Pending(e))
                        if matches!(self.body.expr(*e), Expr::Closure { .. } | Expr::Name { .. }))
                };
                let (early, late): (Vec<_>, Vec<_>) = given
                    .iter()
                    .copied()
                    .enumerate()
                    .partition(|(_, g)| !late(g));
                early.into_iter().chain(late).collect()
            }
            _ => Vec::new(),
        });
        if let Some(Plan::Params(_)) = &plan {
            for (i, g) in order {
                let Some(g) = g else { continue };
                let param = candidate.params[i].ty;
                let unknown = |j: u32| args.get(j as usize).is_some_and(Option::is_none);
                if !mentions(db, param, function, &unknown) {
                    continue;
                }
                let arg = if g < positional.len() {
                    &mut positional[g]
                } else {
                    &mut named[g - positional.len()].1
                };
                let Arg::Pending(e) = *arg else { continue };
                let partial = self.at_args(candidate, &args)[i].ty;
                let ty = match self.body.expr(e) {
                    Expr::Closure { .. } | Expr::Name { .. } => self.infer(e, Some(partial)),
                    _ => self.synth(e),
                };
                bind(db, program, function, param, ty, &mut args);
                *arg = Arg::Typed(e, ty);
            }
        }
        let names = type_param_names(db, program, function);
        let mut uninferred = false;
        for (i, arg) in args.iter_mut().enumerate() {
            if arg.is_none() {
                let name = names.get(i).copied().unwrap_or(name);
                self.error(
                    Site::Expr(id),
                    ErrorKind::UninferredTypeArg { function, name },
                );
                uninferred = true;
                *arg = Some(self.err_ty());
            }
        }
        let args = self.known(&args);
        let params = self.at_args(
            candidate,
            &args.iter().copied().map(Some).collect::<Vec<_>>(),
        );
        self.apply(
            id,
            name,
            &params,
            &positional,
            fields,
            &named,
            builds_record,
        );
        self.mapping_rules(id, function, &args);
        if !uninferred && !args.iter().any(|a| a.is_error(db)) {
            match instantiate(db, program, function, &args, self.call_site()) {
                Ok(instance) => self.callees.push((id, Callee::Instance(instance))),
                Err(fit) => self.error(Site::Expr(id), ErrorKind::Unfit(fit)),
            }
        }
        let result = match result {
            Some(result) => crate::relate::subst(db, program, result, function, &args),
            None => {
                self.missing_success(id, function);
                self.err_ty()
            }
        };
        (params, result)
    }

    /// Types an argument of a call that failed to resolve, without errors
    /// that only follow from that: a closure's parameters stay unknown.
    pub(super) fn unchecked(&mut self, arg: ExprId) {
        let db = self.db;
        match self.body.expr(arg) {
            Expr::Closure { params, .. } => {
                let params = vec![Ty::error(db); params.len()];
                let result = Ty::error(db);
                self.infer(
                    arg,
                    Some(Ty::new(
                        db,
                        TyKind::Fn {
                            params,
                            result,
                            pure: false,
                        },
                    )),
                );
            }
            // A function that only the call's parameter would choose.
            Expr::Name { .. } => self.exprs[arg.index()] = Some(Ty::error(db)),
            _ => {
                self.synth(arg);
            }
        }
    }

    fn any_error(&self, args: &[Arg<'db>]) -> bool {
        args.iter().any(|a| match a {
            Arg::Typed(_, t) | Arg::Receiver(_, t) => t.is_error(self.db),
            Arg::Pending(_) => false,
        })
    }

    /// How the arguments meet a candidate's parameters, if they can.
    pub(super) fn plan(
        &self,
        params: &[SigParam<'db>],
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
    ) -> Option<Plan> {
        if positional.len() > params.len() {
            return None;
        }
        if !builds_record {
            // The named arguments first, then the positional ones.
            let mut given: Vec<Option<usize>> = vec![None; params.len()];
            let mut fits = true;
            for (j, (name, _)) in named.iter().enumerate() {
                match params.iter().position(|p| p.name == Some(*name)) {
                    Some(i) if given[i].is_none() => given[i] = Some(positional.len() + j),
                    _ => fits = false,
                }
            }
            let defaults: Vec<bool> = params.iter().map(|p| p.default).collect();
            let taken: Vec<bool> = given.iter().map(Option::is_some).collect();
            match place_positional(&defaults, &taken, positional.len()) {
                Some(places) => {
                    for (k, i) in places.into_iter().enumerate() {
                        given[i] = Some(k);
                    }
                }
                None => fits = false,
            }
            if fits
                && given
                    .iter()
                    .zip(params)
                    .all(|(g, p)| g.is_some() || p.default)
            {
                return Some(Plan::Params(given));
            }
        }
        let record_param = params.len() == positional.len() + 1
            && (builds_record || !named.is_empty())
            && fields_of(self.db, self.program, params[positional.len()].ty).is_some();
        record_param.then_some(Plan::Record)
    }

    /// Whether every typed argument fits its parameter, and every pending
    /// one could.
    pub(super) fn plan_fits(
        &self,
        params: &[SigParam<'db>],
        plan: &Plan,
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
    ) -> bool {
        let arg_fits = |arg: Arg<'db>, param: Ty<'db>| match arg {
            Arg::Typed(e, t) => self.fits(t, param) || self.sendable(e, t, param),
            Arg::Receiver(_, t) => self.fits(t, param),
            Arg::Pending(e) => self.could_fit(e, param),
        };
        match plan {
            Plan::Params(given) => given.iter().zip(params).all(|(g, p)| match g {
                Some(i) if *i < positional.len() => arg_fits(positional[*i], p.ty),
                Some(i) => arg_fits(named[*i - positional.len()].1, p.ty),
                None => true,
            }),
            Plan::Record => {
                let record = params[positional.len()].ty;
                let fields = fields_of(self.db, self.program, record).unwrap_or_default();
                positional
                    .iter()
                    .zip(params)
                    .all(|(&a, p)| arg_fits(a, p.ty))
                    && named
                        .iter()
                        .all(|(n, a)| fields.iter().any(|(f, t)| f == n && arg_fits(*a, *t)))
            }
        }
    }

    pub(super) fn defaults_fit(&self, params: &[SigParam<'db>], positional: &[Arg<'db>]) -> bool {
        positional.iter().zip(params).all(|(a, p)| match a {
            Arg::Pending(e) => self.default_fits(*e, p.ty),
            _ => true,
        })
    }

    /// Checks the arguments of a call against the chosen function's
    /// parameters.
    #[allow(clippy::too_many_arguments)]
    fn apply(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        params: &[SigParam<'db>],
        positional: &[Arg<'db>],
        fields: &[FieldArg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
    ) {
        let db = self.db;
        let negative = self.negative;
        self.negative = name.text(db) == "negate";
        let plan = self.plan(params, positional, named, builds_record);
        match plan {
            Some(Plan::Params(given)) => {
                for (i, g) in given.iter().enumerate() {
                    let Some(g) = *g else { continue };
                    let arg = if g < positional.len() {
                        positional[g]
                    } else {
                        named[g - positional.len()].1
                    };
                    self.check_arg(arg, params[i].ty);
                }
            }
            Some(Plan::Record) => {
                for (&arg, param) in positional.iter().zip(params) {
                    self.check_arg(arg, param.ty);
                }
                let record = params[positional.len()].ty;
                self.build_record(id, record, fields);
            }
            None => {
                // Only a lone candidate gets here; say what is wrong.
                let mut seen = vec![false; params.len()];
                for (i, &arg) in positional.iter().enumerate() {
                    match params.get(i) {
                        Some(param) => {
                            seen[i] = true;
                            self.check_arg(arg, param.ty);
                        }
                        None => self.check_arg(arg, Ty::error(db)),
                    }
                }
                if positional.len() > params.len() {
                    let kind = ErrorKind::ArgCount {
                        expected: params.len(),
                        found: positional.len(),
                    };
                    self.error(Site::Expr(id), kind);
                }
                for field in fields {
                    let value = field_value(field);
                    let param = match field {
                        FieldArg::Field { path, .. } if path.len() == 1 => {
                            params.iter().position(|p| p.name == Some(path[0]))
                        }
                        _ => None,
                    };
                    match param {
                        Some(i) if !seen[i] => {
                            seen[i] = true;
                            self.check(value, params[i].ty);
                        }
                        _ => {
                            if let FieldArg::Field { path, .. } = field {
                                let kind = ErrorKind::UnknownParam { name: path[0] };
                                self.error(Site::Expr(value), kind);
                            }
                            self.synth(value);
                        }
                    }
                }
                for (i, param) in params.iter().enumerate() {
                    if !seen[i] && !param.default {
                        let kind = match param.name {
                            Some(name) => ErrorKind::MissingArg { name },
                            None => ErrorKind::ArgCount {
                                expected: params.len(),
                                found: positional.len(),
                            },
                        };
                        self.error(Site::Expr(id), kind);
                    }
                }
            }
        }
        self.negative = negative;
    }

    fn check_arg(&mut self, arg: Arg<'db>, param: Ty<'db>) {
        match arg {
            Arg::Pending(e) => {
                self.check(e, param);
            }
            Arg::Typed(e, t) if self.sendable(e, t, param) => {
                let t = self.reference(e, t);
                self.exprs[e.index()] = Some(t);
                self.expect(Site::Expr(e), t, param);
            }
            Arg::Typed(e, t) | Arg::Receiver(e, t) => self.expect(Site::Expr(e), t, param),
        }
    }
}
