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

//! Choosing among the candidates of a call: lifting a call whose union
//! arguments no candidate takes whole, splitting it by their members,
//! and ranking the viable candidates by specificity.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    /// Union lifting (§4.6.1): a call whose union arguments no candidate
    /// takes as a whole is split by their members, each combination
    /// resolved on its own and the results joined. None when no argument
    /// is split, or when no combination resolves, so that the call's own
    /// error stands.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn lift(
        &mut self,
        id: ExprId,
        callee: Option<ExprId>,
        name: Name<'db>,
        candidates: &[Candidate<'db>],
        positional: &[Arg<'db>],
        fields: Option<&[FieldArg<'db>]>,
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
        targs: Option<&[Ty<'db>]>,
        expected: Option<Ty<'db>>,
        success: Option<Ty<'db>>,
    ) -> Option<Ty<'db>> {
        let db = self.db;
        let split = self.split(
            candidates,
            positional,
            named,
            builds_record,
            targs,
            expected,
            success,
        )?;
        let (args, members, chosen) = match split {
            Ok(split) => split,
            Err(kind) => {
                self.error(Site::Expr(id), kind);
                self.unresolved(positional, fields);
                return Some(self.err_ty());
            }
        };
        // The arguments typed by the context are typed once, so their
        // parameters must agree.
        let mut context: Vec<Option<Ty<'db>>> = vec![None; positional.len() + named.len()];
        let mut differs = false;
        // The record named arguments build, which every arm must take.
        let mut record: Option<Ty<'db>> = None;
        let mut arms = Vec::new();
        for (i, at) in &chosen {
            let Some((callee, params, result)) =
                self.arm(id, &candidates[*i], at, named, builds_record, targs)
            else {
                self.unresolved(positional, fields);
                return Some(self.err_ty());
            };
            let given = match self.plan(&params, at, named, builds_record) {
                Some(Plan::Params(given)) if record.is_none() => given,
                Some(Plan::Record) if arms.is_empty() || record.is_some() => {
                    let ty = params[at.len()].ty;
                    differs |= record.is_some_and(|r| r != ty);
                    record = Some(ty);
                    (0..at.len()).map(Some).collect()
                }
                _ => {
                    let kind = ErrorKind::Unsupported(
                        "lifted calls whose named arguments build a record for some members only",
                    );
                    self.error(Site::Expr(id), kind);
                    self.unresolved(positional, fields);
                    return Some(self.err_ty());
                }
            };
            for (p, g) in given.iter().enumerate() {
                let Some(g) = *g else { continue };
                let arg = if g < at.len() {
                    at[g]
                } else {
                    named[g - at.len()].1
                };
                if let Arg::Pending(_) = arg {
                    match context[g] {
                        None => context[g] = Some(params[p].ty),
                        Some(t) => differs |= t != params[p].ty,
                    }
                }
            }
            arms.push(DispatchArm { callee, result });
        }
        if differs {
            let kind = ErrorKind::Unsupported(
                "lifted calls whose arguments typed by the context differ by member",
            );
            self.error(Site::Expr(id), kind);
            self.unresolved(positional, fields);
            return Some(self.err_ty());
        }
        let negative = self.negative;
        self.negative = name.text(db) == "negate";
        let mut params = Vec::new();
        for (g, ty) in context.iter().enumerate() {
            // Named arguments that build a record are checked as one.
            if g >= positional.len() && record.is_some() {
                break;
            }
            let arg = if g < positional.len() {
                positional[g]
            } else {
                named[g - positional.len()].1
            };
            let ty = match (arg, ty) {
                (Arg::Typed(_, t) | Arg::Receiver(_, t), _) => t,
                (Arg::Pending(e), Some(ty)) => {
                    self.check(e, *ty);
                    *ty
                }
                (Arg::Pending(e), None) => {
                    self.unchecked(e);
                    self.err_ty()
                }
            };
            if g < positional.len() {
                params.push(ty);
            }
        }
        self.negative = negative;
        if let (Some(record), Some(fields)) = (record, fields) {
            self.build_record(id, record, fields);
        }
        let result = self.join_all(arms.iter().map(|a| a.result).collect());
        let dispatch = Dispatch {
            args,
            members,
            arms,
        };
        self.callees.push((id, Callee::Dispatch(dispatch)));
        if let Some(callee) = callee {
            self.exprs[callee.index()] = Some(Ty::new(
                db,
                TyKind::Fn {
                    params,
                    result,
                    pure: false,
                },
            ));
        }
        Some(result)
    }

    /// The split of a lifted call: the positional arguments split, their
    /// members, and for each combination of members the candidate chosen
    /// with the arguments it sees. The union arguments no candidate takes
    /// whole at their position are split first, and all union arguments
    /// if that leaves a combination without a function. None when no
    /// argument is split or no combination resolves; the error when some
    /// combination does not.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn split(
        &self,
        candidates: &[Candidate<'db>],
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
        targs: Option<&[Ty<'db>]>,
        expected: Option<Ty<'db>>,
        success: Option<Ty<'db>>,
    ) -> Option<Result<Lifted<'db>, ErrorKind<'db>>> {
        let split = |all| {
            self.split_by(
                candidates,
                positional,
                named,
                builds_record,
                targs,
                expected,
                success,
                all,
            )
        };
        match split(false) {
            first @ (None | Some(Err(ErrorKind::NoLift { .. }))) => match split(true) {
                Some(Ok(lifted)) => Some(Ok(lifted)),
                _ => first,
            },
            other => other,
        }
    }

    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn split_by(
        &self,
        candidates: &[Candidate<'db>],
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
        targs: Option<&[Ty<'db>]>,
        expected: Option<Ty<'db>>,
        success: Option<Ty<'db>>,
        all: bool,
    ) -> Option<Result<Lifted<'db>, ErrorKind<'db>>> {
        let db = self.db;
        let taken_whole = |k: usize, ty: Ty<'db>| {
            candidates.iter().any(|c| {
                let plan = self.plan(&c.params, positional, named, builds_record);
                let args = self.provisional_args(c, plan.as_ref(), targs, positional);
                let params = self.at_args(c, &args);
                match self.plan(&params, positional, named, builds_record) {
                    Some(Plan::Params(given)) => given
                        .iter()
                        .zip(&params)
                        .any(|(g, p)| *g == Some(k) && self.fits(ty, p.ty)),
                    Some(Plan::Record) => params.get(k).is_some_and(|p| self.fits(ty, p.ty)),
                    None => false,
                }
            })
        };
        let args: Vec<usize> = positional
            .iter()
            .enumerate()
            .filter_map(|(k, a)| match *a {
                Arg::Typed(_, t) | Arg::Receiver(_, t)
                    if t.members(db).len() > 1 && (all || !taken_whole(k, t)) =>
                {
                    Some(k)
                }
                _ => None,
            })
            .collect();
        if args.is_empty() {
            return None;
        }
        let members: Vec<Vec<Ty<'db>>> = args
            .iter()
            .map(|&k| match positional[k] {
                Arg::Typed(_, t) | Arg::Receiver(_, t) => t.members(db),
                Arg::Pending(_) => unreachable!("only typed arguments are split"),
            })
            .collect();
        let mut chosen = Vec::new();
        let mut failure = None;
        let mut indices = vec![0; args.len()];
        loop {
            let mut at = positional.to_vec();
            for ((&k, &i), members) in args.iter().zip(&indices).zip(&members) {
                at[k] = match at[k] {
                    Arg::Receiver(e, _) => Arg::Receiver(e, members[i]),
                    arg => match arg {
                        Arg::Typed(e, _) => Arg::Typed(e, members[i]),
                        pending => pending,
                    },
                };
            }
            let combination = || {
                indices
                    .iter()
                    .zip(&members)
                    .map(|(&i, m)| m[i])
                    .collect::<Vec<_>>()
            };
            match self.select(
                candidates,
                &at,
                named,
                builds_record,
                targs,
                expected,
                success,
            ) {
                Selection::One(i) => chosen.push((i, at)),
                Selection::NoneViable => {
                    failure.get_or_insert(Failure::None(combination()));
                }
                Selection::Several(several) => {
                    let functions = several.iter().map(|&i| candidates[i].function).collect();
                    failure.get_or_insert(Failure::Several(functions));
                }
            }
            // The next combination, the last argument's member fastest.
            let mut level = args.len();
            loop {
                if level == 0 {
                    break;
                }
                level -= 1;
                indices[level] += 1;
                if indices[level] < members[level].len() {
                    break;
                }
                indices[level] = 0;
            }
            if indices.iter().all(|&i| i == 0) {
                break;
            }
        }
        if chosen.is_empty() {
            return None;
        }
        let name = *candidates[0].function.name(db);
        Some(match failure {
            None => Ok((args, members, chosen)),
            Some(Failure::None(members)) => Err(ErrorKind::NoLift { name, members }),
            Some(Failure::Several(candidates)) => Err(ErrorKind::Ambiguous { name, candidates }),
        })
    }

    /// One arm of a lifted call: what the chosen candidate calls, its
    /// parameters and its result. None when it fails, which is reported.
    pub(super) fn arm(
        &mut self,
        id: ExprId,
        candidate: &Candidate<'db>,
        at: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
        targs: Option<&[Ty<'db>]>,
    ) -> Option<(Callee<'db>, Vec<SigParam<'db>>, Ty<'db>)> {
        let db = self.db;
        let function = candidate.function;
        match candidate.kind {
            CandidateKind::Plain => {
                let result = self.success(id, function);
                Some((Callee::Function(function), candidate.params.clone(), result))
            }
            CandidateKind::Slot(k) => {
                let result = self.slots()[k as usize].result;
                Some((Callee::Slot(k), candidate.params.clone(), result))
            }
            CandidateKind::Generic => {
                let plan = self.plan(&candidate.params, at, named, builds_record);
                let args = self.provisional_args(candidate, plan.as_ref(), targs, at);
                let Some(args) = args.into_iter().collect::<Option<Vec<_>>>() else {
                    let kind = ErrorKind::Unsupported(
                        "lifted calls of generic functions whose arguments do not fix their type arguments",
                    );
                    self.error(Site::Expr(id), kind);
                    return None;
                };
                let instance =
                    match instantiate(db, self.program, function, &args, self.call_site()) {
                        Ok(instance) => instance,
                        Err(fit) => {
                            self.error(Site::Expr(id), ErrorKind::Unfit(fit));
                            return None;
                        }
                    };
                let params = self.at_args(
                    candidate,
                    &args.iter().copied().map(Some).collect::<Vec<_>>(),
                );
                let result = self.success(id, function);
                let result = crate::relate::subst(db, self.program, result, function, &args);
                Some((Callee::Instance(instance), params, result))
            }
        }
    }

    /// Which candidate a call resolves to, without reporting anything:
    /// the candidates that fit, filtered by the success and the expected
    /// type, the most specific of one module (§11.5.4), and of those the
    /// ones the literals' default types fit.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn select(
        &self,
        candidates: &[Candidate<'db>],
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
        targs: Option<&[Ty<'db>]>,
        expected: Option<Ty<'db>>,
        success: Option<Ty<'db>>,
    ) -> Selection {
        let db = self.db;
        // What each candidate's parameters are with the type arguments
        // the typed arguments give; those still unknown fit anything.
        let provisional: Vec<Vec<SigParam<'db>>> = candidates
            .iter()
            .map(|c| {
                let plan = self.plan(&c.params, positional, named, builds_record);
                let args = self.provisional_args(c, plan.as_ref(), targs, positional);
                self.at_args(c, &args)
            })
            .collect();
        let mut viable: Vec<usize> = (0..candidates.len())
            .filter(|&i| {
                let params = &provisional[i];
                self.plan(params, positional, named, builds_record)
                    .is_some_and(|p| self.plan_fits(params, &p, positional, named))
                    && self.bounds_hold(&candidates[i], positional, named, builds_record, targs)
            })
            .collect();
        let gives = |this: &Self, i: usize| {
            let c = &candidates[i];
            let args = this.provisional_args(c, None, targs, positional);
            this.candidate_success(c, &args)
        };
        if let Some(success) = success {
            viable.retain(|&i| gives(self, i).is_some_and(|r| self.fits(success, r)));
        }
        if viable.len() > 1
            && let Some(expected) = expected
        {
            let fitting: Vec<_> = viable
                .iter()
                .copied()
                .filter(|&i| gives(self, i).is_some_and(|r| self.fits(r, expected)))
                .collect();
            if !fitting.is_empty() {
                viable = fitting;
            }
        }
        // The most specific of the candidates (§5.6.1); of those left,
        // the ones the literals fit with their default types.
        if viable.len() > 1 {
            let ranked: Vec<Ranked<'db>> = viable
                .iter()
                .map(|&i| self.ranked(&candidates[i], positional, named, builds_record))
                .collect();
            viable = most_specific(db, self.program, &ranked)
                .into_iter()
                .map(|k| viable[k])
                .collect();
        }
        if viable.len() > 1 {
            let defaults: Vec<_> = viable
                .iter()
                .copied()
                .filter(|&i| self.defaults_fit(&provisional[i], positional))
                .collect();
            if !defaults.is_empty() {
                viable = defaults;
            }
        }
        // Overloads that require a marker and its absence are told apart
        // by the literals' default types too (§4.7).
        if viable.len() > 1 {
            let defaulted: Vec<Arg<'db>> = positional
                .iter()
                .map(|&a| match a {
                    Arg::Pending(e) => self.default_type(e).map_or(a, |t| Arg::Typed(e, t)),
                    a => a,
                })
                .collect();
            let holding: Vec<_> = viable
                .iter()
                .copied()
                .filter(|&i| {
                    self.bounds_hold(&candidates[i], &defaulted, named, builds_record, targs)
                })
                .collect();
            if !holding.is_empty() {
                viable = holding;
            }
        }
        match viable.as_slice() {
            [one] => Selection::One(*one),
            [] => Selection::NoneViable,
            several => Selection::Several(several.to_vec()),
        }
    }

    /// Whether a generic candidate's bounds hold for the type arguments
    /// the typed arguments fix, if they fix all; a candidate whose bounds
    /// fail is not viable.
    fn bounds_hold(
        &self,
        candidate: &Candidate<'db>,
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
        targs: Option<&[Ty<'db>]>,
    ) -> bool {
        if candidate.kind != CandidateKind::Generic {
            return true;
        }
        let plan = self.plan(&candidate.params, positional, named, builds_record);
        let args = self.provisional_args(candidate, plan.as_ref(), targs, positional);
        let Some(args) = args.into_iter().collect::<Option<Vec<_>>>() else {
            return true;
        };
        args.iter().any(|a| a.is_error(self.db))
            || instantiate(
                self.db,
                self.program,
                candidate.function,
                &args,
                self.call_site(),
            )
            .is_ok()
    }

    /// A candidate as ranking sees it: the declared type of the parameter
    /// each argument goes to.
    fn ranked(
        &self,
        candidate: &Candidate<'db>,
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
    ) -> Ranked<'db> {
        let mut params = vec![None; positional.len() + named.len()];
        match self.plan(&candidate.params, positional, named, builds_record) {
            Some(Plan::Params(given)) => {
                for (i, g) in given.iter().enumerate() {
                    if let Some(g) = *g {
                        params[g] = Some(candidate.params[i].ty);
                    }
                }
            }
            Some(Plan::Record) => {
                for (k, p) in candidate.params.iter().take(positional.len()).enumerate() {
                    params[k] = Some(p.ty);
                }
            }
            None => {}
        }
        let module = match candidate.kind {
            CandidateKind::Slot(_) => self.module,
            _ => *candidate.function.module(self.db),
        };
        Ranked {
            function: candidate.function,
            module,
            params,
        }
    }

    /// The functions a name may call: declared functions, and the slots
    /// of the generic function being checked, one per bound that requires
    /// the form's function.
    pub(super) fn candidates(&self, functions: &[ItemId<'db>]) -> Vec<Candidate<'db>> {
        let db = self.db;
        let mut candidates = Vec::new();
        for &function in functions {
            if *function.kind(db) == ItemKind::Slot {
                for (k, slot) in self.slots().iter().enumerate() {
                    if slot.function == function {
                        candidates.push(Candidate {
                            function,
                            params: slot.params.clone(),
                            kind: CandidateKind::Slot(k as u32),
                        });
                    }
                }
                continue;
            }
            let sig = signature(db, self.program, function);
            candidates.push(Candidate {
                function,
                params: sig.params.clone(),
                kind: if sig.type_params > 0 {
                    CandidateKind::Generic
                } else {
                    CandidateKind::Plain
                },
            });
        }
        candidates
    }

    /// The rules of the prelude's `check` and `expect` (§8.4): their value
    /// must have errors, and `check`'s successes must not contain `Empty`.
    pub(super) fn mapping_rules(&mut self, id: ExprId, function: ItemId<'db>, args: &[Ty<'db>]) {
        let db = self.db;
        let mapping = function.module(db).path(db) == PRELUDE
            && matches!(function.name(db).text(db).as_str(), "check" | "expect");
        // `update`'s closure gives the ref's type or an error (§9.3).
        if function.module(db).path(db) == PRELUDE
            && function.name(db).text(db) == "update"
            && let [t, r] = args
            && !t.is_error(db)
            && !r.is_error(db)
        {
            let found = self.successes_of(*r);
            if !self.fits(found, *t) {
                let kind = ErrorKind::Mismatch {
                    expected: *t,
                    found,
                };
                self.error(Site::Expr(id), kind);
            }
        }
        let [x] = args else { return };
        if !mapping || x.is_error(db) {
            return;
        }
        if self.errors_of(*x).is_never(db) {
            self.error(Site::Expr(id), ErrorKind::NoErrors { function });
        } else if function.name(db).text(db) == "check"
            && self
                .successes_of(*x)
                .members(db)
                .iter()
                .any(|m| matches!(m.kind(db), TyKind::Named(i, _) if Some(*i) == self.empty))
        {
            self.error(Site::Expr(id), ErrorKind::EmptyMerges);
        }
    }

    /// Keeps the generic candidates that take `count` type arguments, and
    /// says what is wrong when none does.
    pub(super) fn with_type_args(
        &mut self,
        id: ExprId,
        candidates: &mut Vec<Candidate<'db>>,
        count: usize,
    ) {
        let db = self.db;
        let arity = |c: &Candidate<'db>| signature(db, self.program, c.function).type_params;
        let generic: Vec<usize> = candidates
            .iter()
            .filter(|c| c.kind == CandidateKind::Generic)
            .map(arity)
            .collect();
        candidates.retain(|c| c.kind == CandidateKind::Generic && arity(c) == count);
        if candidates.is_empty() {
            let kind = match generic.as_slice() {
                [] => ErrorKind::TypeArgCount {
                    expected: 0,
                    found: count,
                },
                [expected, ..] => ErrorKind::TypeArgCount {
                    expected: *expected,
                    found: count,
                },
            };
            self.error(Site::Expr(id), kind);
        }
    }

    /// The slots of the generic function being checked.
    pub(super) fn slots(&self) -> &'db [Slot<'db>] {
        match self.generic {
            Some(item) => slots(self.db, self.program, item),
            None => &[],
        }
    }

    /// Where the body is written, for the slot fillings of its calls.
    pub(super) fn call_site(&self) -> CallSite<'db> {
        CallSite {
            module: self.module,
            caller: self.generic,
        }
    }

    /// The type arguments of a candidate that the given ones and the typed
    /// arguments fix.
    pub(super) fn provisional_args(
        &self,
        candidate: &Candidate<'db>,
        plan: Option<&Plan>,
        targs: Option<&[Ty<'db>]>,
        positional: &[Arg<'db>],
    ) -> Vec<Option<Ty<'db>>> {
        if candidate.kind != CandidateKind::Generic {
            return Vec::new();
        }
        let function = candidate.function;
        let count = signature(self.db, self.program, function).type_params;
        if let Some(targs) = targs {
            return targs.iter().copied().map(Some).collect();
        }
        let mut args = vec![None; count];
        let Some(Plan::Params(given)) = plan else {
            return args;
        };
        for (i, g) in given.iter().enumerate() {
            if let Some(&(Arg::Typed(_, t) | Arg::Receiver(_, t))) =
                g.and_then(|g| positional.get(g))
            {
                bind(
                    self.db,
                    self.program,
                    function,
                    candidate.params[i].ty,
                    t,
                    &mut args,
                );
            }
        }
        args
    }

    /// A candidate's parameters with type arguments, those unknown taking
    /// the error type, which fits everything.
    pub(super) fn at_args(
        &self,
        candidate: &Candidate<'db>,
        args: &[Option<Ty<'db>>],
    ) -> Vec<SigParam<'db>> {
        if candidate.kind != CandidateKind::Generic {
            return candidate.params.clone();
        }
        let args = self.known(args);
        candidate
            .params
            .iter()
            .map(|p| SigParam {
                ty: crate::relate::subst(self.db, self.program, p.ty, candidate.function, &args),
                ..p.clone()
            })
            .collect()
    }

    pub(super) fn known(&self, args: &[Option<Ty<'db>>]) -> Vec<Ty<'db>> {
        args.iter()
            .map(|a| a.unwrap_or_else(|| self.err_ty()))
            .collect()
    }

    /// What a candidate gives on success, which the return-type filter
    /// compares (§5.6.1).
    fn candidate_success(
        &self,
        candidate: &Candidate<'db>,
        args: &[Option<Ty<'db>>],
    ) -> Option<Ty<'db>> {
        match candidate.kind {
            CandidateKind::Plain => self.success_of(candidate.function),
            CandidateKind::Slot(k) => Some(self.successes_of(self.slots()[k as usize].result)),
            CandidateKind::Generic => {
                let success = self.success_of(candidate.function)?;
                let args = self.known(args);
                Some(crate::relate::subst(
                    self.db,
                    self.program,
                    success,
                    candidate.function,
                    &args,
                ))
            }
        }
    }
}
