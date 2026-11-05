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

//! Closures and trap handlers: the parameters a closure takes, from
//! what the context expects of it, and the holes of its patterns.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    pub(super) fn closure(
        &mut self,
        params: &[crag_hir::ClosureParam],
        root: ExprId,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let wanted = expected.and_then(|e| {
            e.members(db).into_iter().find_map(|m| match m.kind(db) {
                TyKind::Fn {
                    params: p, result, ..
                } if p.len() == params.len() => Some((p.clone(), *result)),
                _ => None,
            })
        });
        let mut param_tys = Vec::new();
        let mut holes = Vec::new();
        for (i, param) in params.iter().enumerate() {
            let from_context = wanted.as_ref().map(|(p, _)| p[i]);
            let ty = match (self.written(param.ty), from_context) {
                (Some(written), Some(context)) => {
                    // The closure must accept what the context passes.
                    if !self.fits(context, written) {
                        let site = Site::Type(param.ty.expect("written"));
                        let kind = ErrorKind::Mismatch {
                            expected: context,
                            found: written,
                        };
                        self.error(site, kind);
                        // Reported once: the closure's type is the
                        // context's.
                        self.pattern(param.pat, written);
                        param_tys.push(context);
                        continue;
                    }
                    written
                }
                (Some(written), None) => written,
                (None, Some(context)) => context,
                // A `_` of a partial application fits whatever the call
                // takes there until the call is resolved (§6.6).
                (None, None) if self.hole_of(param.pat).is_some() => {
                    holes.push(i);
                    Ty::never(db)
                }
                (None, None) => {
                    self.error(Site::Pat(param.pat), ErrorKind::CannotInfer);
                    self.err_ty()
                }
            };
            self.pattern(param.pat, ty);
            param_tys.push(ty);
        }
        let result = wanted.map(|(_, r)| r).filter(|r| !r.is_error(db));
        let inside = self.without_vars();
        let outside = std::mem::replace(&mut self.narrowed, inside);
        let result = self.frame(result, root, false);
        self.narrowed = outside;
        for i in holes {
            let pat = params[i].pat;
            let ty = match self.hole_type(pat) {
                Ok(ty) => ty,
                // The call said what is wrong.
                Err(true) => self.err_ty(),
                Err(false) => {
                    self.error(Site::Pat(pat), ErrorKind::CannotInfer);
                    self.err_ty()
                }
            };
            self.pats[pat.index()] = Some(ty);
            if let Some(binding) = self.hole_of(pat) {
                self.bindings[binding.index()] = Some(ty);
                for (e, expr) in self.body.exprs.iter().enumerate() {
                    if matches!(expr, Expr::Name { local: Some(b), .. } if *b == binding) {
                        self.exprs[e] = Some(ty);
                    }
                }
            }
            param_tys[i] = ty;
        }
        Ty::new(
            db,
            TyKind::Fn {
                params: param_tys,
                result,
                pure: false,
            },
        )
    }

    /// The type a handler takes, if it is a trap's (§8.3.1).
    pub(super) fn trap_type(&mut self, ty: TypeRefId) -> Option<Ty<'db>> {
        let db = self.db;
        prelude_item(db, self.program, "Trap")?;
        let ty = self.lower_type(ty);
        let trap = prelude_type(db, self.program, "Trap");
        (!ty.is_error(db) && self.fits(ty, trap)).then_some(ty)
    }

    /// `on T { t -> … }` for a trap type `T`: the parameter takes the trap,
    /// and the body runs in the function's frame once the block has left
    /// what it was doing, so `return` leaves the function and nothing
    /// narrowed before holds. Gives the body's value.
    pub(super) fn trap_handler(&mut self, handler: ExprId, trap: Ty<'db>) -> Ty<'db> {
        let Expr::Closure { params, body } = self.body.expr(handler) else {
            return self.synth(handler);
        };
        match params.as_slice() {
            [param] => {
                if let Some(written) = self.written(param.ty)
                    && !self.fits(trap, written)
                {
                    let kind = ErrorKind::Mismatch {
                        expected: trap,
                        found: written,
                    };
                    self.error(Site::Pat(param.pat), kind);
                }
                self.pattern(param.pat, trap);
            }
            _ => {
                let kind = ErrorKind::ArgCount {
                    expected: 1,
                    found: params.len(),
                };
                self.error(Site::Expr(handler), kind);
            }
        }
        let inside = self.without_vars();
        let outside = std::mem::replace(&mut self.narrowed, inside);
        let given = self.synth(*body);
        self.narrowed = outside;
        self.exprs[handler.index()] = Some(trap);
        self.trap_handlers.push((handler, trap));
        given
    }

    /// The binding of a `_` of a partial application, if `pat` is one.
    fn hole_of(&self, pat: PatId) -> Option<BindingId> {
        match self.body.pat(pat) {
            Pat::Bind { binding, sub: None }
                if self.body.binding(*binding).kind == BindingKind::Hole =>
            {
                Some(*binding)
            }
            _ => None,
        }
    }

    /// The type of the parameter a `_` fills in the call that resolved:
    /// what the partial application's parameter takes (§6.6). An error
    /// if there is none, `true` when the call reported why.
    fn hole_type(&self, pat: PatId) -> Result<Ty<'db>, bool> {
        let typed = self.hole_param(pat);
        typed.ok_or(false)?.ok_or(true)
    }

    /// The parameter type of the call a `_` is an argument of: None if it
    /// is none's, `Some(None)` if that call did not resolve or fixed no
    /// type there.
    fn hole_param(&self, pat: PatId) -> Option<Option<Ty<'db>>> {
        let binding = self.hole_of(pat)?;
        let body = self.body;
        let used = (0..body.exprs.len() as u32).map(ExprId).find(
            |&e| matches!(body.expr(e), Expr::Name { local: Some(b), .. } if *b == binding),
        )?;
        for call in (0..body.exprs.len() as u32).map(ExprId) {
            let (positional, fields): (Vec<ExprId>, &[FieldArg<'db>]) = match body.expr(call) {
                Expr::Call { args, fields, .. } | Expr::TypedCall { args, fields, .. } => {
                    (args.clone(), fields.as_deref().unwrap_or_default())
                }
                Expr::MethodCall {
                    receiver,
                    args,
                    fields,
                    ..
                } => (
                    std::iter::once(*receiver)
                        .chain(args.iter().copied())
                        .collect(),
                    fields.as_deref().unwrap_or_default(),
                ),
                _ => continue,
            };
            let named: Vec<Name<'db>> = fields
                .iter()
                .filter_map(|f| match f {
                    FieldArg::Field { path, .. } if path.len() == 1 => Some(path[0]),
                    _ => None,
                })
                .collect();
            let at = positional.iter().position(|&a| a == used);
            let by_name = fields.iter().find_map(|f| match f {
                FieldArg::Field { path, value } if *value == used && path.len() == 1 => {
                    Some(path[0])
                }
                _ => None,
            });
            if at.is_none() && by_name.is_none() {
                continue;
            }
            return Some(self.param_at(call, at, by_name, positional.len(), &named));
        }
        None
    }

    /// The type of the parameter that the positional argument `at`, or
    /// the named argument `by_name`, of a resolved call goes to.
    fn param_at(
        &self,
        call: ExprId,
        at: Option<usize>,
        by_name: Option<Name<'db>>,
        positional: usize,
        named: &[Name<'db>],
    ) -> Option<Ty<'db>> {
        let db = self.db;
        let body = self.body;
        let callee = self
            .callees
            .iter()
            .find(|(e, _)| *e == call)
            .map(|(_, c)| c)?;
        let (function, args) = match callee {
            Callee::Function(f) => (*f, Vec::new()),
            Callee::Instance(instance) => (instance.function, instance.args.clone()),
            Callee::Value => {
                let callee_ty = match body.expr(call) {
                    Expr::Call { callee, .. } => self.exprs[callee.index()],
                    _ => None,
                }?;
                let (params, ..) = callee_ty.as_fn(db)?;
                return params.get(at?).copied();
            }
            _ => return None,
        };
        let sig = signature(db, self.program, function);
        let index = match by_name {
            Some(name) => sig.params.iter().position(|p| p.name == Some(name))?,
            None => {
                let defaults: Vec<bool> = sig.params.iter().map(|p| p.default).collect();
                let taken: Vec<bool> = sig
                    .params
                    .iter()
                    .map(|p| p.name.is_some_and(|n| named.contains(&n)))
                    .collect();
                place_positional(&defaults, &taken, positional)?[at?]
            }
        };
        let ty = sig.params[index].ty;
        let ty = if args.is_empty() {
            ty
        } else {
            crate::relate::subst(db, self.program, ty, function, &args)
        };
        (!ty.is_error(db) && !ty.is_never(db)).then_some(ty)
    }

    // Narrowing.
}
