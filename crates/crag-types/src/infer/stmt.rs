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

//! Statements: bindings, assignments, ranges and the loops over them,
//! and local functions.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    /// Checks a statement; `Never` when it leaves the block.
    pub(super) fn stmt(&mut self, stmt: &Stmt) -> Ty<'db> {
        let db = self.db;
        let unit = Ty::unit(db);
        match stmt {
            Stmt::Expr(e) => self.synth(*e),
            Stmt::Let { pat, ty, value } => {
                let ty = match self.written(*ty) {
                    Some(ty) => {
                        let found = self.check(*value, ty);
                        if found.is_never(db) {
                            return found;
                        }
                        ty
                    }
                    None => self.synth(*value),
                };
                if self.pattern_checks(*pat, ty) {
                    self.irrefutable(*pat, ty);
                }
                if ty.is_never(db) { ty } else { unit }
            }
            Stmt::LetElse {
                pat,
                ty,
                value,
                rest,
                otherwise,
            } => {
                let value_ty = self.synth(*value);
                let written = self.written(*ty);
                let target = written.unwrap_or(value_ty);
                if let Some(written) = written
                    && !value_ty.is_error(db)
                    && !written.is_error(db)
                    && self.refine(value_ty, written).is_none()
                {
                    let kind = ErrorKind::NeverMatches {
                        pattern: written,
                        subject: value_ty,
                    };
                    self.error(Site::Type(ty.expect("written")), kind);
                }
                let typed = self.pattern_checks(*pat, target);
                let binding = self.narrowable(*value).filter(|_| typed);
                let start = self.narrowed.clone();
                // The `else` part sees the values the pattern misses.
                let unmatched = match self.lowered(*pat).filter(|_| typed) {
                    Some(patterns) => {
                        let mut matrix = PatternMatrix::default();
                        for pattern in patterns {
                            matrix.push(pattern);
                        }
                        let tested = self.rest(value_ty, target);
                        let missed = self.unmatched(&matrix, target);
                        self.join(tested, missed)
                    }
                    None => value_ty,
                };
                if let Some(binding) = binding {
                    self.narrowed[binding.index()] = Some(unmatched);
                }
                if let Some(rest) = rest {
                    self.pattern(*rest, unmatched);
                }
                let leaves = self.synth(*otherwise);
                if !leaves.is_never(db) && !leaves.is_error(db) {
                    self.error(Site::Expr(*otherwise), ErrorKind::MustLeave);
                }
                self.narrowed = start;
                if let Some(binding) = binding
                    && let Some(matched) = self.pats[pat.index()]
                    && let Some(matched) = self.refine(value_ty, matched)
                {
                    self.narrowed[binding.index()] = Some(matched);
                }
                unit
            }
            Stmt::Bind {
                binding,
                ty,
                value,
                otherwise,
            } => {
                if self.body.binding(*binding).kind == BindingKind::Dur {
                    return self.dur_bind(*binding, *ty, *value, otherwise);
                }
                let ty = match self.written(*ty) {
                    Some(ty) => {
                        self.check(*value, ty);
                        ty
                    }
                    None => self.synth(*value),
                };
                // A `ref` or `ext` binding is the cell, not its value
                // (§9.1, §9.6).
                let ty = match self.body.binding(*binding).kind {
                    BindingKind::Ref => self.builtin_of(Builtin::Ref, vec![ty]),
                    BindingKind::Ext => self.builtin_of(Builtin::Ext, vec![ty]),
                    _ => ty,
                };
                self.bindings[binding.index()] = Some(ty);
                unit
            }
            Stmt::Assign { binding, value } => {
                let ty = self.bindings[binding.index()].unwrap_or_else(|| Ty::error(db));
                self.check(*value, ty);
                // A `var` is narrowed until it is reassigned (§7.1).
                self.narrowed[binding.index()] = None;
                unit
            }
            Stmt::For {
                pat,
                iterable,
                body,
            } => {
                let element = self.iterable(*iterable);
                if self.pattern_checks(*pat, element) {
                    self.irrefutable(*pat, element);
                }
                // The body may run again after what it assigns.
                for binding in self.body.assigned_in(*body) {
                    self.narrowed[binding.index()] = None;
                }
                let before = self.narrowed.clone();
                let ty = self.synth(*body);
                let after = std::mem::take(&mut self.narrowed);
                self.meet(vec![(unit, before), (ty, after)]);
                unit
            }
            // A signal spreads the prelude's `Signal` (§11.1).
            Stmt::Emit { value, .. } => {
                // A trap handler passes its trap on (§8.3.1).
                let trap = prelude_item(db, self.program, "Trap")
                    .map(|_| prelude_type(db, self.program, "Trap"));
                if let Some(trap) = trap
                    && let Expr::Name { local: Some(_), .. } = self.body.expr(*value)
                {
                    let found = self.synth(*value);
                    // Passed on, it leaves the handler.
                    if self.fits(found, trap) {
                        return Ty::never(db);
                    }
                    let signal = prelude_type(db, self.program, "Signal");
                    self.expect(Site::Expr(*value), found, signal);
                    return unit;
                }
                if prelude_item(db, self.program, "Signal").is_some() {
                    let signal = prelude_type(db, self.program, "Signal");
                    self.check(*value, signal);
                } else {
                    self.synth(*value);
                }
                unit
            }
            Stmt::Return(value) => {
                let expected = self.frames.last().and_then(|f| f.expected);
                let (ty, site) = match value {
                    Some(value) => (self.infer(*value, expected), Site::Expr(*value)),
                    // A bare `return` gives `()`.
                    None => (unit, self.frame_site()),
                };
                self.result_value(site, ty);
                Ty::never(db)
            }
            // A signal handler: a function of the signal (§11.3). Trap
            // handlers (§8.3.1) come later.
            Stmt::On { ty, handler } => {
                let signal = self.lower_type(*ty);
                let is_signal = prelude_item(db, self.program, "Signal").is_some()
                    && self.fits(signal, prelude_type(db, self.program, "Signal"));
                if !is_signal {
                    self.error(
                        Site::Expr(*handler),
                        ErrorKind::Unsupported("`on` handlers of what is not a signal"),
                    );
                    self.synth(*handler);
                    return unit;
                }
                let expected = Ty::new(
                    db,
                    TyKind::Fn {
                        params: vec![signal],
                        result: unit,
                        pure: false,
                    },
                );
                self.check(*handler, expected);
                unit
            }
            Stmt::Fn { binding, function } => {
                self.local_fn(*binding, function);
                unit
            }
        }
    }

    /// A `dur` binding (§21.2): the annotation names the slot's value
    /// type `T`, the right-hand side is checked against
    /// `Slot[T] | StoreError`, and the `else` part receives what is not
    /// the `Slot[T]` member and must leave, as in `let … else` (§7.1.1).
    /// Without `else`, the right-hand side must be exactly `Slot[T]`.
    /// The binding is the cell, of type `Dur[T]`.
    fn dur_bind(
        &mut self,
        binding: BindingId,
        ty: Option<TypeRefId>,
        value: ExprId,
        otherwise: &Option<(Option<PatId>, ExprId)>,
    ) -> Ty<'db> {
        let db = self.db;
        let unit = Ty::unit(db);
        // The annotation is required: it is the schema of the slot.
        let Some(inner) = self.written(ty) else {
            self.error(Site::Binding(binding), ErrorKind::DurNeedsType);
            self.synth(value);
            let err = Ty::error(db);
            if let Some((rest, otherwise)) = otherwise {
                let start = self.narrowed.clone();
                if let Some(rest) = rest {
                    self.pattern(*rest, err);
                }
                let leaves = self.synth(*otherwise);
                if !leaves.is_never(db) && !leaves.is_error(db) {
                    self.error(Site::Expr(*otherwise), ErrorKind::MustLeave);
                }
                self.narrowed = start;
            }
            self.bindings[binding.index()] = Some(self.builtin_of(Builtin::Dur, vec![err]));
            return unit;
        };
        let slot = self.builtin_of(Builtin::Slot, vec![inner]);
        let store_error = prelude_item(db, self.program, "StoreError")
            .map(|_| prelude_type(db, self.program, "StoreError"));
        match otherwise {
            None => {
                // Without `else`, the initializer's type must have no
                // other members.
                self.check(value, slot);
            }
            Some((rest, otherwise)) => {
                let expected = match store_error {
                    Some(error) => self.join(slot, error),
                    None => slot,
                };
                let value_ty = self.check(value, expected);
                if !value_ty.is_error(db) && self.refine(value_ty, slot).is_none() {
                    let kind = ErrorKind::NeverMatches {
                        pattern: slot,
                        subject: value_ty,
                    };
                    self.error(Site::Expr(value), kind);
                }
                // The `else` part sees the members the slot is not.
                let unmatched = self.rest(value_ty, slot);
                let start = self.narrowed.clone();
                if let Some(rest) = rest {
                    self.pattern(*rest, unmatched);
                }
                let leaves = self.synth(*otherwise);
                if !leaves.is_never(db) && !leaves.is_error(db) {
                    self.error(Site::Expr(*otherwise), ErrorKind::MustLeave);
                }
                self.narrowed = start;
            }
        }
        self.bindings[binding.index()] = Some(self.builtin_of(Builtin::Dur, vec![inner]));
        unit
    }

    fn frame_site(&self) -> Site {
        Site::Expr(self.body.root.unwrap_or(ExprId(0)))
    }

    /// `a..b` or `a..` (§7.4): a `Range[T]` or `RangeFrom[T]` whose ends
    /// have the same discrete type `T`.
    pub(super) fn range(
        &mut self,
        id: ExprId,
        start: ExprId,
        end: Option<ExprId>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let element = expected
            .into_iter()
            .flat_map(|e| e.members(db))
            .find_map(|m| self.range_element(m));
        let element = match (element, end) {
            (Some(element), _) => {
                self.range_end(start, element);
                if let Some(end) = end {
                    self.range_end(end, element);
                }
                element
            }
            // `1..n` takes the type of `n`, if it is discrete.
            (None, Some(end)) if self.is_pending(start) && !self.is_pending(end) => {
                let end_ty = self.synth(end);
                if self.is_discrete(end_ty) {
                    self.range_end(start, end_ty);
                    end_ty
                } else {
                    let element = self.synth(start);
                    self.expect(Site::Expr(end), end_ty, element);
                    element
                }
            }
            (None, _) => {
                let element = match self.written_scale(start) {
                    Some(scale) => {
                        let element = self.builtin(Builtin::Fixed(scale));
                        self.check(start, element);
                        element
                    }
                    None => self.synth(start),
                };
                if let Some(end) = end {
                    self.range_end(end, element);
                }
                element
            }
        };
        if !self.is_discrete(element) {
            self.error(Site::Expr(id), ErrorKind::NotDiscrete { ty: element });
            return self.err_ty();
        }
        let scale = fixed_scale(db, element);
        if let Some(end) = end
            && let (Some(lo), Some(hi)) = (
                self.constant_expr(start, scale),
                self.constant_expr(end, scale),
            )
            && lo > hi
        {
            self.error(Site::Expr(id), ErrorKind::Decreasing);
        }
        let range = if end.is_some() {
            self.range
        } else {
            self.range_from
        };
        match range {
            Some(range) => Ty::new(db, TyKind::Named(range, vec![element])),
            None => self.err_ty(),
        }
    }

    /// Checks a range end against the element type. A decimal literal
    /// end of a `Fixed` range has exactly the scale it is written with,
    /// so `0.0..2.00` mixes `Fixed[1]` and `Fixed[2]` (§7.4).
    fn range_end(&mut self, end: ExprId, element: Ty<'db>) {
        match self.written_scale(end) {
            Some(scale) if fixed_scale(self.db, element).is_some() => {
                let written = self.builtin(Builtin::Fixed(scale));
                self.check(end, written);
                self.expect(Site::Expr(end), written, element);
            }
            _ => {
                self.check(end, element);
            }
        }
    }

    /// The number of decimals of a decimal literal, possibly negated:
    /// `2` for `0.50`.
    pub(super) fn written_scale(&self, id: ExprId) -> Option<u32> {
        match self.body.expr(id) {
            Expr::Literal(Literal::Float(text)) => decimals(text),
            Expr::Call { callee, args, .. } if args.len() == 1 && self.is_negation(*callee) => {
                self.written_scale(args[0])
            }
            _ => None,
        }
    }

    /// The `T` of a `Range[T]` or `RangeFrom[T]`.
    pub(super) fn range_element(&self, ty: Ty<'db>) -> Option<Ty<'db>> {
        match ty.kind(self.db) {
            TyKind::Named(item, args)
                if args.len() == 1 && [self.range, self.range_from].contains(&Some(*item)) =>
            {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// Whether `ty` fits `Discrete` (§7.4): the built-in integers and
    /// `CodePoint`, `Fixed`, and types with a `compare` and a `next` in
    /// scope.
    /// Type parameters pass; their bounds are checked with M2.
    pub(super) fn is_discrete(&self, ty: Ty<'db>) -> bool {
        let db = self.db;
        match ty.kind(db) {
            TyKind::Error | TyKind::Param(..) => true,
            TyKind::Builtin(b, _) => {
                b.int_range().is_some() || matches!(b, Builtin::CodePoint | Builtin::Fixed(_))
            }
            TyKind::Named(..) => {
                let ordering = prelude_type(db, self.program, "Ordering");
                self.has_function("compare", &[ty, ty], ordering)
                    && self.has_function("next", &[ty], ty)
            }
            _ => false,
        }
    }

    /// Whether a function `name` in the body's scope that is not generic
    /// takes `params` and returns a `result`.
    fn has_function(&self, name: &str, params: &[Ty<'db>], result: Ty<'db>) -> bool {
        let db = self.db;
        let scope = module_scope(db, self.program, self.module);
        let Some(Resolution::Value { functions, .. }) =
            scope.resolve(Name::new(db, name.to_string()))
        else {
            return false;
        };
        functions.iter().any(|&function| {
            let sig = signature(db, self.program, function);
            sig.type_params == 0
                && sig.params.len() == params.len()
                && params
                    .iter()
                    .zip(&sig.params)
                    .all(|(&p, s)| self.fits(p, s.ty))
                && self
                    .result_of(function)
                    .is_some_and(|r| self.fits(r, result))
        })
    }

    /// The value of a range end written as a literal, possibly negated,
    /// counted in units of the scale of a `Fixed` range.
    fn constant_expr(&self, id: ExprId, scale: Option<u32>) -> Option<i128> {
        match self.body.expr(id) {
            Expr::Literal(literal) => {
                let n = constant(literal, scale)?;
                Some(if self.body.is_negative(id) { -n } else { n })
            }
            Expr::Call { callee, args, .. } if args.len() == 1 && self.is_negation(*callee) => {
                self.constant_expr(args[0], scale).map(|n| -n)
            }
            _ => None,
        }
    }

    /// The element type of what `for` iterates (§7.3): also of a source of a
    /// stream (§10.5).
    fn iterable(&mut self, iterable: ExprId) -> Ty<'db> {
        let db = self.db;
        let ty = self.synth(iterable);
        if let Some(element) = self.range_element(ty) {
            let known = match element.kind(db) {
                TyKind::Builtin(b, _) => {
                    b.int_range().is_some() || matches!(b, Builtin::CodePoint | Builtin::Fixed(_))
                }
                // A type parameter's range is walked by the instance.
                TyKind::Param(..) => true,
                _ => element.is_error(db),
            };
            if !known {
                // The range steps with the type's own `next` (§7.4).
                let ordering = prelude_type(db, self.program, "Ordering");
                let at = self.call_site();
                let next = function_at(db, self.program, "next", &[element], element, at);
                let compare = function_at(
                    db,
                    self.program,
                    "compare",
                    &[element, element],
                    ordering,
                    at,
                );
                match (next, compare) {
                    (Some(next), Some(compare)) => self
                        .iterations
                        .push((iterable, Iteration::Stepped { next, compare })),
                    _ => self.error(Site::Expr(iterable), ErrorKind::NotIterable { ty }),
                }
            }
            return element;
        }
        let listed = |this: &mut Self, element: Ty<'db>| {
            let list = this.builtin_of(Builtin::List, vec![element]);
            let name = if matches!(ty.as_builtin(db), Some((Builtin::Map, _))) {
                "entries"
            } else {
                "toList"
            };
            match function_at(db, this.program, name, &[ty], list, this.call_site()) {
                Some(f) => this.iterations.push((iterable, Iteration::Listed(f))),
                None => this.error(Site::Expr(iterable), ErrorKind::NotIterable { ty }),
            }
            element
        };
        match ty.kind(db) {
            TyKind::Builtin(Builtin::List, args) => args[0],
            // A grid's cells, row by row (§12.3).
            TyKind::Named(item, args) if Some(*item) == self.grid_item() => listed(self, args[0]),
            TyKind::Builtin(Builtin::Set, args) => listed(self, args[0]),
            TyKind::Builtin(Builtin::Map, args) => {
                let key = Name::new(db, "key".to_string());
                let value = Name::new(db, "value".to_string());
                let entry = Ty::record(db, vec![(key, args[0]), (value, args[1])], false);
                listed(self, entry)
            }
            // Every source of a stream fits `Iterable` (§10.5).
            TyKind::Named(item, args) if is_source(db, *item) => args[0],
            TyKind::Error => ty,
            _ => {
                self.error(Site::Expr(iterable), ErrorKind::NotIterable { ty });
                self.err_ty()
            }
        }
    }

    /// A local function (§5.6.4). With a written success type it may call
    /// itself; without one its type is known only after its body.
    fn local_fn(&mut self, binding: BindingId, function: &LocalFn) {
        let db = self.db;
        if function.generic {
            let kind = ErrorKind::GenericLocalFn;
            self.error(Site::Binding(binding), kind);
        }
        let mut params = Vec::new();
        for param in &function.params {
            let ty = self.lower_type(param.ty);
            self.bindings[param.binding.index()] = Some(ty);
            params.push(ty);
        }
        for param in &function.params {
            if let Some(default) = param.default {
                let ty = self.bindings[param.binding.index()].expect("set above");
                self.check(default, ty);
            }
        }
        let expected = self.written(function.result);
        if let Some(result) = expected {
            let ty = Ty::new(
                db,
                TyKind::Fn {
                    params: params.clone(),
                    result,
                    pure: false,
                },
            );
            self.bindings[binding.index()] = Some(ty);
        }
        let inside = self.without_vars();
        let outside = std::mem::replace(&mut self.narrowed, inside);
        let result = match function.body {
            Some(root) => self.frame(expected, root, false),
            None => expected.unwrap_or_else(|| Ty::error(db)),
        };
        self.narrowed = outside;
        self.bindings[binding.index()] = Some(Ty::new(
            db,
            TyKind::Fn {
                params,
                result,
                pure: false,
            },
        ));
    }

    // Patterns.
}
