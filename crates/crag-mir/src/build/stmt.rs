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

//! Statements and loops: bindings with their patterns, assignments, and
//! `for` over a range, a list or a source.

use super::*;

impl<'a, 'db> MirBuilder<'a, 'db> {
    /// A step where the debugger may stop before what starts at `at`, with
    /// every named local made so far; liveness keeps those that hold
    /// values there.
    pub(super) fn step(&mut self, at: Option<ExprId>) {
        let locals = (0..self.locals.len())
            .filter(|&i| self.locals[i].binding.is_some())
            .map(|i| Local(i as u32))
            .collect();
        self.push(Statement::Step { at, locals });
    }

    pub(super) fn stmt(&mut self, stmt: &Stmt) {
        let body = self.body;
        let at = match stmt {
            Stmt::Expr(e)
            | Stmt::Let { value: e, .. }
            | Stmt::LetElse { value: e, .. }
            | Stmt::Bind { value: e, .. }
            | Stmt::Assign { value: e, .. }
            | Stmt::For { iterable: e, .. }
            | Stmt::Return(Some(e))
            | Stmt::Emit { value: e, .. }
            | Stmt::On { handler: e, .. } => Some(Some(*e)),
            Stmt::Return(None) => Some(None),
            Stmt::Fn { .. } => None,
        };
        if let Some(at) = at {
            self.step(at);
        }
        match stmt {
            Stmt::Expr(e) => self.eval(*e, Dest::Discard),
            Stmt::Let { pat, value, .. } => {
                let op = self.expr(*value);
                self.matched(*pat, op, self.ty(*value), None);
            }
            Stmt::LetElse {
                pat,
                ty,
                value,
                rest,
                otherwise,
            } => {
                let test = ty.map(|t| self.type_ref(t));
                let op = self.expr(*value);
                let otherwise = Otherwise {
                    rest: *rest,
                    body: *otherwise,
                };
                match test {
                    Some(None) => {
                        self.trap(TrapKind::Error, Some(*value));
                    }
                    Some(Some(test)) => self.tested(*pat, op, self.ty(*value), test, otherwise),
                    None => self.matched(*pat, op, self.ty(*value), Some(otherwise)),
                }
            }
            Stmt::Bind { binding, value, .. } => {
                let local = self.binding(*binding);
                match body.binding(*binding).kind {
                    BindingKind::Var if self.celled(*binding) => {
                        let ty = self.types.binding(*binding).map(|t| self.subst(t));
                        let ty = ty.unwrap_or_else(|| Ty::error(self.db));
                        let op = self.expr(*value);
                        let op = self.coerce(op, self.ty(*value), ty);
                        let new = Rvalue::Intrinsic(Intrinsic::RefNew, vec![op]);
                        self.push(Statement::Assign(local, new));
                    }
                    BindingKind::Var => {
                        let op = self.expr(*value);
                        self.assign_to(local, op, self.ty(*value));
                    }
                    kind @ (BindingKind::Ref | BindingKind::Ext) => {
                        let cell = self.locals[local.index()].ty;
                        let Some((Builtin::Ref | Builtin::Ext, &[ty])) = cell.as_builtin(self.db)
                        else {
                            self.trap(TrapKind::Error, Some(*value));
                            return;
                        };
                        let op = self.expr(*value);
                        let op = self.coerce(op, self.ty(*value), ty);
                        let new = match kind {
                            BindingKind::Ref => Intrinsic::RefNew,
                            _ => Intrinsic::ExtNew,
                        };
                        self.push(Statement::Assign(local, Rvalue::Intrinsic(new, vec![op])));
                    }
                    // A `dur` binding runs once the slot table of the
                    // Implementation Plan §11.11.7 wires the `rt_store_*`
                    // entry points; until then it traps.
                    BindingKind::Dur => {
                        self.expr(*value);
                        self.trap(TrapKind::Error, Some(*value));
                    }
                    _ => {
                        self.trap(TrapKind::Error, Some(*value));
                    }
                }
            }
            Stmt::Assign { binding, value } if self.celled(*binding) => {
                let cell = self.binding(*binding);
                let ty = self.types.binding(*binding).map(|t| self.subst(t));
                let ty = ty.unwrap_or_else(|| Ty::error(self.db));
                let op = self.expr(*value);
                let new = self.coerce(op, self.ty(*value), ty);
                let swap = Rvalue::Intrinsic(Intrinsic::RefSwap, vec![Operand::Local(cell), new]);
                self.assign(ty, swap);
                self.leave_on_conflict();
            }
            Stmt::Assign { binding, value } => {
                let local = self.binding(*binding);
                let op = self.expr(*value);
                self.assign_to(local, op, self.ty(*value));
            }
            Stmt::For {
                pat,
                iterable,
                body,
            } => {
                self.loops += 1;
                self.for_loop(*pat, *iterable, *body);
                self.loops -= 1;
            }
            Stmt::Return(Some(e)) => self.eval(*e, Dest::Return),
            Stmt::Return(None) => {
                let unit = Ty::unit(self.db);
                self.finish_dest(self.unit(), unit, Dest::Return);
            }
            // A trap handler passes its trap on (§8.3.1).
            Stmt::Emit { value, .. } if self.is_trap(self.ty(*value)) => {
                self.terminate(Terminator::Trap {
                    kind: TrapKind::Rethrow,
                    site: None,
                    detail: None,
                    catch: None,
                });
            }
            Stmt::Emit { kind, value } => {
                let qualifier = match kind {
                    None => qualifier::PLAIN,
                    Some(EmitKind::Ok) => qualifier::OK,
                    Some(EmitKind::Fail) => qualifier::FAIL,
                    Some(EmitKind::Retry) => qualifier::RETRY,
                };
                let op = self.expr(*value);
                let op = self.typed(op, self.ty(*value));
                let unit = Ty::unit(self.db);
                self.assign(
                    unit,
                    Rvalue::Intrinsic(Intrinsic::SignalEmit { qualifier }, vec![op]),
                );
            }
            Stmt::On { handler, .. } => {
                let f = self.expr(*handler);
                let f_ty = self.ty(*handler);
                let f = Operand::Local(self.materialize(f, f_ty));
                let Some(block) = self.handlers.last_mut() else {
                    self.trap(TrapKind::Error, Some(*handler));
                    return;
                };
                block.closures.push(f.clone());
                let mark = block.mark.clone();
                let unit = Ty::unit(self.db);
                self.assign(unit, Rvalue::Intrinsic(Intrinsic::SignalOn, vec![f, mark]));
            }
            Stmt::Fn { binding, function } => {
                let Some(root) = function.body else {
                    return;
                };
                if function.generic {
                    self.unsupported(root, "generic local functions");
                    return;
                }
                let ty = self
                    .types
                    .binding(*binding)
                    .unwrap_or_else(|| Ty::error(self.db));
                let local = self.binding(*binding);
                let op = self.closure_value(root, ty, Some(*binding));
                self.assign_to(local, op, ty);
            }
        }
    }

    /// Matches a value against the pattern of a `let`, a `let … else` or
    /// a `for`, binding its names.
    pub(super) fn matched(
        &mut self,
        pat: PatId,
        op: Operand<'db>,
        ty: Ty<'db>,
        otherwise: Option<Otherwise>,
    ) {
        match self.body.pat(pat) {
            Pat::Bind { binding, sub: None } if otherwise.is_none() => {
                let local = self.binding(*binding);
                self.assign_to(local, op, ty);
                return;
            }
            Pat::Wildcard if otherwise.is_none() => return,
            _ => {}
        }
        let subject = self.materialize(op, ty);
        let Some(tree) = decision_tree(
            self.db,
            self.program,
            self.owner,
            &self.pats,
            ty,
            &[(pat, false)],
        ) else {
            self.trap(TrapKind::Error, None);
            return;
        };
        let (cont, fail) = (self.new_block(), self.new_block());
        let mut m = Match {
            subject,
            arms: vec![Some(cont)],
            guards: vec![None],
            fail,
        };
        self.lower_decision_tree(&tree, &mut m);
        self.switch_to(fail);
        let site = otherwise.map(|o| o.body);
        if let Some(otherwise) = otherwise {
            self.otherwise(otherwise, subject, ty);
        }
        self.trap(TrapKind::NoMatch, site);
        self.switch_to(cont);
    }

    /// The `else` part of a `let`, its pattern given the unmatched value
    /// in `subject`. It leaves, so its end is never reached (§7.1.1).
    fn otherwise(&mut self, otherwise: Otherwise, subject: Local, ty: Ty<'db>) {
        if let Some(rest) = otherwise.rest {
            let rest_ty = self.pats[rest.index()].unwrap_or_else(|| Ty::error(self.db));
            let value = self.temp(rest_ty);
            self.assign_to(value, Operand::Local(subject), ty);
            self.matched(rest, Operand::Local(value), rest_ty, None);
        }
        self.eval(otherwise.body, Dest::Discard);
    }

    /// `let pat: T = value else …`: the value is tested to be a `T`
    /// before it is matched (§7.1.1).
    fn tested(
        &mut self,
        pat: PatId,
        op: Operand<'db>,
        ty: Ty<'db>,
        test: Ty<'db>,
        otherwise: Otherwise,
    ) {
        let subject = self.materialize(op, ty);
        let (fits, fail) = (self.new_block(), self.new_block());
        let cases = test
            .members(self.db)
            .into_iter()
            .map(|m| (m, fits))
            .collect();
        self.terminate(Terminator::Switch {
            place: Place::local(subject),
            cases,
            otherwise: fail,
        });
        self.switch_to(fail);
        self.otherwise(otherwise, subject, ty);
        self.trap(TrapKind::NoMatch, Some(otherwise.body));
        self.switch_to(fits);
        let narrowed = self.temp(test);
        self.assign_to(narrowed, Operand::Local(subject), ty);
        self.matched(pat, Operand::Local(narrowed), test, Some(otherwise));
    }

    /// `for` over a source of a stream: takes each value until the stream
    /// ends (§10.5).
    fn source_loop(&mut self, pat: PatId, iterable: ExprId, element: Ty<'db>, body: ExprId) {
        let db = self.db;
        let source = self.place_of(iterable);
        let end_ty = Ty::builtin(db, Builtin::RuntimeStream);
        let end = Place {
            local: source,
            path: vec![Step::Field(crag_hir::Name::new(db, "end".to_string()))],
        };
        let end = self.assign(end_ty, Rvalue::Read(end));
        let (head, inside, exit) = (self.new_block(), self.new_block(), self.new_block());
        self.terminate(Terminator::Jump(head));
        self.switch_to(head);
        let int = self.int();
        let status = self.assign(int, Rvalue::Intrinsic(Intrinsic::StreamNext, vec![end]));
        let more = self.is_zero(status);
        self.terminate(Terminator::Branch {
            cond: more,
            then: inside,
            otherwise: exit,
        });
        self.switch_to(inside);
        let value = self.assign(
            element,
            Rvalue::Intrinsic(Intrinsic::StreamValue, Vec::new()),
        );
        self.matched(pat, value, element, None);
        self.eval(body, Dest::Discard);
        self.push(Statement::Poll);
        self.terminate(Terminator::Jump(head));
        self.switch_to(exit);
    }

    /// The function a filling names, as a concrete instance.
    pub(super) fn filled(&self, filling: &Filling<'db>) -> Option<Instance<'db>> {
        match filling {
            Filling::Function(instance) => self.concrete(instance),
            Filling::Slot(k) => self.fillings.get(*k as usize).cloned(),
        }
    }

    /// Calls a filling with the arguments and gives its result.
    pub(super) fn call_filled(
        &mut self,
        filling: &Filling<'db>,
        args: Vec<(Operand<'db>, Ty<'db>)>,
        site: ExprId,
    ) -> Option<(Local, Ty<'db>)> {
        let instance = self.filled(filling)?;
        let sig = self.instance_signature(&instance);
        let result = sig.result?;
        let key = self.callable(site, &instance)?;
        let ops = args
            .into_iter()
            .zip(&sig.params)
            .map(|((op, ty), p)| self.coerce(op, ty, p.ty))
            .collect();
        Some((self.call_code(key, ops, result, site), result))
    }

    /// `for` over what a function lists first: a map's entries or a set's
    /// members (§7.3.1).
    fn listed_loop(&mut self, pat: PatId, iterable: ExprId, list: &Filling<'db>, body: ExprId) {
        let op = self.expr(iterable);
        let ty = self.ty(iterable);
        let Some((listed, list_ty)) = self.call_filled(list, vec![(op, ty)], iterable) else {
            self.trap(TrapKind::Error, Some(iterable));
            return;
        };
        let Some((Builtin::List, [element])) = list_ty.as_builtin(self.db) else {
            self.trap(TrapKind::Error, Some(iterable));
            return;
        };
        let element = *element;
        let int_ty = self.int();
        let len = self.assign(int_ty, Rvalue::Len(Place::local(listed)));
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
        let value = self.assign(
            element,
            Rvalue::Index {
                list: Place::local(listed),
                index: Operand::Local(i),
            },
        );
        let pat_ty = self.pats[pat.index()].unwrap_or(element);
        let value = self.coerce(value, element, pat_ty);
        self.matched(pat, value, pat_ty, None);
        self.eval(body, Dest::Discard);
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

    /// `for` over a range of a type with its own `next` and `compare`
    /// (§7.4): from the first value, while it is not past the last; it
    /// never calls `next` on the last.
    fn stepped_loop(
        &mut self,
        pat: PatId,
        iterable: ExprId,
        next: &Filling<'db>,
        compare: &Filling<'db>,
        body: ExprId,
    ) {
        let db = self.db;
        let container = self.place_of(iterable);
        let ty = self.ty(iterable);
        let Some(element) = (match ty.kind(db) {
            TyKind::Named(_, args) => args.first().copied(),
            _ => None,
        }) else {
            self.trap(TrapKind::Error, Some(iterable));
            return;
        };
        let field = |name: &str| Step::Field(crag_hir::Name::new(db, name.to_string()));
        let has_last = fields_of(db, self.program, ty)
            .is_some_and(|fs| fs.iter().any(|(n, _)| n.text(db) == "last"));
        let i = self.temp(element);
        let first = Place {
            local: container,
            path: vec![field("first")],
        };
        self.push(Statement::Assign(i, Rvalue::Read(first)));
        let last = has_last.then(|| {
            let place = Place {
                local: container,
                path: vec![field("last")],
            };
            self.assign(element, Rvalue::Read(place))
        });
        let tag = |name: &str| {
            prelude_item(db, self.program, name)
                .map(|item| Ty::new(db, TyKind::Named(item, Vec::new())))
        };
        let (Some(greater), Some(equal)) = (tag("Greater"), tag("Equal")) else {
            self.trap(TrapKind::Error, Some(iterable));
            return;
        };
        let (inside, exit) = (self.new_block(), self.new_block());
        // Whether the value compares as `wanted` with the last.
        let is = |this: &mut Self, wanted: Ty<'db>, yes: BlockId, no: BlockId| -> bool {
            let Some(last) = last.clone() else {
                this.terminate(Terminator::Jump(no));
                return true;
            };
            let args = vec![(Operand::Local(i), element), (last, element)];
            let Some((order, _)) = this.call_filled(compare, args, iterable) else {
                return false;
            };
            this.terminate(Terminator::Switch {
                place: Place::local(order),
                cases: vec![(wanted, yes)],
                otherwise: no,
            });
            true
        };
        if !is(self, greater, exit, inside) {
            self.trap(TrapKind::Error, Some(iterable));
            return;
        }
        self.switch_to(inside);
        self.matched(pat, Operand::Local(i), element, None);
        self.eval(body, Dest::Discard);
        let more = self.new_block();
        if !is(self, equal, exit, more) {
            self.trap(TrapKind::Error, Some(iterable));
            return;
        }
        self.switch_to(more);
        let Some((n, n_ty)) = self.call_filled(next, vec![(Operand::Local(i), element)], iterable)
        else {
            self.trap(TrapKind::Error, Some(iterable));
            return;
        };
        self.assign_to(i, Operand::Local(n), n_ty);
        self.push(Statement::Poll);
        self.terminate(Terminator::Jump(inside));
        self.switch_to(exit);
    }

    fn for_loop(&mut self, pat: PatId, iterable: ExprId, body: ExprId) {
        let db = self.db;
        let ty = self.ty(iterable);
        let range = |name: &str| prelude_item(db, self.program, name);
        match self.types.iteration(iterable).cloned() {
            Some(Iteration::Listed(filling)) => {
                return self.listed_loop(pat, iterable, &filling, body);
            }
            Some(Iteration::Stepped { next, compare }) => {
                return self.stepped_loop(pat, iterable, &next, &compare, body);
            }
            None => {}
        }
        let (kind, element) = match ty.kind(db) {
            TyKind::Named(item, args) if crag_types::is_source(db, *item) => {
                return self.source_loop(pat, iterable, args[0], body);
            }
            TyKind::Builtin(Builtin::List, args) => ("list", args[0]),
            TyKind::Named(item, args) if Some(*item) == range("Range") => ("range", args[0]),
            TyKind::Named(item, args) if Some(*item) == range("RangeFrom") => ("from", args[0]),
            _ => {
                self.unsupported(iterable, "`for` over other types than lists and ranges");
                return;
            }
        };
        let step = match element.as_builtin(db) {
            Some((b, _)) if b.int_range().is_some() || matches!(b, Builtin::Fixed(_)) => b,
            Some((Builtin::CodePoint, _)) if kind == "range" => Builtin::CodePoint,
            _ if kind == "list" => Builtin::Int,
            _ => {
                self.unsupported(iterable, "ranges of other types than numbers");
                return;
            }
        };
        let container = self.place_of(iterable);
        let int_ty = self.int();
        let bool_ty = self.bool_ty;
        let next = |b: &mut Self, i: Local, ty: Builtin, check: Option<ExprId>| {
            let elem = b.locals[i.index()].ty;
            let rvalue = Rvalue::Binary {
                op: BinOp::Add,
                ty,
                a: Operand::Local(i),
                b: int(1),
                check,
            };
            b.assign(elem, rvalue)
        };
        if kind == "list" {
            let len = self.assign(int_ty, Rvalue::Len(Place::local(container)));
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
            let list = Place::local(container);
            let index = Operand::Local(i);
            let value = self.assign(element, Rvalue::Index { list, index });
            self.matched(pat, value, element, None);
            self.eval(body, Dest::Discard);
            let n = next(self, i, Builtin::Int, None);
            self.assign_to(i, n, int_ty);
            self.push(Statement::Poll);
            self.terminate(Terminator::Jump(head));
            self.switch_to(exit);
            return;
        }
        let field = |name: &str| Step::Field(crag_hir::Name::new(db, name.to_string()));
        let i = self.temp(element);
        let first = Place {
            local: container,
            path: vec![field("first")],
        };
        self.push(Statement::Assign(i, Rvalue::Read(first)));
        let (inside, exit) = (self.new_block(), self.new_block());
        let last = if kind == "range" {
            let last = Place {
                local: container,
                path: vec![field("last")],
            };
            let last = self.assign(element, Rvalue::Read(last));
            let some = self.compare(CmpOp::Le, step, Operand::Local(i), last.clone());
            self.terminate(Terminator::Branch {
                cond: some,
                then: inside,
                otherwise: exit,
            });
            Some(last)
        } else {
            self.terminate(Terminator::Jump(inside));
            None
        };
        self.switch_to(inside);
        self.matched(pat, Operand::Local(i), element, None);
        self.eval(body, Dest::Discard);
        if let Some(last) = last {
            let done = self.compare(CmpOp::Eq, step, Operand::Local(i), last);
            let more = self.new_block();
            self.terminate(Terminator::Branch {
                cond: done,
                then: exit,
                otherwise: more,
            });
            self.switch_to(more);
        }
        // An endless range traps past its type's last value.
        let check = (kind == "from").then_some(iterable);
        let n = next(self, i, step, check);
        if step == Builtin::CodePoint {
            // The surrogates are not code points (§2.6).
            let gap = self.assign(
                bool_ty,
                Rvalue::Compare {
                    op: CmpOp::Eq,
                    ty: step,
                    a: n.clone(),
                    b: int(0xD800),
                },
            );
            let (skip, plain, back) = (self.new_block(), self.new_block(), self.new_block());
            self.terminate(Terminator::Branch {
                cond: gap,
                then: skip,
                otherwise: plain,
            });
            self.switch_to(skip);
            self.push(Statement::Assign(i, Rvalue::Use(int(0xE000))));
            self.terminate(Terminator::Jump(back));
            self.switch_to(plain);
            self.assign_to(i, n, element);
            self.terminate(Terminator::Jump(back));
            self.switch_to(back);
        } else {
            self.assign_to(i, n, element);
        }
        self.push(Statement::Poll);
        self.terminate(Terminator::Jump(inside));
        self.switch_to(exit);
    }

    // `case`.
}
