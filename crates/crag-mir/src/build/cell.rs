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

//! Lazy values, cells, refs and exts: what a read of a lazy value does,
//! how a value's cell is reached, how a ref is read and updated, and
//! atomic blocks with their handlers.

use super::*;

impl<'a, 'db> MirBuilder<'a, 'db> {
    /// The value type of a read of a lazy value, if the call is the
    /// prelude's `value` (§6.10).
    pub(super) fn lazy_read(&self, instance: &Instance<'db>) -> Option<Ty<'db>> {
        let db = self.db;
        let function = instance.function;
        if function.module(db).path(db) != PRELUDE
            || function.name(db).text(db) != "value"
            || hir_body(db, self.program, Owner::Item(function))
                .root
                .is_some()
        {
            return None;
        }
        let sig = self.instance_signature(instance);
        match sig.params.first()?.ty.as_builtin(db) {
            Some((Builtin::Lazy, &[value])) => Some(value),
            _ => None,
        }
    }

    /// `.value` of a lazy value: the value there, or the one the reader
    /// computes and stores when it is the first, or a trap like the
    /// computation's.
    pub(super) fn lazy_value(
        &mut self,
        expr: ExprId,
        lazy: Operand<'db>,
        ty: Ty<'db>,
    ) -> Operand<'db> {
        let db = self.db;
        let int = self.int();
        let status = self.assign(
            int,
            Rvalue::Intrinsic(Intrinsic::LazyGet, vec![lazy.clone()]),
        );
        let value = self.temp(ty);
        let (done, other, run, trapped, join) = (
            self.new_block(),
            self.new_block(),
            self.new_block(),
            self.new_block(),
            self.new_block(),
        );
        let there = self.is_zero(status.clone());
        self.terminate(Terminator::Branch {
            cond: there,
            then: done,
            otherwise: other,
        });
        self.switch_to(done);
        let read = self.assign(ty, Rvalue::Intrinsic(Intrinsic::LazyValue, Vec::new()));
        self.assign_to(value, read, ty);
        self.terminate(Terminator::Jump(join));
        self.switch_to(other);
        let compute = self.assign(
            self.bool_ty,
            Rvalue::Compare {
                op: CmpOp::Eq,
                ty: Builtin::Int,
                a: status,
                b: Operand::Const(Constant::Int(1)),
            },
        );
        self.terminate(Terminator::Branch {
            cond: compute,
            then: run,
            otherwise: trapped,
        });
        self.switch_to(run);
        let code_ty = Ty::new(
            db,
            TyKind::Fn {
                params: Vec::new(),
                result: ty,
                pure: false,
            },
        );
        let code = self.assign(
            code_ty,
            Rvalue::Intrinsic(Intrinsic::LazyCode, vec![lazy.clone()]),
        );
        let computed = self.temp(ty);
        let after = self.new_block();
        self.terminate(Terminator::CallValue {
            callee: code,
            args: Vec::new(),
            dst: computed,
            target: after,
            site: expr,
            unwind: None,
            catch: None,
        });
        self.switch_to(after);
        let unit = Ty::unit(db);
        self.assign(
            unit,
            Rvalue::Intrinsic(Intrinsic::LazySet, vec![lazy, Operand::Local(computed)]),
        );
        self.assign_to(value, Operand::Local(computed), ty);
        self.terminate(Terminator::Jump(join));
        self.switch_to(trapped);
        self.assign(unit, Rvalue::Intrinsic(Intrinsic::LazyTrap, Vec::new()));
        self.terminate(Terminator::Trap {
            kind: TrapKind::Error,
            site: Some(expr),
            detail: None,
            catch: None,
        });
        self.switch_to(join);
        Operand::Local(value)
    }

    /// The access function of a ref that a call of the prelude names, if
    /// it is one (Specification §9.3).
    pub(super) fn cell_access(&self, instance: &Instance<'db>) -> Option<Access> {
        let db = self.db;
        let function = instance.function;
        if function.module(db).path(db) != PRELUDE
            || hir_body(db, self.program, Owner::Item(function))
                .root
                .is_some()
        {
            return None;
        }
        let sig = self.instance_signature(instance);
        let first = sig.params.first()?.ty;
        if !matches!(first.as_builtin(db), Some((Builtin::Ref | Builtin::Ext, _))) {
            return None;
        }
        Some(
            match (function.name(db).text(db).as_str(), sig.params.len()) {
                ("use", 1) => Access::Get,
                ("use", 2) => Access::Use,
                ("update", 2) => Access::Update,
                ("swap", 2) => Access::Swap,
                ("empty", 1) => Access::Empty,
                _ => return None,
            },
        )
    }

    /// A call of an access function of a ref: the read, the update or the
    /// swap of its cell.
    pub(super) fn ref_access(
        &mut self,
        expr: ExprId,
        access: Access,
        instance: &Instance<'db>,
        positional: &[ExprId],
    ) -> Operand<'db> {
        let db = self.db;
        let sig = self.instance_signature(instance);
        let cell_ty = sig.params[0].ty;
        let Some((builtin @ (Builtin::Ref | Builtin::Ext), &[ty])) = cell_ty.as_builtin(db) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        if positional.len() != sig.params.len() {
            return self.trap(TrapKind::Error, Some(expr));
        }
        let cell = self.expr(positional[0]);
        let cell = Operand::Local(self.materialize(cell, cell_ty));
        if builtin == Builtin::Ext {
            return self.ext_access(expr, access, cell, ty, positional);
        }
        match access {
            Access::Get => self.ref_get(cell, ty),
            Access::Use => {
                let value = self.ref_get(cell, ty);
                let f = self.expr(positional[1]);
                let f_ty = self.ty(positional[1]);
                let f = self.typed(f, f_ty);
                let Some((_, result, _)) = f_ty.as_fn(db) else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let dst = self.temp(result);
                let target = self.new_block();
                self.terminate(Terminator::CallValue {
                    callee: f,
                    args: vec![value],
                    dst,
                    target,
                    site: expr,
                    unwind: None,
                    catch: None,
                });
                self.switch_to(target);
                Operand::Local(dst)
            }
            Access::Swap => {
                let new = self.expr(positional[1]);
                let new = self.coerce(new, self.ty(positional[1]), ty);
                let old = self.assign(ty, Rvalue::Intrinsic(Intrinsic::RefSwap, vec![cell, new]));
                self.leave_on_conflict();
                old
            }
            Access::Empty => {
                let empty_item = prelude_item(db, self.program, "Empty");
                let Some(empty) = ty.members(db).into_iter().find(
                    |m| matches!(m.kind(db), TyKind::Named(item, _) if Some(*item) == empty_item),
                ) else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let new = self.coerce(Operand::Const(Constant::Tag(empty)), empty, ty);
                let old = self.assign(ty, Rvalue::Intrinsic(Intrinsic::RefSwap, vec![cell, new]));
                self.leave_on_conflict();
                old
            }
            Access::Update => self.ref_update(expr, cell, ty, positional[1]),
        }
    }

    /// An `atomic` block (§9.5): its body runs between `TxBegin` and the
    /// commit, or the abort when its value is an error. A conflict, found
    /// by a ref operation in the body, by code the body calls or by the
    /// commit, goes to the handler: it frees what the attempt pushed on the
    /// side stack, then passes the conflict to the block around this one,
    /// or reruns the body if this is the outermost of the transaction, or
    /// else leaves this function's frame for the block of a caller.
    pub(super) fn atomic_block(&mut self, expr: ExprId, inner: ExprId) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        let ty = self.ty(expr);
        let (int, unit) = (self.int(), Ty::unit(db));
        let outer = self.atomic.last().map(|f| f.handler);
        let side_ptr = self.assign(int, Rvalue::Intrinsic(Intrinsic::SidePtr, Vec::new()));
        let side_end = self.assign(int, Rvalue::Intrinsic(Intrinsic::SideEnd, Vec::new()));
        let signal_mark = self.assign(int, Rvalue::Intrinsic(Intrinsic::SignalMark, Vec::new()));
        let depth = self.assign(int, Rvalue::Intrinsic(Intrinsic::TxBegin, Vec::new()));
        let (head, outcome, handler, join) = (
            self.new_block(),
            self.new_block(),
            self.new_block(),
            self.new_block(),
        );
        let value = self.temp(ty);
        self.terminate(Terminator::Jump(head));
        self.switch_to(head);
        self.atomic.push(AtomicFrame {
            handler,
            outcome,
            value,
            handlers: self.handlers.len(),
        });
        self.eval(inner, Dest::Value(value));
        self.terminate(Terminator::Jump(outcome));
        self.atomic.pop();

        self.switch_to(outcome);
        let errors = crag_types::error_members(db, program, ty);
        if !errors.is_never(db) {
            let (abort, commit) = (self.new_block(), self.new_block());
            let cases = errors.members(db).into_iter().map(|m| (m, abort)).collect();
            self.terminate(Terminator::Switch {
                place: Place::local(value),
                cases,
                otherwise: commit,
            });
            self.switch_to(abort);
            self.assign(unit, Rvalue::Intrinsic(Intrinsic::TxAbort, Vec::new()));
            self.drain_signals();
            self.terminate(Terminator::Jump(join));
            self.switch_to(commit);
        }
        let status = self.assign(int, Rvalue::Intrinsic(Intrinsic::TxCommit, Vec::new()));
        let committed = self.is_zero(status);
        let delivered = self.new_block();
        self.terminate(Terminator::Branch {
            cond: committed,
            then: delivered,
            otherwise: handler,
        });
        self.switch_to(delivered);
        self.drain_signals();
        self.terminate(Terminator::Jump(join));

        self.switch_to(handler);
        self.assign(
            unit,
            Rvalue::Intrinsic(Intrinsic::SideReset, vec![side_ptr, side_end]),
        );
        // A throw may have left handlers of the frames it left.
        self.assign(
            unit,
            Rvalue::Intrinsic(Intrinsic::SignalReset, vec![signal_mark]),
        );
        match outer {
            Some(outer) => self.terminate(Terminator::Jump(outer)),
            None => {
                let outermost = self.assign(
                    self.bool_ty,
                    Rvalue::Compare {
                        op: CmpOp::Eq,
                        ty: Builtin::Int,
                        a: depth,
                        b: Operand::Const(Constant::Int(1)),
                    },
                );
                let (retry, throw) = (self.new_block(), self.new_block());
                self.terminate(Terminator::Branch {
                    cond: outermost,
                    then: retry,
                    otherwise: throw,
                });
                self.switch_to(retry);
                self.assign(unit, Rvalue::Intrinsic(Intrinsic::TxRetry, Vec::new()));
                self.drain_signals();
                self.push(Statement::Poll);
                self.terminate(Terminator::Jump(head));
                self.switch_to(throw);
                self.throw();
            }
        }
        self.switch_to(join);
        Operand::Local(value)
    }

    /// Forgets the signal handlers of the blocks from the one at `depth`
    /// on, as their code is left.
    pub(super) fn reset_handlers(&mut self, depth: usize) {
        let Some(first) = self.handlers.get(depth) else {
            return;
        };
        let mut ops = vec![first.mark.clone()];
        for block in &self.handlers[depth..] {
            ops.extend(block.closures.iter().cloned());
        }
        let unit = Ty::unit(self.db);
        self.assign(unit, Rvalue::Intrinsic(Intrinsic::SignalReset, ops));
    }

    /// Delivers the signals an outcome made deliverable.
    fn drain_signals(&mut self) {
        let unit = Ty::unit(self.db);
        self.assign(unit, Rvalue::Intrinsic(Intrinsic::SignalDrain, Vec::new()));
    }

    /// Leaves the attempt of the transaction for an `atomic` block of a
    /// caller.
    fn throw(&mut self) {
        let unit = Ty::unit(self.db);
        self.assign(unit, Rvalue::Intrinsic(Intrinsic::TxThrow, Vec::new()));
        self.terminate(Terminator::Trap {
            kind: TrapKind::Error,
            site: None,
            detail: None,
            catch: None,
        });
    }

    /// After a ref operation that reads a cell: when the attempt of the
    /// transaction the task runs must rerun, goes to the handler of the
    /// `atomic` block around, or leaves the frame for a caller's.
    pub(super) fn leave_on_conflict(&mut self) {
        let int = self.int();
        let flag = self.assign(int, Rvalue::Intrinsic(Intrinsic::TxConflicted, Vec::new()));
        let clear = self.is_zero(flag);
        let (go_on, conflict) = (self.new_block(), self.new_block());
        self.terminate(Terminator::Branch {
            cond: clear,
            then: go_on,
            otherwise: conflict,
        });
        self.switch_to(conflict);
        match self.atomic.last() {
            Some(frame) => {
                let handler = frame.handler;
                self.terminate(Terminator::Jump(handler));
            }
            None => self.throw(),
        }
        self.switch_to(go_on);
    }

    /// Whether an `Int` is zero, a `Bool`.
    pub(super) fn is_zero(&mut self, value: Operand<'db>) -> Operand<'db> {
        self.assign(
            self.bool_ty,
            Rvalue::Compare {
                op: CmpOp::Eq,
                ty: Builtin::Int,
                a: value,
                b: Operand::Const(Constant::Int(0)),
            },
        )
    }

    /// A call of an access function of an `ext`: its closure runs once,
    /// while the task holds the lock (§9.6).
    fn ext_access(
        &mut self,
        expr: ExprId,
        access: Access,
        cell: Operand<'db>,
        ty: Ty<'db>,
        positional: &[ExprId],
    ) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        let unit = Ty::unit(db);
        let call = |b: &mut Self, f: Operand<'db>, result: Ty<'db>, arg: Operand<'db>| {
            let dst = b.temp(result);
            let target = b.new_block();
            b.terminate(Terminator::CallValue {
                callee: f,
                args: vec![arg],
                dst,
                target,
                site: expr,
                unwind: None,
                catch: None,
            });
            b.switch_to(target);
            dst
        };
        let closure = |b: &mut Self| {
            let f = b.expr(positional[1]);
            let f_ty = b.ty(positional[1]);
            let result = f_ty.as_fn(db).map(|(_, result, _)| result);
            (b.typed(f, f_ty), result)
        };
        self.assign(
            unit,
            Rvalue::Intrinsic(Intrinsic::ExtLock, vec![cell.clone()]),
        );
        let value = |b: &mut Self| {
            b.assign(
                ty,
                Rvalue::Intrinsic(Intrinsic::ExtValue, vec![cell.clone()]),
            )
        };
        let result = match access {
            Access::Get => value(self),
            Access::Use => {
                let (f, result) = closure(self);
                let Some(result) = result else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let v = value(self);
                Operand::Local(call(self, f, result, v))
            }
            Access::Swap | Access::Empty => {
                let new = match access {
                    Access::Swap => {
                        let new = self.expr(positional[1]);
                        self.coerce(new, self.ty(positional[1]), ty)
                    }
                    _ => {
                        let empty_item = prelude_item(db, program, "Empty");
                        let Some(empty) = ty.members(db).into_iter().find(|m| {
                            matches!(m.kind(db), TyKind::Named(item, _) if Some(*item) == empty_item)
                        }) else {
                            return self.trap(TrapKind::Error, Some(expr));
                        };
                        self.coerce(Operand::Const(Constant::Tag(empty)), empty, ty)
                    }
                };
                let old = value(self);
                self.assign(
                    unit,
                    Rvalue::Intrinsic(Intrinsic::ExtStore, vec![cell.clone(), new]),
                );
                old
            }
            Access::Update => {
                let (f, result) = closure(self);
                let Some(result_ty) = result else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let out = self.temp(self.ty(expr));
                let v = value(self);
                let new = call(self, f, result_ty, v);
                let join = self.new_block();
                let errors = crag_types::error_members(db, program, result_ty);
                if !errors.is_never(db) {
                    let (failed, fits) = (self.new_block(), self.new_block());
                    let cases = errors
                        .members(db)
                        .into_iter()
                        .map(|m| (m, failed))
                        .collect();
                    self.terminate(Terminator::Switch {
                        place: Place::local(new),
                        cases,
                        otherwise: fits,
                    });
                    self.switch_to(failed);
                    self.assign_to(out, Operand::Local(new), result_ty);
                    self.terminate(Terminator::Jump(join));
                    self.switch_to(fits);
                }
                let new = self.coerce(Operand::Local(new), result_ty, ty);
                self.assign(
                    unit,
                    Rvalue::Intrinsic(Intrinsic::ExtStore, vec![cell.clone(), new]),
                );
                self.assign_to(out, self.unit(), unit);
                self.terminate(Terminator::Jump(join));
                self.switch_to(join);
                Operand::Local(out)
            }
        };
        self.assign(unit, Rvalue::Intrinsic(Intrinsic::ExtUnlock, vec![cell]));
        result
    }

    /// The current value of a ref cell, with a reference of its own.
    pub(super) fn ref_get(&mut self, cell: Operand<'db>, ty: Ty<'db>) -> Operand<'db> {
        let int = self.int();
        self.assign(int, Rvalue::Intrinsic(Intrinsic::RefRead, vec![cell]));
        self.leave_on_conflict();
        let value = self.assign(ty, Rvalue::Intrinsic(Intrinsic::RefValue, Vec::new()));
        let unit = Ty::unit(self.db);
        self.assign(unit, Rvalue::Intrinsic(Intrinsic::RefDone, Vec::new()));
        value
    }

    /// `update`: the closure runs on the value read, and its result is
    /// committed if the cell still holds that version, else it runs again.
    /// An error result ends the update and is its value (§9.3).
    fn ref_update(
        &mut self,
        expr: ExprId,
        cell: Operand<'db>,
        ty: Ty<'db>,
        closure: ExprId,
    ) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        if let Some((op, k)) = self.commutative(closure, ty) {
            let Some((builtin, _)) = ty.as_builtin(db) else {
                return self.trap(TrapKind::Error, Some(expr));
            };
            let k = self.expr(k);
            let status = self.assign(
                self.int(),
                Rvalue::Intrinsic(Intrinsic::RefApply { op, ty: builtin }, vec![cell, k]),
            );
            self.leave_on_conflict();
            let fits = self.assign(
                self.bool_ty,
                Rvalue::Compare {
                    op: CmpOp::Eq,
                    ty: Builtin::Int,
                    a: status,
                    b: Operand::Const(Constant::Int(0)),
                },
            );
            let (done, overflow) = (self.new_block(), self.new_block());
            self.terminate(Terminator::Branch {
                cond: fits,
                then: done,
                otherwise: overflow,
            });
            self.switch_to(overflow);
            self.trap(TrapKind::Overflow, Some(expr));
            self.switch_to(done);
            return self.unit();
        }
        let f = self.expr(closure);
        let f_ty = self.ty(closure);
        let f = Operand::Local(self.materialize(f, f_ty));
        let Some((_, result_ty, _)) = f_ty.as_fn(db) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let value = self.temp(self.ty(expr));
        let (head, join) = (self.new_block(), self.new_block());
        self.terminate(Terminator::Jump(head));
        self.switch_to(head);
        let int = self.int();
        let version = self.assign(
            int,
            Rvalue::Intrinsic(Intrinsic::RefRead, vec![cell.clone()]),
        );
        self.leave_on_conflict();
        let old = self.assign(ty, Rvalue::Intrinsic(Intrinsic::RefValue, Vec::new()));
        let new = self.temp(result_ty);
        let ran = self.new_block();
        self.terminate(Terminator::CallValue {
            callee: f,
            args: vec![old],
            dst: new,
            target: ran,
            site: expr,
            unwind: None,
            catch: None,
        });
        self.switch_to(ran);
        let errors = crag_types::error_members(db, program, result_ty);
        if !errors.is_never(db) {
            let (failed, fits) = (self.new_block(), self.new_block());
            let cases = errors
                .members(db)
                .into_iter()
                .map(|m| (m, failed))
                .collect();
            self.terminate(Terminator::Switch {
                place: Place::local(new),
                cases,
                otherwise: fits,
            });
            self.switch_to(failed);
            let unit = Ty::unit(db);
            self.assign(unit, Rvalue::Intrinsic(Intrinsic::RefDone, Vec::new()));
            self.drain_signals();
            self.assign_to(value, Operand::Local(new), result_ty);
            self.terminate(Terminator::Jump(join));
            self.switch_to(fits);
        }
        let new = self.coerce(Operand::Local(new), result_ty, ty);
        let status = self.assign(
            int,
            Rvalue::Intrinsic(Intrinsic::RefCommit, vec![cell, version, new]),
        );
        self.drain_signals();
        let committed = self.assign(
            self.bool_ty,
            Rvalue::Compare {
                op: CmpOp::Eq,
                ty: Builtin::Int,
                a: status,
                b: Operand::Const(Constant::Int(0)),
            },
        );
        let (done, again) = (self.new_block(), self.new_block());
        self.terminate(Terminator::Branch {
            cond: committed,
            then: done,
            otherwise: again,
        });
        self.switch_to(again);
        self.push(Statement::Poll);
        self.terminate(Terminator::Jump(head));
        self.switch_to(done);
        self.assign_to(value, self.unit(), Ty::unit(db));
        self.terminate(Terminator::Jump(join));
        self.switch_to(join);
        Operand::Local(value)
    }
}
