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

//! Expressions: each is evaluated into an operand of the current block,
//! and control flow adds blocks. Blocks, trap regions, names, literals,
//! indexing, comparisons and branches.

use super::*;

impl<'a, 'db> MirBuilder<'a, 'db> {
    /// Evaluates an expression into `dest`.
    pub(super) fn eval(&mut self, expr: ExprId, dest: Dest) {
        let body = self.body;
        // An assertion in a test is recorded, and the test goes on; a
        // block, `if` or `case` passes it to the expression that gives it.
        if self.test
            && matches!(dest, Dest::Discard | Dest::Return)
            && !matches!(
                body.expr(expr),
                Expr::Block { .. } | Expr::If { .. } | Expr::Case { .. }
            )
            && self.is_assertion(self.ty(expr))
        {
            let ty = self.ty(expr);
            let op = self.expr(expr);
            self.record_assertion(op, ty, expr);
            let unit = Ty::unit(self.db);
            return self.finish_dest(self.unit(), unit, dest);
        }
        match body.expr(expr) {
            Expr::Block { stmts, tail } => {
                // A block with signal handlers forgets them when it ends.
                let registers = stmts.iter().any(
                    |s| matches!(s, Stmt::On { handler, .. } if self.types.trap_handler(*handler).is_none()),
                );
                if registers {
                    let int = self.int();
                    let mark =
                        self.assign(int, Rvalue::Intrinsic(Intrinsic::SignalMark, Vec::new()));
                    self.handlers.push(HandlerBlock {
                        mark,
                        closures: Vec::new(),
                    });
                }
                self.block_rest(stmts, *tail, dest, &[]);
                if registers {
                    if !matches!(dest, Dest::Return) {
                        let depth = self.handlers.len() - 1;
                        self.reset_handlers(depth);
                    }
                    self.handlers.pop();
                }
            }
            Expr::If {
                condition,
                then,
                otherwise,
            } => {
                let (t, f, join) = (self.new_block(), self.new_block(), self.new_block());
                self.branch_on(*condition, t, f);
                self.switch_to(t);
                self.eval(*then, dest);
                self.join(dest, join);
                self.switch_to(f);
                match otherwise {
                    Some(otherwise) => self.eval(*otherwise, dest),
                    None => {
                        let unit = Ty::unit(self.db);
                        self.finish_dest(self.unit(), unit, dest);
                    }
                }
                self.join(dest, join);
                self.switch_to(join);
            }
            Expr::Case { subject, arms } => self.case(expr, *subject, arms, dest),
            _ if self.is_optional(expr) => {
                let op = self.optional(expr);
                self.finish_dest(op, self.ty(expr), dest);
            }
            // A tail call would leave an `atomic` block's frame.
            Expr::Call { .. } | Expr::MethodCall { .. } | Expr::TypedCall { .. }
                if matches!(dest, Dest::Return) =>
            {
                let op = self.call(expr, self.leaves_frame_freely());
                self.finish_dest(op, self.ty(expr), dest);
            }
            Expr::Field { .. } if matches!(dest, Dest::Return) && self.is_call(expr) => {
                let op = self.call(expr, self.leaves_frame_freely());
                self.finish_dest(op, self.ty(expr), dest);
            }
            _ => {
                let op = self.expr(expr);
                self.finish_dest(op, self.ty(expr), dest);
            }
        }
    }

    /// Whether a tail call may leave the frame: not from an `atomic`
    /// block, a block with signal handlers or one with a trap handler.
    fn leaves_frame_freely(&self) -> bool {
        self.atomic.is_empty() && self.handlers.is_empty() && self.catches.is_empty()
    }

    /// The statements of a block from one on, then its tail, into `dest`.
    /// A trap handler takes the rest after it (§8.3.1); `siblings` are the
    /// trap handlers of the block before.
    fn block_rest(
        &mut self,
        stmts: &[Stmt],
        tail: Option<ExprId>,
        dest: Dest,
        siblings: &[ExprId],
    ) {
        for (i, stmt) in stmts.iter().enumerate() {
            if let Stmt::On { handler, .. } = stmt
                && self.types.trap_handler(*handler).is_some()
            {
                let mut handlers = siblings.to_vec();
                handlers.push(*handler);
                self.trap_region(&stmts[i + 1..], tail, dest, &handlers);
                return;
            }
            self.stmt(stmt);
        }
        match tail {
            Some(tail) => {
                self.step(Some(tail));
                self.eval(tail, dest)
            }
            None => {
                let unit = Ty::unit(self.db);
                self.finish_dest(self.unit(), unit, dest);
            }
        }
    }

    /// The rest of a block that trap handlers cover, then their handler:
    /// the state the trap left behind reset, the trap made a value of its
    /// type, and the most specific of the handlers that takes it run into
    /// `dest`; a trap none takes goes on to the handlers around
    /// (§8.3.1).
    fn trap_region(
        &mut self,
        stmts: &[Stmt],
        tail: Option<ExprId>,
        dest: Dest,
        handlers: &[ExprId],
    ) {
        let (db, program) = (self.db, self.program);
        let (int_ty, unit) = (self.int(), Ty::unit(db));
        let int = int_ty;
        let intrinsic = |b: &mut Self, ty: Ty<'db>, i: Intrinsic<'db>, args: Vec<Operand<'db>>| {
            b.assign(ty, Rvalue::Intrinsic(i, args))
        };
        let side_ptr = intrinsic(self, int, Intrinsic::SidePtr, Vec::new());
        let side_end = intrinsic(self, int, Intrinsic::SideEnd, Vec::new());
        let signal_mark = intrinsic(self, int, Intrinsic::SignalMark, Vec::new());
        let depth = intrinsic(self, int, Intrinsic::TxDepth, Vec::new());
        let (landing, join) = (self.new_block(), self.new_block());
        self.catches.push(landing);
        self.block_rest(stmts, tail, dest, handlers);
        self.join(dest, join);
        self.catches.pop();

        self.switch_to(landing);
        intrinsic(self, unit, Intrinsic::SideReset, vec![side_ptr, side_end]);
        intrinsic(self, unit, Intrinsic::SignalReset, vec![signal_mark]);
        intrinsic(self, unit, Intrinsic::TxUnwind, vec![depth]);
        let kind = intrinsic(self, int, Intrinsic::TrapCaught(0), Vec::new());
        let takes: Vec<(ExprId, Ty<'db>)> = handlers
            .iter()
            .filter_map(|&h| Some((h, self.subst(self.types.trap_handler(h)?))))
            .collect();
        for (abi, name) in TRAP_TYPES {
            let Some(item) = prelude_item(db, program, name) else {
                continue;
            };
            let trap_ty = Ty::new(db, TyKind::Named(item, Vec::new()));
            // The most specific handler whose type the trap fits.
            let fitting: Vec<&(ExprId, Ty<'db>)> = takes
                .iter()
                .filter(|(_, t)| crag_types::is_subtype(db, program, trap_ty, *t))
                .collect();
            let Some(&&(handler, takes_ty)) = fitting.iter().find(|(_, t)| {
                fitting
                    .iter()
                    .all(|(_, other)| crag_types::is_subtype(db, program, *t, *other))
            }) else {
                continue;
            };
            let (this, next) = (self.new_block(), self.new_block());
            let code = Operand::Const(Constant::Int(abi as i128));
            let is = self.compare(CmpOp::Eq, Builtin::Int, kind.clone(), code);
            self.terminate(Terminator::Branch {
                cond: is,
                then: this,
                otherwise: next,
            });
            self.switch_to(this);
            let value = self.trap_value(trap_ty);
            let value = self.coerce(value, trap_ty, takes_ty);
            if let Expr::Closure { params, body } = self.body.expr(handler) {
                if let Some(param) = params.first() {
                    self.matched(param.pat, value, takes_ty, None);
                }
                let body = *body;
                self.eval(body, dest);
            }
            self.join(dest, join);
            self.switch_to(next);
        }
        self.terminate(Terminator::Trap {
            kind: TrapKind::Rethrow,
            site: None,
            detail: None,
            catch: None,
        });
        self.switch_to(join);
    }

    /// Whether a type is a trap's.
    pub(super) fn is_trap(&self, ty: Ty<'db>) -> bool {
        let (db, program) = (self.db, self.program);
        prelude_item(db, program, "Trap").is_some_and(|item| {
            let trap = Ty::new(db, TyKind::Named(item, Vec::new()));
            !ty.is_error(db) && crag_types::is_subtype(db, program, ty, trap)
        })
    }

    /// The value of a trap a handler took, of the prelude's type for its
    /// kind (§8.3): its message, origin, and the detail some name.
    fn trap_value(&mut self, ty: Ty<'db>) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        let (int, text) = (self.int(), Ty::builtin(db, Builtin::Str));
        let Some(fields) = fields_of(db, program, ty) else {
            return self.trap(TrapKind::Error, None);
        };
        let mut values = Vec::new();
        for (name, field_ty) in fields {
            let op = match name.text(db).as_str() {
                "message" => self.assign(
                    text,
                    Rvalue::Intrinsic(Intrinsic::TrapCaughtText(1), Vec::new()),
                ),
                "origin" => {
                    let Some(origin) = fields_of(db, program, field_ty) else {
                        return self.trap(TrapKind::Error, None);
                    };
                    let mut parts = Vec::new();
                    for (part, _) in origin {
                        let op = match part.text(db).as_str() {
                            "module" => self.assign(
                                text,
                                Rvalue::Intrinsic(Intrinsic::TrapCaughtText(0), Vec::new()),
                            ),
                            "line" => self.assign(
                                int,
                                Rvalue::Intrinsic(Intrinsic::TrapCaught(1), Vec::new()),
                            ),
                            _ => self.assign(
                                int,
                                Rvalue::Intrinsic(Intrinsic::TrapCaught(2), Vec::new()),
                            ),
                        };
                        parts.push((part, op));
                    }
                    let dispose = self.dispose_code(field_ty);
                    self.assign(
                        field_ty,
                        Rvalue::Record {
                            ty: field_ty,
                            fields: parts,
                            dispose,
                            reuse: None,
                        },
                    )
                }
                _ => self.assign(
                    text,
                    Rvalue::Intrinsic(Intrinsic::TrapCaughtText(2), Vec::new()),
                ),
            };
            values.push((name, op));
        }
        let dispose = self.dispose_code(ty);
        self.assign(
            ty,
            Rvalue::Record {
                ty,
                fields: values,
                dispose,
                reuse: None,
            },
        )
    }

    pub(super) fn finish_dest(&mut self, op: Operand<'db>, ty: Ty<'db>, dest: Dest) {
        match dest {
            Dest::Value(local) => self.assign_to(local, op, ty),
            Dest::Discard => {}
            // A test gives no value.
            // `return` in an `atomic` block gives the block's value.
            Dest::Return if !self.atomic.is_empty() => {
                let frame = *self.atomic.last().expect("in a block");
                self.assign_to(frame.value, op, ty);
                self.reset_handlers(frame.handlers);
                self.terminate(Terminator::Jump(frame.outcome));
            }
            Dest::Return if !self.handlers.is_empty() => {
                self.reset_handlers(0);
                let ty_op = self.coerce(op, ty, self.result);
                let op = if self.test { self.unit() } else { ty_op };
                self.terminate(Terminator::Return(op));
            }
            Dest::Return if self.test => {
                self.terminate(Terminator::Return(self.unit()));
            }
            Dest::Return => {
                let op = self.coerce(op, ty, self.result);
                self.terminate(Terminator::Return(op));
            }
        }
    }

    /// Ends a branch that gives a value at the join.
    pub(super) fn join(&mut self, dest: Dest, join: BlockId) {
        if !matches!(dest, Dest::Return) {
            self.terminate(Terminator::Jump(join));
        }
    }

    fn is_call(&self, expr: ExprId) -> bool {
        self.types.callee(expr).is_some()
    }

    /// Evaluates an expression into an operand.
    pub(super) fn expr(&mut self, expr: ExprId) -> Operand<'db> {
        if let Some(&(Some(local), _)) = self.given.get(&expr) {
            return Operand::Local(local);
        }
        if self.is_optional(expr) {
            return self.optional(expr);
        }
        let db = self.db;
        let body = self.body;
        let ty = self.ty(expr);
        match body.expr(expr) {
            Expr::Missing => self.trap(TrapKind::Error, Some(expr)),
            Expr::Hole => self.trap(TrapKind::Hole, Some(expr)),
            Expr::Literal(literal) => {
                Operand::Const(self.literal(literal, ty, body.is_negative(expr)))
            }
            Expr::Embed => self.embed(expr, ty),
            Expr::Str(parts) => {
                let mut ops = Vec::new();
                for part in parts {
                    match part {
                        StrPart::Text(text) => {
                            ops.push(Operand::Const(Constant::Str(text.clone())))
                        }
                        // A string, or a conditioned alias of one, is
                        // written as it is.
                        StrPart::Expr(e)
                            if crag_types::unrefined(db, self.program, self.ty(*e)) == ty =>
                        {
                            let op = self.expr(*e);
                            ops.push(self.coerce(op, self.ty(*e), ty));
                        }
                        // A union with members that are text writes those
                        // as they are and the rest by their `show`.
                        StrPart::Expr(e) if self.has_text_member(self.ty(*e)) => {
                            let part = self.text_or_shown(*e, ty);
                            ops.push(part);
                        }
                        // A value whose type has a `show` of its own is
                        // written by it (§19.11).
                        StrPart::Expr(e) if self.writes_text(self.types.show(*e)) => {
                            let filling = self.types.show(*e).cloned().expect("a show");
                            let op = self.expr(*e);
                            let args = vec![(op, self.ty(*e))];
                            match self.call_filled(&filling, args, *e) {
                                Some((text, text_ty)) => {
                                    ops.push(self.coerce(Operand::Local(text), text_ty, ty))
                                }
                                None => return self.trap(TrapKind::Error, Some(*e)),
                            }
                        }
                        // Any other value is written as text, a number as
                        // such and the rest as `show` writes it by its
                        // structure; in a local, so its type stays known.
                        StrPart::Expr(e) => {
                            let part_ty = self.ty(*e);
                            let op = self.expr(*e);
                            ops.push(Operand::Local(self.materialize(op, part_ty)));
                        }
                    }
                }
                self.assign(ty, Rvalue::Concat(ops))
            }
            Expr::Name { local, item, .. } => self.name(expr, *local, item.as_ref()),
            Expr::Call { .. } | Expr::MethodCall { .. } | Expr::TypedCall { .. } => {
                self.call(expr, false)
            }
            Expr::Field { .. } if self.is_call(expr) => self.call(expr, false),
            Expr::Field { receiver, name, .. } => {
                let local = self.place_of(*receiver);
                let place = Place {
                    local,
                    path: vec![Step::Field(*name)],
                };
                self.assign(ty, Rvalue::Read(place))
            }
            Expr::Index { base, args } => self.index(expr, *base, args),
            Expr::And(..) | Expr::Or(..) | Expr::Not(_) | Expr::Is { .. } => {
                let result = self.temp(ty);
                let (t, f, join) = (self.new_block(), self.new_block(), self.new_block());
                self.branch_on(expr, t, f);
                for (block, tag) in [(t, self.true_ty), (f, self.false_ty)] {
                    self.switch_to(block);
                    let value = Operand::Const(Constant::Tag(tag));
                    self.assign_to(result, value, tag);
                    self.terminate(Terminator::Jump(join));
                }
                self.switch_to(join);
                Operand::Local(result)
            }
            Expr::Range { start, end } => {
                let Some(fields) = fields_of(db, self.program, ty) else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let mut values = Vec::new();
                for (&(name, field_ty), &e) in fields.iter().zip([*start].iter().chain(end)) {
                    let op = self.expr(e);
                    let op = self.coerce(op, self.ty(e), field_ty);
                    values.push((name, op));
                }
                let dispose = self.dispose_code(ty);
                self.assign(
                    ty,
                    Rvalue::Record {
                        ty,
                        fields: values,
                        dispose,
                        reuse: None,
                    },
                )
            }
            Expr::Record(fields) => self.record(expr, ty, &[], fields),
            Expr::List(items) => {
                let element = match ty.as_builtin(db) {
                    Some((Builtin::List | Builtin::Set, [element])) => *element,
                    _ => return self.trap(TrapKind::Error, Some(expr)),
                };
                let mut ops = Vec::new();
                for &item in items {
                    let op = self.expr(item);
                    ops.push(self.coerce(op, self.ty(item), element));
                }
                self.assign(ty, Rvalue::List(ops))
            }
            Expr::Map(entries) => {
                let (k, v) = match ty.as_builtin(db) {
                    Some((Builtin::Map, [k, v])) => (*k, *v),
                    _ => return self.trap(TrapKind::Error, Some(expr)),
                };
                let mut ops = Vec::new();
                for &(key, value) in entries {
                    let key_op = self.expr(key);
                    let key_op = self.coerce(key_op, self.ty(key), k);
                    let value_op = self.expr(value);
                    let value_op = self.coerce(value_op, self.ty(value), v);
                    ops.push((key_op, value_op));
                }
                self.assign(ty, Rvalue::Map(ops))
            }
            Expr::Block { .. } | Expr::If { .. } | Expr::Case { .. } => {
                let result = self.temp(ty);
                self.eval(expr, Dest::Value(result));
                Operand::Local(result)
            }
            // A grid of its rows' cells, row by row (§12.3).
            Expr::Grid(rows) => {
                let Some(fields) = fields_of(db, self.program, ty) else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let cells_ty = fields
                    .iter()
                    .find(|(n, _)| n.text(db) == "cells")
                    .map_or_else(|| Ty::error(db), |(_, t)| *t);
                let cell = match cells_ty.as_builtin(db) {
                    Some((Builtin::List, [cell])) => *cell,
                    _ => return self.trap(TrapKind::Error, Some(expr)),
                };
                let mut ops = Vec::new();
                for &item in rows.iter().flatten() {
                    let op = self.expr(item);
                    ops.push(self.coerce(op, self.ty(item), cell));
                }
                let cells = self.assign(cells_ty, Rvalue::List(ops));
                let width = rows.first().map_or(0, Vec::len) as i128;
                let height = rows.len() as i128;
                let values = fields
                    .iter()
                    .map(|(name, _)| {
                        let op = match name.text(db).as_str() {
                            "width" => int(width),
                            "height" => int(height),
                            _ => cells.clone(),
                        };
                        (*name, op)
                    })
                    .collect();
                let dispose = self.dispose_code(ty);
                self.assign(
                    ty,
                    Rvalue::Record {
                        ty,
                        fields: values,
                        dispose,
                        reuse: None,
                    },
                )
            }
            // A tag or unit record whose level is written, as `Empty[Int]`.
            Expr::TypeArgs { base, .. } => match body.expr(*base) {
                Expr::Name {
                    item: Some(Resolution::Type(item)),
                    local: None,
                    ..
                } => match type_def(db, self.program, *item).kind {
                    TypeDefKind::Record { .. } => self.record_value(expr, ty, &[], &[]),
                    _ => Operand::Const(Constant::Tag(ty)),
                },
                _ => self.unsupported(expr, "type arguments"),
            },
            Expr::Closure { .. } => self.closure_value(expr, ty, None),
            Expr::Pass => self.unsupported(expr, "`pass`"),
            Expr::Atomic(inner) => self.atomic_block(expr, *inner),
            Expr::Lazy(_) => {
                let Some((Builtin::Lazy, &[value])) = ty.as_builtin(db) else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let code = Ty::new(
                    db,
                    TyKind::Fn {
                        params: Vec::new(),
                        result: value,
                        pure: false,
                    },
                );
                let f = self.closure_value(expr, code, None);
                self.assign(ty, Rvalue::Intrinsic(Intrinsic::LazyNew, vec![f]))
            }
        }
    }

    /// The content of an `embed`'s resource as a constant of its type,
    /// which inference made `Bytes` or a `Str` that is UTF-8, or the value
    /// the type's `on Embed` handler makes of it (§18.4.1). A handler's
    /// error is a compile error, so the code never gets one.
    fn embed(&mut self, expr: ExprId, ty: Ty<'db>) -> Operand<'db> {
        let db = self.db;
        let Owner::Item(item) = *self.instance.owner(db) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let Ok(content) = crag_hir::embed_content(db, self.program, item) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let handler = lifecycle_handler(db, self.program, ty, "Embed");
        let param = match handler.as_ref().map(|h| h.form.kind(db)) {
            Some(TyKind::Fn { params, .. }) => params[0],
            _ => ty,
        };
        let constant = match param.as_builtin(db) {
            Some((Builtin::Str, _)) => match std::str::from_utf8(content) {
                Ok(text) => Constant::Str(text.to_string()),
                Err(_) => return self.trap(TrapKind::Error, Some(expr)),
            },
            _ => Constant::Bytes(content.to_vec()),
        };
        let Some(handler) = handler else {
            return Operand::Const(constant);
        };
        let result = handler.result(db);
        let Some(dst) = self.call_handler(&handler, vec![Operand::Const(constant)], expr) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let (fits, fail) = (self.new_block(), self.new_block());
        let cases = ty.members(db).into_iter().map(|m| (m, fits)).collect();
        self.terminate(Terminator::Switch {
            place: Place::local(dst),
            cases,
            otherwise: fail,
        });
        self.switch_to(fail);
        self.trap(TrapKind::Error, Some(expr));
        self.switch_to(fits);
        let value = self.temp(ty);
        self.assign_to(value, Operand::Local(dst), result);
        Operand::Local(value)
    }

    /// Calls a lifecycle handler and gives the local of its result: a
    /// function, or a closure of the declaring type, which captures
    /// nothing. None when it cannot be called, which is recorded.
    pub(super) fn call_handler(
        &mut self,
        handler: &Handler<'db>,
        args: Vec<Operand<'db>>,
        site: ExprId,
    ) -> Option<Local> {
        let db = self.db;
        let result = handler.result(db);
        match &handler.code {
            HandlerCode::Function(function) => {
                let func = self.callable(site, function)?;
                Some(self.call_code(func, args, result, site))
            }
            HandlerCode::Closure { .. } => {
                let value = Rvalue::Closure {
                    code: crate::handler_code(db, handler),
                    env: Ty::unit(db),
                    captures: Vec::new(),
                    placement: ClosurePlacement::Heap,
                };
                let callee = self.assign(handler.ty, value);
                let dst = self.temp(result);
                let target = self.new_block();
                self.terminate(Terminator::CallValue {
                    callee,
                    args,
                    dst,
                    target,
                    site,
                    unwind: None,
                    catch: None,
                });
                self.switch_to(target);
                Some(dst)
            }
        }
    }

    /// The value of a module-level `let`: a call of the code that computes
    /// it, which keeps the value once computed (§11.6.2). That code gives
    /// the whole value of the `let`, so only a `let` that binds one name is
    /// read so far.
    pub(super) fn module_value(&mut self, expr: ExprId, item: ItemId<'db>) -> Operand<'db> {
        let db = self.db;
        let owner = Owner::Item(item);
        let body = hir_body(db, self.program, owner);
        let single = body
            .pattern
            .is_some_and(|(pat, _)| matches!(body.pat(pat), Pat::Bind { sub: None, .. }));
        let Some(ty) = value_type(db, self.program, item) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        // A pattern binds a part of the value to the name (§5.5).
        let (func, ty) = match single {
            true => (InstanceKey::body(db, owner), ty),
            false => {
                let part =
                    InstanceKey::new(db, owner, Vec::new(), Vec::new(), Vec::new(), Entry::Part);
                (part, self.ty(expr))
            }
        };
        let dst = self.temp(ty);
        let target = self.new_block();
        self.terminate(Terminator::Call {
            func,
            args: Vec::new(),
            dst,
            target,
            site: expr,
            unwind: None,
            catch: None,
        });
        self.switch_to(target);
        self.coerce(Operand::Local(dst), ty, self.ty(expr))
    }

    /// The local an expression's value is in.
    pub(super) fn place_of(&mut self, expr: ExprId) -> Local {
        let op = self.expr(expr);
        self.materialize(op, self.ty(expr))
    }

    pub(super) fn literal(&self, literal: &Literal, ty: Ty<'db>, negative: bool) -> Constant<'db> {
        let sign: i128 = if negative { -1 } else { 1 };
        // A literal of a conditioned alias is one of its target (§3.10.1).
        let ty = crag_types::unrefined(self.db, self.program, ty);
        let builtin = ty.as_builtin(self.db).map(|(b, _)| b);
        let float = |x: f64| Constant::Float((sign as f64 * x).to_bits());
        match (literal, builtin) {
            (Literal::Int(n), Some(Builtin::Float)) => float(*n as f64),
            (Literal::Int(_) | Literal::Float(_), Some(Builtin::Fixed(scale))) => {
                Constant::Int(sign * literal_value(literal, Some(scale)).unwrap_or(0))
            }
            (Literal::Float(text), _) => float(text.parse().unwrap_or(0.0)),
            (Literal::Int(_), _) => Constant::Int(sign * literal_value(literal, None).unwrap_or(0)),
            (Literal::CodePoint(c), _) => Constant::Int(i128::from(u32::from(*c))),
            (Literal::Str(s), _) => Constant::Str(s.clone()),
            (Literal::Bytes(b), _) => Constant::Bytes(b.clone()),
        }
    }

    fn name(
        &mut self,
        expr: ExprId,
        local: Option<BindingId>,
        item: Option<&Resolution<'db>>,
    ) -> Operand<'db> {
        if let Some(binding) = local {
            let local = self.binding(binding);
            if self.celled(binding) {
                let ty = self.types.binding(binding).map(|t| self.subst(t));
                let ty = ty.unwrap_or_else(|| Ty::error(self.db));
                let value = self.ref_get(Operand::Local(local), ty);
                return self.coerce(value, ty, self.ty(expr));
            }
            // A narrowed binding is read as the member a test found
            // (§3.13.4).
            let (from, to) = (self.locals[local.index()].ty, self.ty(expr));
            return match self.converts(from, to) {
                true => self.assign(to, Rvalue::Convert(Operand::Local(local))),
                false => Operand::Local(local),
            };
        }
        // A function used as a value gets code that calls it.
        if self.is_call(expr) {
            let code = self.instance.with_entry(self.db, Entry::Function(expr));
            let (env, captures) = self.with_tree(expr, Ty::unit(self.db), Vec::new());
            let value = Rvalue::Closure {
                code,
                env,
                captures,
                placement: ClosurePlacement::Heap,
            };
            return self.assign(self.ty(expr), value);
        }
        match item {
            Some(Resolution::Value { value: Some(v), .. }) => {
                match self.module_locals.iter().find(|(m, _)| m == v) {
                    Some(&(_, local)) => {
                        let from = self.locals[local.index()].ty;
                        self.coerce(Operand::Local(local), from, self.ty(expr))
                    }
                    None => self.module_value(expr, *v),
                }
            }
            // A unit record is built like `T()` (§3.3).
            Some(Resolution::Type(item))
                if matches!(
                    type_def(self.db, self.program, *item).kind,
                    TypeDefKind::Record { .. }
                ) =>
            {
                self.record_value(expr, self.ty(expr), &[], &[])
            }
            Some(Resolution::Type(_)) => Operand::Const(Constant::Tag(self.ty(expr))),
            _ => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    fn index(&mut self, expr: ExprId, base: ExprId, args: &[ExprId]) -> Operand<'db> {
        let db = self.db;
        let ty = self.ty(expr);
        let base_ty = self.ty(base);
        if let [row, column] = args {
            return self.grid_cell(expr, base, *row, *column);
        }
        let [arg] = args else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let container = self.place_of(base);
        match base_ty.as_builtin(db) {
            Some((Builtin::List, _)) => {
                let index = self.expr(*arg);
                let len = self.assign(self.int(), Rvalue::Len(Place::local(container)));
                let below = self.compare(CmpOp::Lt, Builtin::Int, index.clone(), int(0));
                self.check(below, TrapKind::Index, expr);
                let beyond = self.compare(CmpOp::Ge, Builtin::Int, index.clone(), len);
                self.check(beyond, TrapKind::Index, expr);
                let list = Place::local(container);
                self.assign(ty, Rvalue::Index { list, index })
            }
            Some((Builtin::Map, [k, v])) => {
                let boxed = two_words(db, *v);
                let key = self.expr(*arg);
                let key = self.coerce(key, self.ty(*arg), *k);
                let map = Place::local(container);
                self.assign(ty, Rvalue::MapGet { map, key, boxed })
            }
            _ => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    /// `g[row, column]`: the cell, which traps with `Index` outside the
    /// grid (§19.11).
    fn grid_cell(
        &mut self,
        expr: ExprId,
        base: ExprId,
        row: ExprId,
        column: ExprId,
    ) -> Operand<'db> {
        let db = self.db;
        let ty = self.ty(expr);
        let grid = self.place_of(base);
        let int_ty = self.int();
        let field = |name: &str| Place {
            local: grid,
            path: vec![Step::Field(crag_hir::Name::new(db, name.to_string()))],
        };
        let width = self.assign(int_ty, Rvalue::Read(field("width")));
        let height = self.assign(int_ty, Rvalue::Read(field("height")));
        let row = self.expr(row);
        let column = self.expr(column);
        for (at, limit) in [(row.clone(), height), (column.clone(), width.clone())] {
            let below = self.compare(CmpOp::Lt, Builtin::Int, at.clone(), int(0));
            self.check(below, TrapKind::Index, expr);
            let beyond = self.compare(CmpOp::Ge, Builtin::Int, at, limit);
            self.check(beyond, TrapKind::Index, expr);
        }
        let start = self.assign(
            int_ty,
            Rvalue::Binary {
                op: BinOp::Mul,
                ty: Builtin::Int,
                a: row,
                b: width,
                check: None,
            },
        );
        let index = self.assign(
            int_ty,
            Rvalue::Binary {
                op: BinOp::Add,
                ty: Builtin::Int,
                a: start,
                b: column,
                check: None,
            },
        );
        let cells_ty = self.place_ty(grid, &field("cells").path);
        let cells = self.assign(cells_ty, Rvalue::Read(field("cells")));
        let cells = self.materialize(cells, cells_ty);
        self.assign(
            ty,
            Rvalue::Index {
                list: Place::local(cells),
                index,
            },
        )
    }

    pub(super) fn compare(
        &mut self,
        op: CmpOp,
        ty: Builtin,
        a: Operand<'db>,
        b: Operand<'db>,
    ) -> Operand<'db> {
        self.assign(self.bool_ty, Rvalue::Compare { op, ty, a, b })
    }

    /// Traps at `site` if the `Bool` is `True`.
    fn check(&mut self, cond: Operand<'db>, kind: TrapKind, site: ExprId) {
        let (trap, ok) = (self.new_block(), self.new_block());
        self.terminate(Terminator::Branch {
            cond,
            then: trap,
            otherwise: ok,
        });
        self.switch_to(trap);
        self.trap(kind, Some(site));
        self.switch_to(ok);
    }

    /// Goes to `then` if the condition holds and to `otherwise` if not,
    /// short-circuiting `and` and `or`.
    pub(super) fn branch_on(&mut self, cond: ExprId, then: BlockId, otherwise: BlockId) {
        match self.body.expr(cond) {
            Expr::And(a, b) => {
                let mid = self.new_block();
                self.branch_on(*a, mid, otherwise);
                self.switch_to(mid);
                self.branch_on(*b, then, otherwise);
            }
            Expr::Or(a, b) => {
                let mid = self.new_block();
                self.branch_on(*a, then, mid);
                self.switch_to(mid);
                self.branch_on(*b, then, otherwise);
            }
            Expr::Not(a) => self.branch_on(*a, otherwise, then),
            Expr::Is { expr, ty } => {
                let target = self.type_ref(*ty);
                let Some(target) = target else {
                    self.trap(TrapKind::Error, Some(cond));
                    return;
                };
                let local = self.place_of(*expr);
                let cases = target
                    .members(self.db)
                    .into_iter()
                    .map(|m| (m, then))
                    .collect();
                self.terminate(Terminator::Switch {
                    place: Place::local(local),
                    cases,
                    otherwise,
                });
            }
            _ => {
                let cond = self.expr(cond);
                self.terminate(Terminator::Branch {
                    cond,
                    then,
                    otherwise,
                });
            }
        }
    }

    // Calls.
}
