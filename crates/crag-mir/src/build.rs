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

//! Building the graph from the HIR and the types inference gave it.
//!
//! Every expression is evaluated into an operand of the current block;
//! control flow (`if`, `case`, `and`, `or`, `for`) adds blocks. A call in
//! tail position becomes a tail call (§5.6.3). Operators of the prelude on
//! numbers are not calls but operations, and arithmetic carries its check
//! until `insert_overflow_checks` makes it explicit. Where a value meets a
//! type it fits but is not, such as a member passed for a union, a
//! conversion is explicit too.

use std::collections::HashMap;

use crag_db::Db;
use crag_hir::{
    Arm, BindingId, BindingKind, Body, Expr, ExprId, FieldArg, ItemId, ItemKind, Literal, Owner,
    PRELUDE, Pat, PatId, Program, Resolution, Stmt, StrPart, hir_body, lower_body,
};
use crag_types::{
    Builtin, Callee, DecisionTree, InferenceResult, ListLen, Position, Signature, Step, Ty, TyKind,
    TypeDefKind, Value, body_types, decision_tree, declared_fields, fields_of, literal_value,
    prelude_item, signature, type_def,
};

use crate::InstanceKey;
use crate::ir::{
    BinOp, Block, BlockId, CmpOp, Constant, Local, LocalDecl, MirBody, Operand, Place, Rvalue,
    Statement, Terminator, TrapKind,
};

/// The graph of a function, test or module-level value, before checks and
/// reference counts are explicit. None for what has no body.
pub fn build<'db>(db: &'db dyn Db, program: Program, owner: Owner<'db>) -> Option<MirBody<'db>> {
    if let Owner::Item(item) = owner
        && !matches!(*item.kind(db), ItemKind::Function | ItemKind::Value)
    {
        return None;
    }
    let lowered = lower_body(db, program, owner);
    let root = lowered.body.root?;
    let types = body_types(db, program, owner);
    let mut b = MirBuilder::new(db, program, owner, &lowered.body, types);
    if lowered.errors.is_empty() && types.errors.is_empty() {
        b.eval(root, Dest::Return);
    } else {
        b.terminate(Terminator::Trap {
            kind: TrapKind::Error,
            site: None,
        });
    }
    Some(b.finish())
}

/// Whether values of a type are reference-counted: everything on the heap.
/// Numbers, tags and `()` are not.
pub(crate) fn counted<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    match ty.kind(db) {
        TyKind::Error => false,
        TyKind::Builtin(b, _) => matches!(
            b,
            Builtin::Str
                | Builtin::Bytes
                | Builtin::List
                | Builtin::Map
                | Builtin::Set
                | Builtin::Grid
                | Builtin::Ref
                | Builtin::Lazy
        ),
        TyKind::Named(item, _) => !matches!(type_def(db, program, *item).kind, TypeDefKind::Tag),
        TyKind::Record { fields, open } => !fields.is_empty() || *open,
        TyKind::Fn { .. } | TyKind::Param(..) => true,
        TyKind::Union(members) => members.iter().any(|&m| counted(db, program, m)),
    }
}

/// Where the value of an expression goes.
#[derive(Clone, Copy)]
enum Dest {
    Value(Local),
    /// Only its effects matter.
    Discard,
    /// It is the function's result: the expression is in tail position.
    Return,
}

/// An operator of the prelude that is an operation on numbers.
#[derive(Clone, Copy)]
enum Primitive {
    Arith {
        op: BinOp,
        ty: Builtin,
        checked: bool,
    },
    Negate(Builtin),
    Compare(CmpOp, Builtin),
}

/// A field of a record being built: the expression written for it, or
/// the last spread that has it.
struct Slot<'db> {
    name: crag_hir::Name<'db>,
    ty: Ty<'db>,
    given: Option<ExprId>,
    spread: Option<ExprId>,
}

/// The state of lowering one decision tree.
struct Match {
    subject: Local,
    /// The block each arm starts at, once a leaf reaches it.
    arms: Vec<Option<BlockId>>,
    guards: Vec<Option<ExprId>>,
    fail: BlockId,
}

pub struct MirBuilder<'a, 'db> {
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    body: &'a Body<'db>,
    types: &'a InferenceResult<'db>,
    locals: Vec<LocalDecl<'db>>,
    blocks: Vec<(Vec<Statement<'db>>, Option<Terminator<'db>>)>,
    current: BlockId,
    bindings: HashMap<BindingId, Local>,
    unsupported: Vec<(ExprId, &'static str)>,
    params: usize,
    result: Ty<'db>,
    bool_ty: Ty<'db>,
    true_ty: Ty<'db>,
    false_ty: Ty<'db>,
}

impl<'a, 'db> MirBuilder<'a, 'db> {
    fn new(
        db: &'db dyn Db,
        program: Program,
        owner: Owner<'db>,
        body: &'a Body<'db>,
        types: &'a InferenceResult<'db>,
    ) -> Self {
        let named = |name: &str| match prelude_item(db, program, name) {
            Some(item) => Ty::new(db, TyKind::Named(item, Vec::new())),
            None => Ty::error(db),
        };
        let (true_ty, false_ty) = (named("True"), named("False"));
        let bool_ty = match prelude_item(db, program, "Bool") {
            Some(_) => crag_types::join(db, program, true_ty, false_ty),
            None => Ty::error(db),
        };
        let mut b = MirBuilder {
            db,
            program,
            owner,
            body,
            types,
            locals: Vec::new(),
            blocks: Vec::new(),
            current: BlockId(0),
            bindings: HashMap::new(),
            unsupported: Vec::new(),
            params: body.params.len(),
            result: types.result.unwrap_or_else(|| Ty::unit(db)),
            bool_ty,
            true_ty,
            false_ty,
        };
        for param in &body.params {
            b.binding(param.binding);
        }
        b.current = b.new_block();
        b
    }

    /// Prunes the blocks no path reaches and the locals no block uses, and
    /// goes past blocks that only jump.
    fn finish(mut self) -> MirBody<'db> {
        let forward: Vec<BlockId> = (0..self.blocks.len())
            .map(|b| {
                let mut b = BlockId(b as u32);
                for _ in 0..self.blocks.len() {
                    match &self.blocks[b.index()] {
                        (statements, Some(Terminator::Jump(next))) if statements.is_empty() => {
                            b = *next
                        }
                        _ => break,
                    }
                }
                b
            })
            .collect();
        for (_, terminator) in &mut self.blocks {
            for s in terminator.iter_mut().flat_map(Terminator::successors_mut) {
                *s = forward[s.index()];
            }
        }
        let mut order = Vec::new();
        let mut seen = vec![false; self.blocks.len()];
        let mut stack = vec![0];
        while let Some(b) = stack.pop() {
            if std::mem::replace(&mut seen[b], true) {
                continue;
            }
            order.push(b);
            let term = self.blocks[b].1.as_ref().expect("reachable blocks end");
            stack.extend(term.successors().iter().rev().map(|s| s.index()));
        }
        order.sort_unstable();
        let mut renumber = vec![BlockId(u32::MAX); self.blocks.len()];
        for (new, &old) in order.iter().enumerate() {
            renumber[old] = BlockId(new as u32);
        }
        let mut blocks: Vec<Block<'db>> = Vec::new();
        let mut old_blocks: Vec<_> = self.blocks.into_iter().map(Some).collect();
        for &old in &order {
            let (statements, terminator) = old_blocks[old].take().expect("each block once");
            let mut terminator = terminator.expect("reachable blocks end");
            for s in terminator.successors_mut() {
                *s = renumber[s.index()];
            }
            blocks.push(Block {
                statements,
                terminator,
            });
        }
        let mut used = vec![false; self.locals.len()];
        used[..self.params].fill(true);
        for block in &mut blocks {
            for s in &mut block.statements {
                for l in s.locals_mut() {
                    used[l.index()] = true;
                }
            }
            for l in block.terminator.locals_mut() {
                used[l.index()] = true;
            }
        }
        let mut map = vec![Local(u32::MAX); self.locals.len()];
        let mut locals = Vec::new();
        for (i, decl) in self.locals.into_iter().enumerate() {
            if used[i] {
                map[i] = Local(locals.len() as u32);
                locals.push(decl);
            }
        }
        for block in &mut blocks {
            for s in &mut block.statements {
                for l in s.locals_mut() {
                    *l = map[l.index()];
                }
            }
            for l in block.terminator.locals_mut() {
                *l = map[l.index()];
            }
        }
        MirBody {
            params: self.params,
            locals,
            blocks,
            result: self.result,
            bool_ty: self.bool_ty,
            unsupported: self.unsupported,
        }
    }

    // Blocks and locals.

    fn new_block(&mut self) -> BlockId {
        self.blocks.push((Vec::new(), None));
        BlockId(self.blocks.len() as u32 - 1)
    }

    fn switch_to(&mut self, block: BlockId) {
        self.current = block;
    }

    /// Ends the current block. What follows goes to a block no path
    /// reaches until the caller switches to another.
    fn terminate(&mut self, terminator: Terminator<'db>) {
        let slot = &mut self.blocks[self.current.index()].1;
        assert!(slot.is_none(), "a block ends once");
        *slot = Some(terminator);
        self.current = self.new_block();
    }

    fn push(&mut self, statement: Statement<'db>) {
        self.blocks[self.current.index()].0.push(statement);
    }

    fn local(&mut self, ty: Ty<'db>, binding: Option<BindingId>) -> Local {
        let counted = counted(self.db, self.program, ty);
        let binding = binding.and_then(|b| Some((b, self.body.binding(b).name?)));
        self.locals.push(LocalDecl {
            ty,
            binding,
            counted,
        });
        Local(self.locals.len() as u32 - 1)
    }

    fn temp(&mut self, ty: Ty<'db>) -> Local {
        self.local(ty, None)
    }

    /// The local of a binding.
    fn binding(&mut self, binding: BindingId) -> Local {
        if let Some(&local) = self.bindings.get(&binding) {
            return local;
        }
        let ty = self
            .types
            .binding(binding)
            .unwrap_or_else(|| Ty::error(self.db));
        let local = self.local(ty, Some(binding));
        self.bindings.insert(binding, local);
        local
    }

    fn assign(&mut self, ty: Ty<'db>, rvalue: Rvalue<'db>) -> Operand<'db> {
        let local = self.temp(ty);
        self.push(Statement::Assign(local, rvalue));
        Operand::Local(local)
    }

    /// The operand in a local, so that places can start at it.
    fn materialize(&mut self, op: Operand<'db>, ty: Ty<'db>) -> Local {
        match op {
            Operand::Local(l) => l,
            op => match self.assign(ty, Rvalue::Use(op)) {
                Operand::Local(l) => l,
                Operand::Const(_) => unreachable!("assign gives a local"),
            },
        }
    }

    /// The operand as a value of `to`, which its type `from` fits.
    fn coerce(&mut self, op: Operand<'db>, from: Ty<'db>, to: Ty<'db>) -> Operand<'db> {
        match self.converts(from, to) {
            true => {
                let op = self.typed(op, from);
                self.assign(to, Rvalue::Convert(op))
            }
            false => op,
        }
    }

    /// The operand as one whose type is known: a constant typed only by
    /// where it goes, such as a number, goes into a local of `ty` first,
    /// so that a conversion knows what it converts from.
    fn typed(&mut self, op: Operand<'db>, ty: Ty<'db>) -> Operand<'db> {
        match op {
            Operand::Const(Constant::Tag(_) | Constant::Unit) | Operand::Local(_) => op,
            Operand::Const(_) => self.assign(ty, Rvalue::Use(op)),
        }
    }

    /// Assigns the operand to a local.
    fn assign_to(&mut self, local: Local, op: Operand<'db>, from: Ty<'db>) {
        let to = self.locals[local.index()].ty;
        if self.converts(from, to) {
            let op = self.typed(op, from);
            self.push(Statement::Assign(local, Rvalue::Convert(op)));
        } else if op != Operand::Local(local) {
            self.push(Statement::Assign(local, Rvalue::Use(op)));
        }
    }

    /// Whether a value of `from` must be converted to be one of `to`.
    fn converts(&self, from: Ty<'db>, to: Ty<'db>) -> bool {
        let db = self.db;
        from != to && !from.is_error(db) && !to.is_error(db) && !from.is_never(db)
    }

    fn ty(&self, expr: ExprId) -> Ty<'db> {
        self.types.expr(expr).unwrap_or_else(|| Ty::error(self.db))
    }

    fn int(&self) -> Ty<'db> {
        Ty::builtin(self.db, Builtin::Int)
    }

    fn unit(&self) -> Operand<'db> {
        Operand::Const(Constant::Unit)
    }

    fn trap(&mut self, kind: TrapKind, site: Option<ExprId>) -> Operand<'db> {
        self.terminate(Terminator::Trap { kind, site });
        self.unit()
    }

    fn unsupported(&mut self, expr: ExprId, what: &'static str) -> Operand<'db> {
        self.unsupported.push((expr, what));
        self.trap(TrapKind::Unsupported, Some(expr))
    }

    // Expressions.

    /// Evaluates an expression into `dest`.
    fn eval(&mut self, expr: ExprId, dest: Dest) {
        let body = self.body;
        match body.expr(expr) {
            Expr::Block { stmts, tail } => {
                for stmt in stmts {
                    self.stmt(stmt);
                }
                match tail {
                    Some(tail) => self.eval(*tail, dest),
                    None => {
                        let unit = Ty::unit(self.db);
                        self.finish_dest(self.unit(), unit, dest);
                    }
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
            Expr::Call { .. } | Expr::MethodCall { .. } | Expr::TypedCall { .. }
                if matches!(dest, Dest::Return) =>
            {
                let op = self.call(expr, true);
                self.finish_dest(op, self.ty(expr), dest);
            }
            Expr::Field { .. } if matches!(dest, Dest::Return) && self.is_call(expr) => {
                let op = self.call(expr, true);
                self.finish_dest(op, self.ty(expr), dest);
            }
            _ => {
                let op = self.expr(expr);
                self.finish_dest(op, self.ty(expr), dest);
            }
        }
    }

    fn finish_dest(&mut self, op: Operand<'db>, ty: Ty<'db>, dest: Dest) {
        match dest {
            Dest::Value(local) => self.assign_to(local, op, ty),
            Dest::Discard => {}
            // A test gives no value.
            Dest::Return if self.types.result.is_none() => {
                self.terminate(Terminator::Return(self.unit()));
            }
            Dest::Return => {
                let op = self.coerce(op, ty, self.result);
                self.terminate(Terminator::Return(op));
            }
        }
    }

    /// Ends a branch that gives a value at the join.
    fn join(&mut self, dest: Dest, join: BlockId) {
        if !matches!(dest, Dest::Return) {
            self.terminate(Terminator::Jump(join));
        }
    }

    fn is_call(&self, expr: ExprId) -> bool {
        self.types.callee(expr).is_some()
    }

    /// Evaluates an expression into an operand.
    fn expr(&mut self, expr: ExprId) -> Operand<'db> {
        let db = self.db;
        let body = self.body;
        let ty = self.ty(expr);
        match body.expr(expr) {
            Expr::Missing => self.trap(TrapKind::Error, Some(expr)),
            Expr::Hole => self.trap(TrapKind::Hole, Some(expr)),
            Expr::Literal(literal) => Operand::Const(self.literal(literal, ty, false)),
            Expr::Str(parts) => {
                let mut ops = Vec::new();
                for part in parts {
                    match part {
                        StrPart::Text(text) => {
                            ops.push(Operand::Const(Constant::Str(text.clone())))
                        }
                        StrPart::Expr(e) if self.ty(*e) == ty => ops.push(self.expr(*e)),
                        StrPart::Expr(e) => {
                            return self.unsupported(*e, "interpolations of other types than Str");
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
                self.assign(ty, Rvalue::Record { ty, fields: values })
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
            Expr::Grid(_) => self.unsupported(expr, "grids"),
            Expr::TypeArgs { .. } => self.unsupported(expr, "type arguments"),
            Expr::Closure { .. } => self.unsupported(expr, "closures"),
            Expr::Pass => self.unsupported(expr, "`pass`"),
            Expr::Atomic(_) => self.unsupported(expr, "`atomic` blocks"),
            Expr::Lazy(_) => self.unsupported(expr, "`lazy`"),
        }
    }

    /// The local an expression's value is in.
    fn place_of(&mut self, expr: ExprId) -> Local {
        let op = self.expr(expr);
        self.materialize(op, self.ty(expr))
    }

    fn literal(&self, literal: &Literal, ty: Ty<'db>, negative: bool) -> Constant<'db> {
        let sign: i128 = if negative { -1 } else { 1 };
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
            if self.body.binding(binding).kind == BindingKind::Fn {
                return self.unsupported(expr, "local functions");
            }
            // A narrowed binding is read as the member a test found
            // (§3.13.4).
            let local = self.binding(binding);
            let (from, to) = (self.locals[local.index()].ty, self.ty(expr));
            return match self.converts(from, to) {
                true => self.assign(to, Rvalue::Convert(Operand::Local(local))),
                false => Operand::Local(local),
            };
        }
        if self.is_call(expr) {
            return self.unsupported(expr, "functions as values");
        }
        match item {
            Some(Resolution::Value { value: Some(v), .. }) => {
                self.assign(self.ty(expr), Rvalue::Global(*v))
            }
            Some(Resolution::Type(_)) => Operand::Const(Constant::Tag(self.ty(expr))),
            _ => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    fn index(&mut self, expr: ExprId, base: ExprId, args: &[ExprId]) -> Operand<'db> {
        let db = self.db;
        let ty = self.ty(expr);
        let base_ty = self.ty(base);
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
            Some((Builtin::Map, [k, _])) => {
                let key = self.expr(*arg);
                let key = self.coerce(key, self.ty(*arg), *k);
                let map = Place::local(container);
                self.assign(ty, Rvalue::MapGet { map, key })
            }
            _ => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    fn compare(
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
    fn branch_on(&mut self, cond: ExprId, then: BlockId, otherwise: BlockId) {
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
                let target = self.types.types.get(ty.index()).copied().flatten();
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

    /// A call, a method call, or a field access that calls a function.
    fn call(&mut self, expr: ExprId, tail: bool) -> Operand<'db> {
        let body = self.body;
        let (receiver, args, fields): (Option<ExprId>, &[ExprId], Option<&[FieldArg<'db>]>) =
            match body.expr(expr) {
                Expr::Call { args, fields, .. } | Expr::TypedCall { args, fields, .. } => {
                    (None, args, fields.as_deref())
                }
                Expr::MethodCall {
                    receiver,
                    args,
                    fields,
                    ..
                } => (Some(*receiver), args, fields.as_deref()),
                Expr::Field { receiver, .. } => (Some(*receiver), &[], None),
                _ => unreachable!("only calls are called"),
            };
        let positional: Vec<ExprId> = receiver.into_iter().chain(args.iter().copied()).collect();
        match self.types.callee(expr).cloned() {
            Some(Callee::Function(function)) => {
                self.call_function(expr, function, &positional, fields, tail)
            }
            Some(Callee::Construct(ty)) => self.construct(expr, ty, &positional, fields),
            _ => self.unsupported(expr, "calls of function values"),
        }
    }

    fn call_function(
        &mut self,
        expr: ExprId,
        function: ItemId<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        tail: bool,
    ) -> Operand<'db> {
        let db = self.db;
        if fields.is_none()
            && let Some(primitive) = self.primitive(function)
        {
            return self.primitive_call(expr, primitive, positional);
        }
        let sig = signature(db, self.program, function);
        if sig.type_params > 0 {
            return self.unsupported(expr, "calls of generic functions");
        }
        let Some(args) = self.arguments(sig, positional, fields) else {
            return self.unsupported(expr, "default arguments");
        };
        let func = InstanceKey::new(db, Owner::Item(function), Vec::new());
        let ty = self.ty(expr);
        if tail && ty == self.result {
            self.terminate(Terminator::TailCall {
                func,
                args,
                site: expr,
            });
            return self.unit();
        }
        let dst = self.temp(ty);
        let target = self.new_block();
        self.terminate(Terminator::Call {
            func,
            args,
            dst,
            target,
            site: expr,
        });
        self.switch_to(target);
        Operand::Local(dst)
    }

    /// The arguments for the parameters, in the order they are written:
    /// positional, then named, or named arguments building the last
    /// parameter, a record (§5.6.2). None when a parameter takes its
    /// default.
    fn arguments(
        &mut self,
        sig: &Signature<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Option<Vec<Operand<'db>>> {
        let db = self.db;
        let params = &sig.params;
        let named: Option<Vec<_>> = fields
            .unwrap_or(&[])
            .iter()
            .map(|f| match f {
                FieldArg::Field { path, value } if path.len() == 1 => Some((path[0], *value)),
                _ => None,
            })
            .collect();
        let mut slots: Vec<Option<ExprId>> = vec![None; params.len()];
        let mut fits = positional.len() <= params.len();
        if fits {
            for (i, &arg) in positional.iter().enumerate() {
                slots[i] = Some(arg);
            }
            match &named {
                Some(named) => {
                    for &(name, value) in named {
                        match params.iter().position(|p| p.name == Some(name)) {
                            Some(i) if slots[i].is_none() => slots[i] = Some(value),
                            _ => fits = false,
                        }
                    }
                }
                None => fits = false,
            }
        }
        if fits && slots.iter().all(Option::is_some) {
            let mut ops: Vec<Option<Operand<'db>>> = vec![None; params.len()];
            let order = positional
                .iter()
                .chain(named.iter().flatten().map(|(_, v)| v));
            for &arg in order {
                let i = slots.iter().position(|s| *s == Some(arg))?;
                let op = self.expr(arg);
                ops[i] = Some(self.coerce(op, self.ty(arg), params[i].ty));
            }
            return ops.into_iter().collect();
        }
        let last = params.last()?;
        let builds = params.len() == positional.len() + 1
            && fields.is_some()
            && fields_of(db, self.program, last.ty).is_some();
        if !builds || !self.record_fits(last.ty, &[], fields.unwrap_or(&[])) {
            return None;
        }
        let mut ops = Vec::new();
        for (&arg, param) in positional.iter().zip(params) {
            let op = self.expr(arg);
            ops.push(self.coerce(op, self.ty(arg), param.ty));
        }
        let site = positional.first().copied();
        ops.push(self.record_value(site, last.ty, &[], fields.unwrap_or(&[])));
        Some(ops)
    }

    /// The operation an operator function of the prelude stands for, if
    /// it is one: a builtin on numbers, or `equals` of strings and bytes.
    fn primitive(&self, function: ItemId<'db>) -> Option<Primitive> {
        let db = self.db;
        if function.module(db).path(db) != PRELUDE
            || hir_body(db, self.program, Owner::Item(function))
                .root
                .is_some()
        {
            return None;
        }
        let sig = signature(db, self.program, function);
        let builtin = |ty: Ty<'db>| match ty.kind(db) {
            TyKind::Builtin(b, args) if args.is_empty() => Some(*b),
            _ => None,
        };
        let params: Vec<Builtin> = sig
            .params
            .iter()
            .map(|p| builtin(p.ty))
            .collect::<Option<_>>()?;
        let result = sig.result.and_then(builtin);
        let number =
            |b: Builtin| b.int_range().is_some() || matches!(b, Builtin::Float | Builtin::Fixed(_));
        let name = function.name(db).text(db).as_str();
        let arith = |op: BinOp, checked: bool| -> Option<Primitive> {
            let [a, b] = params.as_slice() else {
                return None;
            };
            let (a, b, ty) = (*a, *b, result?);
            let fits = match (a, b) {
                _ if !number(a) || !number(b) => false,
                (Builtin::Fixed(_), Builtin::Fixed(_)) => {
                    a == b && matches!(op, BinOp::Add | BinOp::Sub | BinOp::Rem)
                }
                (Builtin::Fixed(_), _) | (_, Builtin::Fixed(_)) => {
                    op == BinOp::Mul && b.int_range().or(a.int_range()).is_some()
                }
                _ => a == b,
            };
            (fits && (checked || ty != Builtin::Float)).then_some(Primitive::Arith {
                op,
                ty,
                checked,
            })
        };
        let compare = |op: CmpOp| -> Option<Primitive> {
            let [a, b] = params.as_slice() else {
                return None;
            };
            let text = matches!(a, Builtin::Str | Builtin::Bytes) && op == CmpOp::Eq;
            let ordered = number(*a) || *a == Builtin::CodePoint;
            (a == b && (ordered || text)).then_some(Primitive::Compare(op, *a))
        };
        match name {
            "add" => arith(BinOp::Add, true),
            "subtract" => arith(BinOp::Sub, true),
            "multiply" => arith(BinOp::Mul, true),
            "divide" => arith(BinOp::Div, true),
            "remainder" => arith(BinOp::Rem, true),
            "addWrapping" => arith(BinOp::Add, false),
            "subtractWrapping" => arith(BinOp::Sub, false),
            "multiplyWrapping" => arith(BinOp::Mul, false),
            "negate" => match params.as_slice() {
                [a] if number(*a) => Some(Primitive::Negate(*a)),
                _ => None,
            },
            "equals" => compare(CmpOp::Eq),
            "lessThan" => compare(CmpOp::Lt),
            "lessOrEqual" => compare(CmpOp::Le),
            "greaterThan" => compare(CmpOp::Gt),
            "greaterOrEqual" => compare(CmpOp::Ge),
            _ => None,
        }
    }

    fn primitive_call(
        &mut self,
        expr: ExprId,
        primitive: Primitive,
        args: &[ExprId],
    ) -> Operand<'db> {
        let ty = self.ty(expr);
        match (primitive, args) {
            (Primitive::Arith { op, ty: b, checked }, [x, y]) => {
                let (a, c) = (self.expr(*x), self.expr(*y));
                let check = checked.then_some(expr);
                self.assign(
                    ty,
                    Rvalue::Binary {
                        op,
                        ty: b,
                        a,
                        b: c,
                        check,
                    },
                )
            }
            (Primitive::Negate(b), [x]) => {
                // `-1` is a constant, so `Int8.min` can be written.
                if let Expr::Literal(literal) = self.body.expr(*x) {
                    return Operand::Const(self.literal(literal, ty, true));
                }
                let a = self.expr(*x);
                let rvalue = match b {
                    // -0.0 must stay negative zero; -1.0 * x keeps the sign.
                    Builtin::Float => Rvalue::Binary {
                        op: BinOp::Mul,
                        ty: b,
                        a: Operand::Const(Constant::Float((-1.0f64).to_bits())),
                        b: a,
                        check: Some(expr),
                    },
                    _ => Rvalue::Binary {
                        op: BinOp::Sub,
                        ty: b,
                        a: int(0),
                        b: a,
                        check: Some(expr),
                    },
                };
                self.assign(ty, rvalue)
            }
            (Primitive::Compare(op, b), [x, y]) => {
                let (a, c) = (self.expr(*x), self.expr(*y));
                self.assign(ty, Rvalue::Compare { op, ty: b, a, b: c })
            }
            _ => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    /// A call of a type: a tag's value, or a record built from arguments.
    fn construct(
        &mut self,
        expr: ExprId,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Operand<'db> {
        let db = self.db;
        if let TyKind::Named(item, _) = ty.kind(db)
            && let TypeDefKind::Tag = type_def(db, self.program, *item).kind
        {
            return Operand::Const(Constant::Tag(ty));
        }
        if fields_of(db, self.program, ty).is_none() {
            return self.unsupported(expr, "constructions of collections");
        }
        self.record(expr, ty, positional, fields.unwrap_or(&[]))
    }

    fn record(
        &mut self,
        expr: ExprId,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> Operand<'db> {
        if ty == Ty::unit(self.db) {
            return self.unit();
        }
        if fields
            .iter()
            .any(|f| matches!(f, FieldArg::Field { path, .. } if path.len() > 1))
        {
            return self.unsupported(expr, "field paths");
        }
        if !self.record_fits(ty, positional, fields) {
            return self.unsupported(expr, "field defaults");
        }
        self.record_value(Some(expr), ty, positional, fields)
    }

    /// The fields of a record in the order of `fields_of`, each written,
    /// or taken from a spread.
    fn record_slots(
        &self,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> Option<Vec<Slot<'db>>> {
        let db = self.db;
        let all = fields_of(db, self.program, ty)?;
        let declared: Vec<_> = match declared_fields(db, self.program, ty) {
            Some(declared) => declared.into_iter().map(|(n, ..)| n).collect(),
            None => all.iter().map(|(n, _)| *n).collect(),
        };
        let mut slots = Vec::new();
        for &(name, field_ty) in &all {
            let given = positional
                .iter()
                .zip(&declared)
                .find(|(_, n)| **n == name)
                .map(|(e, _)| *e)
                .or_else(|| {
                    fields.iter().find_map(|f| match f {
                        FieldArg::Field { path, value } if path == &[name] => Some(*value),
                        _ => None,
                    })
                });
            let spread = fields.iter().rev().find_map(|f| match f {
                FieldArg::Spread(e) => fields_of(db, self.program, self.ty(*e))?
                    .iter()
                    .any(|(n, _)| *n == name)
                    .then_some(*e),
                _ => None,
            });
            slots.push(Slot {
                name,
                ty: field_ty,
                given,
                spread,
            });
        }
        Some(slots)
    }

    fn record_fits(&self, ty: Ty<'db>, positional: &[ExprId], fields: &[FieldArg<'db>]) -> bool {
        self.record_slots(ty, positional, fields)
            .is_some_and(|slots| {
                slots
                    .iter()
                    .all(|s| s.given.is_some() || s.spread.is_some())
            })
    }

    /// Builds a record that `record_fits`: the written values in their
    /// order, then the fields spreads give.
    fn record_value(
        &mut self,
        site: Option<ExprId>,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> Operand<'db> {
        let Some(slots) = self.record_slots(ty, positional, fields) else {
            return self.trap(TrapKind::Error, site);
        };
        let written = positional
            .iter()
            .copied()
            .chain(fields.iter().map(|f| match f {
                FieldArg::Field { value, .. } | FieldArg::Spread(value) => *value,
            }));
        let mut values: HashMap<ExprId, Operand<'db>> = HashMap::new();
        for e in written.collect::<Vec<_>>() {
            let op = self.expr(e);
            values.insert(e, op);
        }
        let mut spreads: HashMap<ExprId, Local> = HashMap::new();
        let mut out = Vec::new();
        for Slot {
            name,
            ty: field_ty,
            given,
            spread,
        } in slots
        {
            let op = match (given, spread) {
                (Some(e), _) => {
                    let op = values[&e].clone();
                    self.coerce(op, self.ty(e), field_ty)
                }
                (None, Some(s)) => {
                    let local = match spreads.get(&s) {
                        Some(&l) => l,
                        None => {
                            let l = self.materialize(values[&s].clone(), self.ty(s));
                            spreads.insert(s, l);
                            l
                        }
                    };
                    let from = fields_of(self.db, self.program, self.ty(s))
                        .and_then(|fs| fs.into_iter().find(|(n, _)| *n == name))
                        .map_or(field_ty, |(_, t)| t);
                    let place = Place {
                        local,
                        path: vec![Step::Field(name)],
                    };
                    let op = self.assign(from, Rvalue::Read(place));
                    self.coerce(op, from, field_ty)
                }
                (None, None) => return self.trap(TrapKind::Error, site),
            };
            out.push((name, op));
        }
        self.assign(ty, Rvalue::Record { ty, fields: out })
    }

    // Statements.

    fn stmt(&mut self, stmt: &Stmt) {
        let body = self.body;
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
                otherwise,
            } => {
                let test = ty.map(|t| self.types.types.get(t.index()).copied().flatten());
                let op = self.expr(*value);
                match test {
                    Some(None) => {
                        self.trap(TrapKind::Error, Some(*value));
                    }
                    Some(Some(test)) => self.tested(*pat, op, self.ty(*value), test, *otherwise),
                    None => self.matched(*pat, op, self.ty(*value), Some(*otherwise)),
                }
            }
            Stmt::Bind { binding, value, .. } => {
                if body.binding(*binding).kind != BindingKind::Var {
                    self.unsupported(*value, "`ref` and `ext` bindings");
                    return;
                }
                let local = self.binding(*binding);
                let op = self.expr(*value);
                self.assign_to(local, op, self.ty(*value));
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
            } => self.for_loop(*pat, *iterable, *body),
            Stmt::Return(Some(e)) => self.eval(*e, Dest::Return),
            Stmt::Return(None) => {
                let unit = Ty::unit(self.db);
                self.finish_dest(self.unit(), unit, Dest::Return);
            }
            Stmt::Emit { value, .. } => {
                self.unsupported(*value, "`emit`");
            }
            Stmt::On { handler, .. } => {
                self.unsupported(*handler, "`on` handlers");
            }
            Stmt::Fn { function, .. } => {
                if let Some(e) = function.body {
                    self.unsupported(e, "local functions");
                }
            }
        }
    }

    /// Matches a value against the pattern of a `let`, a `let … else` or
    /// a `for`, binding its names.
    fn matched(&mut self, pat: PatId, op: Operand<'db>, ty: Ty<'db>, otherwise: Option<ExprId>) {
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
        let Some(tree) = decision_tree(self.db, self.program, self.owner, ty, &[(pat, false)])
        else {
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
        if let Some(otherwise) = otherwise {
            // The `else` leaves, so its end is never reached (§7.1.1).
            self.eval(otherwise, Dest::Discard);
        }
        self.trap(TrapKind::NoMatch, otherwise);
        self.switch_to(cont);
    }

    /// `let pat: T = value else …`: the value is tested to be a `T`
    /// before it is matched (§7.1.1).
    fn tested(
        &mut self,
        pat: PatId,
        op: Operand<'db>,
        ty: Ty<'db>,
        test: Ty<'db>,
        otherwise: ExprId,
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
        self.eval(otherwise, Dest::Discard);
        self.trap(TrapKind::NoMatch, Some(otherwise));
        self.switch_to(fits);
        let narrowed = self.temp(test);
        self.assign_to(narrowed, Operand::Local(subject), ty);
        self.matched(pat, Operand::Local(narrowed), test, Some(otherwise));
    }

    fn for_loop(&mut self, pat: PatId, iterable: ExprId, body: ExprId) {
        let db = self.db;
        let ty = self.ty(iterable);
        let range = |name: &str| prelude_item(db, self.program, name);
        let (kind, element) = match ty.kind(db) {
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

    fn case(&mut self, expr: ExprId, subject: ExprId, arms: &[Arm], dest: Dest) {
        let local = self.place_of(subject);
        let ty = self.ty(subject);
        let spec: Vec<(PatId, bool)> = arms.iter().map(|a| (a.pat, a.guard.is_some())).collect();
        let Some(tree) = decision_tree(self.db, self.program, self.owner, ty, &spec) else {
            self.trap(TrapKind::Error, Some(expr));
            return;
        };
        let fail = self.new_block();
        let mut m = Match {
            subject: local,
            arms: vec![None; arms.len()],
            guards: arms.iter().map(|a| a.guard).collect(),
            fail,
        };
        self.lower_decision_tree(&tree, &mut m);
        self.switch_to(fail);
        self.trap(TrapKind::NoMatch, Some(expr));
        let join = self.new_block();
        for (arm, block) in arms.iter().zip(m.arms) {
            if let Some(block) = block {
                self.switch_to(block);
                self.eval(arm.body, dest);
                self.join(dest, join);
            }
        }
        self.switch_to(join);
    }

    /// Lowers a decision tree into tests of the subject, ending the
    /// current block. A leaf binds its arm's names and goes to the arm.
    fn lower_decision_tree(&mut self, tree: &DecisionTree<'db>, m: &mut Match) {
        let db = self.db;
        match tree {
            DecisionTree::Fail => self.terminate(Terminator::Jump(m.fail)),
            DecisionTree::Leaf { arm, bindings } => {
                self.bind(m.subject, bindings);
                let target = self.arm_block(m, *arm);
                self.terminate(Terminator::Jump(target));
            }
            DecisionTree::Guard {
                arm,
                bindings,
                otherwise,
            } => {
                self.bind(m.subject, bindings);
                let target = self.arm_block(m, *arm);
                let next = self.new_block();
                let guard = m.guards[*arm].expect("a guarded arm has a guard");
                self.branch_on(guard, target, next);
                self.switch_to(next);
                self.lower_decision_tree(otherwise, m);
            }
            DecisionTree::Switch {
                position,
                cases,
                default,
            } => {
                let place = self.place(m.subject, position);
                let mut targets: Vec<(Ty<'db>, BlockId)> =
                    cases.iter().map(|(t, _)| (*t, self.new_block())).collect();
                let otherwise = match default {
                    Some(_) => self.new_block(),
                    None => targets.pop().map_or(m.fail, |(_, b)| b),
                };
                let blocks: Vec<BlockId> = targets.iter().map(|(_, b)| *b).collect();
                if targets.is_empty() {
                    self.terminate(Terminator::Jump(otherwise));
                } else {
                    self.terminate(Terminator::Switch {
                        place,
                        cases: targets,
                        otherwise,
                    });
                }
                for (block, (_, sub)) in blocks.iter().zip(cases) {
                    self.switch_to(*block);
                    self.lower_decision_tree(sub, m);
                }
                self.switch_to(otherwise);
                match default {
                    Some(default) => self.lower_decision_tree(default, m),
                    None => match cases.last() {
                        Some((_, sub)) => self.lower_decision_tree(sub, m),
                        None => self.terminate(Terminator::Jump(m.fail)),
                    },
                }
            }
            DecisionTree::Ranges {
                position,
                ty,
                cases,
                default,
            } => {
                let builtin = ty.as_builtin(db).map_or(Builtin::Int, |(b, _)| b);
                let value = self.read(m.subject, position, *ty);
                for (k, (lo, hi, sub)) in cases.iter().enumerate() {
                    if k + 1 == cases.len() && default.is_none() {
                        self.lower_decision_tree(sub, m);
                        return;
                    }
                    let (hit, miss) = (self.new_block(), self.new_block());
                    self.interval(value.clone(), builtin, *lo, *hi, hit, miss);
                    self.switch_to(hit);
                    self.lower_decision_tree(sub, m);
                    self.switch_to(miss);
                }
                match default {
                    Some(default) => self.lower_decision_tree(default, m),
                    None => self.terminate(Terminator::Jump(m.fail)),
                }
            }
            DecisionTree::Values {
                position,
                ty,
                cases,
                default,
            } => {
                let builtin = ty.as_builtin(db).map_or(Builtin::Str, |(b, _)| b);
                let value = self.read(m.subject, position, *ty);
                for (literal, sub) in cases {
                    let constant = match literal {
                        Value::Str(s) => Constant::Str(s.clone()),
                        Value::Bytes(b) => Constant::Bytes(b.clone()),
                        Value::Float(bits) => Constant::Float(*bits),
                    };
                    let same =
                        self.compare(CmpOp::Eq, builtin, value.clone(), Operand::Const(constant));
                    let (hit, miss) = (self.new_block(), self.new_block());
                    self.terminate(Terminator::Branch {
                        cond: same,
                        then: hit,
                        otherwise: miss,
                    });
                    self.switch_to(hit);
                    self.lower_decision_tree(sub, m);
                    self.switch_to(miss);
                }
                self.lower_decision_tree(default, m);
            }
            DecisionTree::Length {
                position,
                cases,
                default,
            } => {
                let place = self.place(m.subject, position);
                let len = self.assign(self.int(), Rvalue::Len(place));
                for (k, (length, sub)) in cases.iter().enumerate() {
                    if k + 1 == cases.len() && default.is_none() {
                        self.lower_decision_tree(sub, m);
                        return;
                    }
                    let fits = match length {
                        ListLen::Fixed(n) => {
                            self.compare(CmpOp::Eq, Builtin::Int, len.clone(), int(*n as i128))
                        }
                        ListLen::AtLeast { prefix, suffix } => self.compare(
                            CmpOp::Ge,
                            Builtin::Int,
                            len.clone(),
                            int((prefix + suffix) as i128),
                        ),
                    };
                    let (hit, miss) = (self.new_block(), self.new_block());
                    self.terminate(Terminator::Branch {
                        cond: fits,
                        then: hit,
                        otherwise: miss,
                    });
                    self.switch_to(hit);
                    self.lower_decision_tree(sub, m);
                    self.switch_to(miss);
                }
                match default {
                    Some(default) => self.lower_decision_tree(default, m),
                    None => self.terminate(Terminator::Jump(m.fail)),
                }
            }
        }
    }

    /// Goes to `hit` if the value lies between the ends, and to `miss` if
    /// not.
    fn interval(
        &mut self,
        value: Operand<'db>,
        ty: Builtin,
        lo: Option<i128>,
        hi: Option<i128>,
        hit: BlockId,
        miss: BlockId,
    ) {
        let mut tests = match (lo, hi) {
            (Some(l), Some(h)) if l == h => vec![(CmpOp::Eq, l)],
            _ => {
                let lo = lo.map(|l| (CmpOp::Ge, l));
                let hi = hi.map(|h| (CmpOp::Le, h));
                lo.into_iter().chain(hi).collect()
            }
        };
        let Some(last) = tests.pop() else {
            self.terminate(Terminator::Jump(hit));
            return;
        };
        for (op, bound) in tests {
            let ok = self.compare(op, ty, value.clone(), int(bound));
            let next = self.new_block();
            self.terminate(Terminator::Branch {
                cond: ok,
                then: next,
                otherwise: miss,
            });
            self.switch_to(next);
        }
        let ok = self.compare(last.0, ty, value, int(last.1));
        self.terminate(Terminator::Branch {
            cond: ok,
            then: hit,
            otherwise: miss,
        });
    }

    fn arm_block(&mut self, m: &mut Match, arm: usize) -> BlockId {
        match m.arms[arm] {
            Some(block) => block,
            None => {
                let block = self.new_block();
                m.arms[arm] = Some(block);
                block
            }
        }
    }

    fn place(&self, subject: Local, position: &Position<'db>) -> Place<'db> {
        Place {
            local: subject,
            path: position.0.clone(),
        }
    }

    /// The value at a position, which is not a slice.
    fn read(&mut self, subject: Local, position: &Position<'db>, ty: Ty<'db>) -> Operand<'db> {
        if position.0.is_empty() {
            return Operand::Local(subject);
        }
        let place = self.place(subject, position);
        self.assign(ty, Rvalue::Read(place))
    }

    /// The type of the value at a path into a local.
    fn place_ty(&self, local: Local, path: &[Step<'db>]) -> Ty<'db> {
        let db = self.db;
        let mut ty = self.locals[local.index()].ty;
        for step in path {
            ty = match step {
                Step::As(t) => *t,
                Step::Field(name) => fields_of(db, self.program, ty)
                    .and_then(|fs| fs.into_iter().find(|(n, _)| n == name))
                    .map_or_else(|| Ty::error(db), |(_, t)| t),
                Step::Elem(_) | Step::ElemBack(_) => match ty.as_builtin(db) {
                    Some((Builtin::List, [element])) => *element,
                    _ => Ty::error(db),
                },
                Step::Slice { .. } => ty,
            };
        }
        ty
    }

    fn bind(&mut self, subject: Local, bindings: &[(BindingId, Position<'db>)]) {
        for (binding, position) in bindings {
            let local = self.binding(*binding);
            let path = &position.0;
            let (rvalue, ty) = match path.last() {
                None => {
                    let ty = self.locals[subject.index()].ty;
                    self.assign_to(local, Operand::Local(subject), ty);
                    continue;
                }
                Some(Step::Slice { front, back }) => {
                    let list = Place {
                        local: subject,
                        path: path[..path.len() - 1].to_vec(),
                    };
                    let ty = self.place_ty(subject, path);
                    let rvalue = Rvalue::Slice {
                        list,
                        front: *front,
                        back: *back,
                    };
                    (rvalue, ty)
                }
                Some(_) => (
                    Rvalue::Read(self.place(subject, position)),
                    self.place_ty(subject, path),
                ),
            };
            if ty == self.locals[local.index()].ty {
                self.push(Statement::Assign(local, rvalue));
            } else {
                let value = self.assign(ty, rvalue);
                self.assign_to(local, value, ty);
            }
        }
    }
}

fn int<'db>(n: i128) -> Operand<'db> {
    Operand::Const(Constant::Int(n))
}
