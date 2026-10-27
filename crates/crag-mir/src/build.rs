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
//!
//! A closure becomes a function value: the code of its body, an instance
//! of its owner, and an environment record of what it captures (§11.5.9).
//! The code takes the environment first and reads the captured values out
//! of it. The environment of a closure that does not outlive its frame
//! goes on the side stack and borrows what it captures; any other goes on
//! the heap. A local function is a closure with a name, and a declared
//! function used as a value gets code of its own that calls it.

use std::collections::HashMap;

use crag_db::Db;
use crag_hir::{
    Arm, BindingId, BindingKind, Body, EmitKind, Expr, ExprId, FieldArg, ItemId, ItemKind, Literal,
    LocalFn, Name, Owner, PRELUDE, Pat, PatId, Program, Resolution, Stmt, StrPart, hir_body,
    lower_body,
};
use crag_types::{
    Builtin, Callee, DecisionTree, Dispatch, EscapeLevel, Filling, Handler, HandlerCode,
    InferenceResult, Instance, ListLen, Position, SigParam, Signature, Step, Ty, TyKind,
    TypeDefKind, Value, body_types, decision_tree_with, declared_fields, dispose_handler,
    fields_of, lifecycle_handler, literal_value, prelude_item, result_type, signature, subst,
    type_def, type_header, value_type,
};

use crate::ir::{
    BinOp, Block, BlockId, ClosurePlacement, CmpOp, Constant, Intrinsic, Local, LocalDecl, MirBody,
    Operand, Place, Rvalue, Statement, Terminator, TrapKind,
};
use crate::{Entry, InstanceKey};

/// The graph of an instance: a function, test or module-level value, or
/// the code of a closure in one, before checks and reference counts are
/// explicit. In an instance of a generic function every type has the
/// instance's type arguments in place of the type parameters, and a call
/// of a slot calls the function that fills it (§11.5.10). None for what
/// has no body, and for a generic function without type arguments.
pub fn build<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
) -> Option<MirBody<'db>> {
    let (owner, entry) = (*instance.owner(db), *instance.entry(db));
    if let Owner::Item(item) = owner {
        let params = match *item.kind(db) {
            ItemKind::Function => signature(db, program, item).type_params,
            // A type has code only for what its declaration holds.
            ItemKind::Type if entry != Entry::Body => type_header(db, program, item).params.len(),
            kind if kind.is_value() => 0,
            _ => return None,
        };
        if params != instance.args(db).len() {
            return None;
        }
    }
    let lowered = lower_body(db, program, owner);
    let types = body_types(db, program, owner);
    let mut b = MirBuilder::new(db, program, instance, &lowered.body, types);
    let ok = lowered.errors.is_empty() && types.errors.is_empty();
    let start = match entry {
        Entry::Body => b.body_entry(lowered.body.root?),
        Entry::Closure(frame) => b.closure_entry(frame),
        Entry::Function(expr) => b.function_entry(expr),
        Entry::Default(expr) => b.default_entry(expr),
        Entry::Dispose => b.dispose_entry(),
    };
    match start {
        Some(start) if ok => start(&mut b),
        _ => {
            b.terminate(Terminator::Trap {
                kind: TrapKind::Error,
                site: None,
            });
        }
    }
    Some(b.finish())
}

/// What a builder does once its parameters are in place.
type Start<'a, 'db> = Box<dyn FnOnce(&mut MirBuilder<'a, 'db>) + 'a>;

/// Where a closure's environment goes: on the side stack when the closure
/// does not outlive its frame's use of it (§11.5.8), unless it is made in
/// a loop, which would push one per iteration; on the heap otherwise. A
/// closure a task runs goes on the heap too, whose environment holds its
/// own references: the task runs on after the call that started it, while
/// the frame's locals that a side-stack environment borrows may die.
/// Inlining a closure into a known callee, which needs no environment at
/// all, comes with the optimizing tier.
pub fn place(level: EscapeLevel, in_loop: bool) -> ClosurePlacement {
    match level {
        EscapeLevel::Local if !in_loop => ClosurePlacement::SideStack,
        _ => ClosurePlacement::Heap,
    }
}

/// How deeply the type arguments of an instance may nest: a function that
/// calls itself with ever larger type arguments would otherwise have
/// instances without end.
const INSTANCE_DEPTH: usize = 16;

/// How deeply a type nests.
fn depth(db: &dyn Db, ty: Ty<'_>) -> usize {
    let deepest = |tys: &mut dyn Iterator<Item = Ty<'_>>| tys.map(|t| depth(db, t)).max();
    1 + match ty.kind(db) {
        TyKind::Builtin(_, args) | TyKind::Named(_, args) | TyKind::Union(args) => {
            deepest(&mut args.iter().copied())
        }
        TyKind::Record { fields, .. } => deepest(&mut fields.iter().map(|&(_, t)| t)),
        TyKind::Fn { params, result, .. } => deepest(&mut params.iter().copied().chain([*result])),
        TyKind::Error | TyKind::Param(..) => None,
    }
    .unwrap_or(0)
}

/// The name of the field of an environment that holds the `i`th captured
/// value.
fn capture_name<'db>(db: &'db dyn Db, i: usize) -> Name<'db> {
    Name::new(db, format!("{i}"))
}

/// Whether interpolation writes values of a type as text without a `Show`
/// form, which does not exist yet: the numbers and code points.
fn shown_as_text<'db>(db: &'db dyn Db, ty: Ty<'db>) -> bool {
    ty.as_builtin(db).is_some_and(|(b, _)| {
        b.int_range().is_some()
            || matches!(b, Builtin::Float | Builtin::Fixed(_) | Builtin::CodePoint)
    })
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
                | Builtin::Ext
                | Builtin::Lazy
                | Builtin::RuntimeStream
                | Builtin::RuntimeHub
                | Builtin::RuntimeSocket
                | Builtin::Oks
                | Builtin::Errs
        ),
        TyKind::Named(item, _) => !matches!(type_def(db, program, *item).kind, TypeDefKind::Tag),
        TyKind::Record { fields, open } => !fields.is_empty() || *open,
        TyKind::Fn { .. } | TyKind::Param(..) => true,
        TyKind::Union(members) => members.iter().any(|&m| counted(db, program, m)),
    }
}

/// Whether values of a type take two words: strings, bytes and function
/// values, which a union holds in a member box (Compiler Architecture
/// §11).
pub(crate) fn two_words<'db>(db: &'db dyn Db, ty: Ty<'db>) -> bool {
    matches!(
        ty.kind(db),
        TyKind::Builtin(Builtin::Str | Builtin::Bytes, _) | TyKind::Fn { .. }
    )
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

/// The qualifiers of `crag_abi::RuntimeFn::SignalEmit`, which MIR names
/// without depending on the ABI.
mod qualifier {
    pub const PLAIN: u8 = 0;
    pub const OK: u8 = 1;
    pub const FAIL: u8 = 2;
    pub const RETRY: u8 = 3;
}

/// An `atomic` block being built (Plan §11.7.14).
#[derive(Clone, Copy)]
struct AtomicFrame {
    /// Where conflicts go: the block's handler.
    handler: BlockId,
    /// Where the block's value decides between commit and abort.
    outcome: BlockId,
    /// The block's value.
    value: Local,
    /// How many blocks with signal handlers are around the block.
    handlers: usize,
}

/// A block that registers signal handlers (§11.3): the mark they go back
/// to when it ends, and their function values.
#[derive(Clone)]
struct HandlerBlock<'db> {
    mark: Operand<'db>,
    closures: Vec<Operand<'db>>,
}

/// An access function of a ref (Specification §9.3).
#[derive(Clone, Copy)]
enum Access {
    /// `use()`: the current value.
    Get,
    /// `use(f)`: what the closure computes from the current value.
    Use,
    Update,
    Swap,
    Empty,
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
    default: Option<FieldDefault<'db>>,
}

/// The default of a field: a literal, or code of the type that declares
/// the field.
enum FieldDefault<'db> {
    Constant(Constant<'db>),
    Code(InstanceKey<'db>),
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
    instance: InstanceKey<'db>,
    /// The generic function whose type parameters the instance's type
    /// arguments replace, and those arguments.
    generic: Option<(ItemId<'db>, Vec<Ty<'db>>)>,
    /// The functions that fill the instance's slots, in their order.
    fillings: Vec<Instance<'db>>,
    /// The type of each pattern, with the type arguments in place.
    pats: Vec<Option<Ty<'db>>>,
    body: &'a Body<'db>,
    types: &'a InferenceResult<'db>,
    locals: Vec<LocalDecl<'db>>,
    blocks: Vec<(Vec<Statement<'db>>, Option<Terminator<'db>>)>,
    current: BlockId,
    bindings: HashMap<BindingId, Local>,
    unsupported: Vec<(ExprId, &'static str)>,
    params: usize,
    /// Whether local 0 is an environment.
    env: bool,
    result: Ty<'db>,
    /// Whether the code is a test's, which gives no value.
    test: bool,
    /// The `for` loops around what is being built.
    loops: u32,
    /// The `atomic` blocks around what is being built, the innermost last.
    atomic: Vec<AtomicFrame>,
    /// The blocks around what is being built that register signal handlers,
    /// the innermost last.
    handlers: Vec<HandlerBlock<'db>>,
    bool_ty: Ty<'db>,
    true_ty: Ty<'db>,
    false_ty: Ty<'db>,
}

impl<'a, 'db> MirBuilder<'a, 'db> {
    fn new(
        db: &'db dyn Db,
        program: Program,
        instance: InstanceKey<'db>,
        body: &'a Body<'db>,
        types: &'a InferenceResult<'db>,
    ) -> Self {
        let owner = *instance.owner(db);
        let generic = match owner {
            Owner::Item(item) if !instance.args(db).is_empty() => {
                Some((item, instance.args(db).clone()))
            }
            _ => None,
        };
        let pats = match &generic {
            Some((item, args)) => types
                .pats
                .iter()
                .map(|t| t.map(|t| subst(db, program, t, *item, args)))
                .collect(),
            None => types.pats.clone(),
        };
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
            instance,
            generic,
            fillings: instance.fillings(db).clone(),
            pats,
            body,
            types,
            locals: Vec::new(),
            blocks: Vec::new(),
            current: BlockId(0),
            bindings: HashMap::new(),
            unsupported: Vec::new(),
            params: 0,
            env: false,
            result: Ty::unit(db),
            test: false,
            loops: 0,
            atomic: Vec::new(),
            handlers: Vec::new(),
            bool_ty,
            true_ty,
            false_ty,
        };
        b.current = b.new_block();
        b
    }

    // Entries: each makes the parameters and says how the code goes on.

    /// The body of the owner itself.
    fn body_entry(&mut self, root: ExprId) -> Option<Start<'a, 'db>> {
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

    /// The code of a closure literal or a local function: the environment
    /// and the parameters, then the captured values read out of it.
    fn closure_entry(&mut self, frame: ExprId) -> Option<Start<'a, 'db>> {
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
            (TyKind::Fn { params, result, .. }, _) => (params.clone(), *result),
            _ => return None,
        };
        let param_tys = &param_tys;
        self.result = result;
        let (captures, env_ty) = self.environment(frame, own);
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
    fn default_entry(&mut self, default: ExprId) -> Option<Start<'a, 'db>> {
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

    /// The dispose code of the type: the box, whose count reached zero and
    /// which the runtime gave a reference again, then a call of the
    /// handler, which takes it.
    fn dispose_entry(&mut self) -> Option<Start<'a, 'db>> {
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
    fn dispose_code(&self, ty: Ty<'db>) -> Option<InstanceKey<'db>> {
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
            Entry::Dispose,
        ))
    }

    /// The code of a declared function used as a value at `expr`: an empty
    /// environment and the parameters, then the call, split by the
    /// members of union parameters when the value is lifted (§11.5.5).
    fn function_entry(&mut self, expr: ExprId) -> Option<Start<'a, 'db>> {
        let db = self.db;
        let ty = self.expr_ty(expr)?;
        let TyKind::Fn { params, result, .. } = ty.kind(db) else {
            return None;
        };
        let callee = self.types.callee(expr)?.clone();
        let instance = self.callee_instance(&callee);
        self.result = *result;
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
                    &args,
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
        });
        self.switch_to(target);
        self.finish_dest(Operand::Local(dst), ty, Dest::Return);
    }

    /// The bindings a closure's environment holds, all it captures but a
    /// local function's own name, and the environment's type.
    fn environment(&self, frame: ExprId, own: Option<BindingId>) -> (Vec<BindingId>, Ty<'db>) {
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

    fn closure_code(&self, frame: ExprId) -> InstanceKey<'db> {
        self.instance.with_entry(self.db, Entry::Closure(frame))
    }

    // Instances.

    /// A type with the instance's type arguments in place.
    fn subst(&self, ty: Ty<'db>) -> Ty<'db> {
        match &self.generic {
            Some((item, args)) => subst(self.db, self.program, ty, *item, args),
            None => ty,
        }
    }

    fn expr_ty(&self, expr: ExprId) -> Option<Ty<'db>> {
        self.types.expr(expr).map(|t| self.subst(t))
    }

    fn binding_ty(&self, binding: BindingId) -> Option<Ty<'db>> {
        self.types.binding(binding).map(|t| self.subst(t))
    }

    /// The type a type written in the body stands for.
    fn type_ref(&self, ty: crag_hir::TypeRefId) -> Option<Ty<'db>> {
        let ty = self.types.types.get(ty.index()).copied().flatten()?;
        Some(self.subst(ty))
    }

    /// An instance a call in the body names, with the instance's type
    /// arguments in place and its slots replaced by their fillings: one
    /// that names no slot.
    fn concrete(&self, instance: &Instance<'db>) -> Option<Instance<'db>> {
        let fillings = instance
            .fillings
            .iter()
            .map(|f| match f {
                Filling::Function(i) => self.concrete(i).map(Filling::Function),
                Filling::Slot(k) => self
                    .fillings
                    .get(*k as usize)
                    .cloned()
                    .map(Filling::Function),
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Instance {
            function: instance.function,
            args: instance.args.iter().map(|&t| self.subst(t)).collect(),
            fillings,
        })
    }

    /// The function a callee calls, as a concrete instance: a declared
    /// function, an instance of a generic one, or what fills a slot.
    fn callee_instance(&self, callee: &Callee<'db>) -> Option<Instance<'db>> {
        match callee {
            Callee::Function(function) => Some(Instance {
                function: *function,
                args: Vec::new(),
                fillings: Vec::new(),
            }),
            Callee::Instance(instance) => self.concrete(instance),
            Callee::Slot(slot) => self.fillings.get(*slot as usize).cloned(),
            _ => None,
        }
    }

    /// The signature of a concrete instance, its type arguments in place,
    /// with the result inference gives when none is written.
    fn instance_signature(&self, instance: &Instance<'db>) -> Signature<'db> {
        let (db, program) = (self.db, self.program);
        let sig = signature(db, program, instance.function);
        let ty = |t: Ty<'db>| match instance.args.is_empty() {
            true => t,
            false => subst(db, program, t, instance.function, &instance.args),
        };
        Signature {
            type_params: 0,
            params: sig
                .params
                .iter()
                .map(|p| SigParam {
                    ty: ty(p.ty),
                    ..p.clone()
                })
                .collect(),
            result: sig
                .result
                .or_else(|| result_type(db, program, instance.function))
                .map(ty),
        }
    }

    /// The value type of a read of a lazy value, if the call is the
    /// prelude's `value` (§6.10).
    fn lazy_read(&self, instance: &Instance<'db>) -> Option<Ty<'db>> {
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
    fn lazy_value(&mut self, expr: ExprId, lazy: Operand<'db>, ty: Ty<'db>) -> Operand<'db> {
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
        });
        self.switch_to(join);
        Operand::Local(value)
    }

    /// The access function of a ref that a call of the prelude names, if
    /// it is one (Specification §9.3).
    fn cell_access(&self, instance: &Instance<'db>) -> Option<Access> {
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
    fn ref_access(
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
                let TyKind::Fn { result, .. } = f_ty.kind(db) else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let dst = self.temp(*result);
                let target = self.new_block();
                self.terminate(Terminator::CallValue {
                    callee: f,
                    args: vec![value],
                    dst,
                    target,
                    site: expr,
                    unwind: None,
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
    fn atomic_block(&mut self, expr: ExprId, inner: ExprId) -> Operand<'db> {
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
    fn reset_handlers(&mut self, depth: usize) {
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
        });
    }

    /// After a ref operation that reads a cell: when the attempt of the
    /// transaction the task runs must rerun, goes to the handler of the
    /// `atomic` block around, or leaves the frame for a caller's.
    fn leave_on_conflict(&mut self) {
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
    fn is_zero(&mut self, value: Operand<'db>) -> Operand<'db> {
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
            });
            b.switch_to(target);
            dst
        };
        let closure = |b: &mut Self| {
            let f = b.expr(positional[1]);
            let f_ty = b.ty(positional[1]);
            let result = match f_ty.kind(db) {
                TyKind::Fn { result, .. } => Some(*result),
                _ => None,
            };
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
    fn ref_get(&mut self, cell: Operand<'db>, ty: Ty<'db>) -> Operand<'db> {
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
        let TyKind::Fn { result, .. } = f_ty.kind(db) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let result_ty = *result;
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

    /// The operation and the operand `k` of an update closure of the form
    /// `v ⊕ k` on an integer, which the runtime applies under the cell's
    /// lock so that the update never reruns (§9.4): `+`, `*` either way
    /// round and `-` with `v` first, checked, and `k` a literal or another
    /// binding, which the closure captures.
    fn commutative(&self, closure: ExprId, ty: Ty<'db>) -> Option<(BinOp, ExprId)> {
        let db = self.db;
        ty.as_builtin(db).and_then(|(b, _)| b.int_range())?;
        let body = self.body;
        let Expr::Closure {
            params,
            body: inner,
        } = body.expr(closure)
        else {
            return None;
        };
        let [param] = params.as_slice() else {
            return None;
        };
        let Pat::Bind { binding, sub: None } = body.pat(param.pat) else {
            return None;
        };
        let mut inner = *inner;
        while let Expr::Block {
            stmts,
            tail: Some(tail),
        } = body.expr(inner)
            && stmts.is_empty()
        {
            inner = *tail;
        }
        let Expr::Call {
            callee: _,
            args,
            fields: None,
        } = body.expr(inner)
        else {
            return None;
        };
        let [a, b] = args.as_slice() else {
            return None;
        };
        let instance = self.callee_instance(self.types.callee(inner)?)?;
        let Some(Primitive::Arith {
            op,
            ty: builtin,
            checked: true,
        }) = self.primitive_of(&instance)
        else {
            return None;
        };
        if Some((builtin, &[][..])) != ty.as_builtin(db) {
            return None;
        }
        let is_v =
            |e: ExprId| matches!(body.expr(e), Expr::Name { local: Some(l), .. } if l == binding);
        let is_k = |e: ExprId| match body.expr(e) {
            Expr::Literal(_) => true,
            Expr::Name { local: Some(l), .. } => l != binding,
            _ => false,
        };
        match op {
            BinOp::Add | BinOp::Mul if is_v(*a) && is_k(*b) => Some((op, *b)),
            BinOp::Add | BinOp::Mul if is_k(*a) && is_v(*b) => Some((op, *a)),
            BinOp::Sub if is_v(*a) && is_k(*b) => Some((op, *b)),
            _ => None,
        }
    }

    /// The runtime operation a function of the standard library without a
    /// body stands for, if it is one.
    fn intrinsic(&self, instance: &Instance<'db>) -> Option<Intrinsic<'db>> {
        let db = self.db;
        let function = instance.function;
        if hir_body(db, self.program, Owner::Item(function))
            .root
            .is_some()
        {
            return None;
        }
        let module = function.module(db).path(db);
        Some(
            match (module.as_str(), function.name(db).text(db).as_str()) {
                ("std.time", "sleepNanos") => Intrinsic::Sleep,
                ("std.task", "scopeNew") => Intrinsic::ScopeNew,
                ("std.task", "scopeStart") => Intrinsic::ScopeStart,
                ("std.task", "scopeNext") => Intrinsic::ScopeNext,
                ("std.task", "scopeResult") => Intrinsic::ScopeResult,
                ("std.task", "scopeCancel") => Intrinsic::ScopeCancel,
                ("std.task", "scopeEnd") => Intrinsic::ScopeEnd,
                ("std.stream", "streamNew") => Intrinsic::StreamNew {
                    value: *instance.args.first()?,
                },
                ("std.stream", "streamPeer") => Intrinsic::StreamPeer,
                ("std.stream", "streamPut") => Intrinsic::StreamPut { wait: true },
                ("std.stream", "streamTryPut") => Intrinsic::StreamPut { wait: false },
                ("std.stream", "streamNext") => Intrinsic::StreamNext,
                ("std.stream", "streamValue") => Intrinsic::StreamValue,
                ("std.stream", "streamClose") => Intrinsic::StreamClose,
                ("std.stream", "hubNew") => Intrinsic::HubNew {
                    value: *instance.args.first()?,
                },
                ("std.stream", "hubSink") => Intrinsic::HubSink,
                ("std.stream", "hubSource") => Intrinsic::HubSource,
                ("std.stream", "hubSeal") => Intrinsic::HubSeal,
                ("std.stream", "hubRelease") => Intrinsic::HubRelease,
                ("std.io", "ioListen") => Intrinsic::IoListen,
                ("std.io", "ioOwn") => Intrinsic::IoOwn,
                ("std.io", "ioPort") => Intrinsic::IoPort,
                ("std.io", "ioAccept") => Intrinsic::IoAccept,
                ("std.io", "ioSocket") => Intrinsic::IoSocket,
                ("std.io", "ioConnect") => Intrinsic::IoConnect,
                ("std.io", "ioRead") => Intrinsic::IoRead,
                ("std.io", "ioReadBytes") => Intrinsic::IoReadBytes,
                ("std.io", "ioWrite") => Intrinsic::IoWrite,
                _ => return None,
            },
        )
    }

    /// The operation a concrete instance stands for, if it is one.
    fn primitive_of(&self, instance: &Instance<'db>) -> Option<Primitive> {
        match instance.args.is_empty() {
            true => self.primitive(instance.function),
            false => None,
        }
    }

    /// The code a call of a concrete instance goes to, or none when it
    /// cannot be called yet, which is recorded at the call.
    fn callable(&mut self, expr: ExprId, instance: &Instance<'db>) -> Option<InstanceKey<'db>> {
        let db = self.db;
        if crag_hir::c_function(db, instance.function).is_some() {
            self.unsupported(expr, "calls of C functions");
            return None;
        }
        if signature(db, self.program, instance.function).type_params != instance.args.len() {
            self.trap(TrapKind::Error, Some(expr));
            return None;
        }
        if instance.args.iter().any(|&t| depth(db, t) > INSTANCE_DEPTH) {
            self.unsupported(expr, "instances whose type arguments nest this deeply");
            return None;
        }
        Some(InstanceKey::of(db, instance))
    }

    /// A closure literal or a local function as a value: its code and its
    /// environment, placed by its escape level.
    fn closure_value(
        &mut self,
        frame: ExprId,
        ty: Ty<'db>,
        own: Option<BindingId>,
    ) -> Operand<'db> {
        let (captures, env) = self.environment(frame, own);
        let mut ops = Vec::new();
        for &binding in &captures {
            // A closure reads a `var` as it is when it runs, which needs
            // the variable on the side stack.
            if self.body.binding(binding).kind == BindingKind::Var {
                return self.unsupported(frame, "closures capturing a `var`");
            }
            ops.push(Operand::Local(self.binding(binding)));
        }
        let level = self
            .types
            .escapes
            .closures
            .iter()
            .find(|(f, _)| *f == frame)
            .map_or(EscapeLevel::Escaping, |(_, l)| *l);
        let placement = place(level, self.loops > 0);
        let code = self.closure_code(frame);
        self.assign(
            ty,
            Rvalue::Closure {
                code,
                env,
                captures: ops,
                placement,
            },
        )
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
            env: self.env,
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
    fn terminate(&mut self, mut terminator: Terminator<'db>) {
        // A call in an `atomic` block goes to its handler when the code it
        // called leaves the attempt.
        if let Some(frame) = self.atomic.last()
            && let Terminator::Call { unwind, .. } | Terminator::CallValue { unwind, .. } =
                &mut terminator
        {
            *unwind = Some(frame.handler);
        }
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
            .binding_ty(binding)
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
        self.expr_ty(expr).unwrap_or_else(|| Ty::error(self.db))
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
                // A block with signal handlers forgets them when it ends.
                let registers = stmts.iter().any(|s| matches!(s, Stmt::On { .. }));
                if registers {
                    let int = self.int();
                    let mark =
                        self.assign(int, Rvalue::Intrinsic(Intrinsic::SignalMark, Vec::new()));
                    self.handlers.push(HandlerBlock {
                        mark,
                        closures: Vec::new(),
                    });
                }
                for stmt in stmts {
                    self.stmt(stmt);
                }
                match tail {
                    Some(tail) => {
                        self.step(Some(*tail));
                        self.eval(*tail, dest)
                    }
                    None => {
                        let unit = Ty::unit(self.db);
                        self.finish_dest(self.unit(), unit, dest);
                    }
                }
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
            // A tail call would leave an `atomic` block's frame.
            Expr::Call { .. } | Expr::MethodCall { .. } | Expr::TypedCall { .. }
                if matches!(dest, Dest::Return) =>
            {
                let op = self.call(expr, self.atomic.is_empty() && self.handlers.is_empty());
                self.finish_dest(op, self.ty(expr), dest);
            }
            Expr::Field { .. } if matches!(dest, Dest::Return) && self.is_call(expr) => {
                let op = self.call(expr, self.atomic.is_empty() && self.handlers.is_empty());
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
            Expr::Embed => self.embed(expr, ty),
            Expr::Str(parts) => {
                let mut ops = Vec::new();
                for part in parts {
                    match part {
                        StrPart::Text(text) => {
                            ops.push(Operand::Const(Constant::Str(text.clone())))
                        }
                        StrPart::Expr(e) if self.ty(*e) == ty => ops.push(self.expr(*e)),
                        // A number is written as text; in a local, so its
                        // type stays known.
                        StrPart::Expr(e) if shown_as_text(db, self.ty(*e)) => {
                            let part_ty = self.ty(*e);
                            let op = self.expr(*e);
                            ops.push(Operand::Local(self.materialize(op, part_ty)));
                        }
                        StrPart::Expr(e) => {
                            return self.unsupported(
                                *e,
                                "interpolations of other types than Str and numbers",
                            );
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
            Expr::Grid(_) => self.unsupported(expr, "grids"),
            Expr::TypeArgs { .. } => self.unsupported(expr, "type arguments"),
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
    fn call_handler(
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
    fn module_value(&mut self, expr: ExprId, item: ItemId<'db>) -> Operand<'db> {
        let db = self.db;
        let owner = Owner::Item(item);
        let body = hir_body(db, self.program, owner);
        let single = body
            .pattern
            .is_some_and(|(pat, _)| matches!(body.pat(pat), Pat::Bind { sub: None, .. }));
        if !single {
            return self.unsupported(expr, "module-level `let`s with patterns");
        }
        let Some(ty) = value_type(db, self.program, item) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let dst = self.temp(ty);
        let target = self.new_block();
        self.terminate(Terminator::Call {
            func: InstanceKey::body(db, owner),
            args: Vec::new(),
            dst,
            target,
            site: expr,
            unwind: None,
        });
        self.switch_to(target);
        self.coerce(Operand::Local(dst), ty, self.ty(expr))
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
            // A narrowed binding is read as the member a test found
            // (§3.13.4).
            let local = self.binding(binding);
            let (from, to) = (self.locals[local.index()].ty, self.ty(expr));
            return match self.converts(from, to) {
                true => self.assign(to, Rvalue::Convert(Operand::Local(local))),
                false => Operand::Local(local),
            };
        }
        // A function used as a value gets code that calls it.
        if self.is_call(expr) {
            let code = self.instance.with_entry(self.db, Entry::Function(expr));
            let value = Rvalue::Closure {
                code,
                env: Ty::unit(self.db),
                captures: Vec::new(),
                placement: ClosurePlacement::Heap,
            };
            return self.assign(self.ty(expr), value);
        }
        match item {
            Some(Resolution::Value { value: Some(v), .. }) => self.module_value(expr, *v),
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
            Some(callee @ (Callee::Function(_) | Callee::Instance(_) | Callee::Slot(_))) => {
                match self.callee_instance(&callee) {
                    Some(instance) => {
                        self.call_function(expr, &instance, &positional, fields, tail)
                    }
                    None => self.trap(TrapKind::Error, Some(expr)),
                }
            }
            Some(Callee::Construct(ty)) => {
                let ty = self.subst(ty);
                self.construct(expr, ty, &positional, fields)
            }
            Some(Callee::Dispatch(dispatch)) => self.dispatch(expr, &dispatch, &positional, fields),
            Some(Callee::Value) => self.call_value(expr, tail),
            None => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    /// A call of a function value: a closure, a local function, a
    /// parameter or a field.
    fn call_value(&mut self, expr: ExprId, tail: bool) -> Operand<'db> {
        let db = self.db;
        let body = self.body;
        let (callee, fn_ty, args) = match body.expr(expr) {
            Expr::Call { callee, args, .. } => {
                let op = self.expr(*callee);
                (op, self.ty(*callee), args)
            }
            Expr::MethodCall {
                receiver,
                name,
                args,
                ..
            } => {
                let local = self.place_of(*receiver);
                let field = fields_of(db, self.program, self.ty(*receiver))
                    .and_then(|fs| fs.into_iter().find(|(n, _)| n == name));
                let Some((_, field_ty)) = field else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let place = Place {
                    local,
                    path: vec![Step::Field(*name)],
                };
                (self.assign(field_ty, Rvalue::Read(place)), field_ty, args)
            }
            _ => return self.trap(TrapKind::Error, Some(expr)),
        };
        let TyKind::Fn { params, result, .. } = fn_ty.kind(db) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let callee = self.typed(callee, fn_ty);
        let mut ops = Vec::new();
        for (&arg, &param) in args.iter().zip(params) {
            let op = self.expr(arg);
            ops.push(self.coerce(op, self.ty(arg), param));
        }
        if tail && *result == self.result {
            self.terminate(Terminator::TailCallValue {
                callee,
                args: ops,
                site: expr,
            });
            return self.unit();
        }
        let dst = self.temp(*result);
        let target = self.new_block();
        self.terminate(Terminator::CallValue {
            callee,
            args: ops,
            dst,
            target,
            site: expr,
            unwind: None,
        });
        self.switch_to(target);
        Operand::Local(dst)
    }

    /// A lifted call (§4.6.1): the arguments are evaluated once, then a
    /// switch on the tag of each split argument reaches the call for its
    /// members, which gets them converted to the members' types.
    fn dispatch(
        &mut self,
        expr: ExprId,
        dispatch: &Dispatch<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Operand<'db> {
        if fields.is_some_and(|f| !f.is_empty()) {
            return self.unsupported(expr, "lifted calls with named arguments");
        }
        let functions = match self.dispatch_functions(expr, dispatch, positional) {
            Ok(functions) => functions,
            Err(op) => return op,
        };
        let args: Vec<(Local, Ty<'db>)> = positional
            .iter()
            .map(|&arg| {
                let ty = self.ty(arg);
                let op = self.expr(arg);
                (self.materialize(op, ty), ty)
            })
            .collect();
        let dst = self.temp(self.ty(expr));
        let join = self.new_block();
        self.dispatch_arms(
            expr,
            dispatch,
            &functions,
            &args,
            &mut Vec::new(),
            dst,
            join,
        );
        self.switch_to(join);
        Operand::Local(dst)
    }

    /// The concrete instance each arm of a dispatch calls, or what stops
    /// it from being lowered.
    fn dispatch_functions(
        &mut self,
        expr: ExprId,
        dispatch: &Dispatch<'db>,
        positional: &[ExprId],
    ) -> Result<Vec<Instance<'db>>, Operand<'db>> {
        let mut functions = Vec::new();
        for arm in &dispatch.arms {
            let Some(instance) = self.callee_instance(&arm.callee) else {
                return Err(self.trap(TrapKind::Error, Some(expr)));
            };
            if self.instance_signature(&instance).params.len() != positional.len() {
                return Err(self.unsupported(expr, "default arguments"));
            }
            functions.push(instance);
        }
        Ok(functions)
    }

    /// The switch on the split argument at `indices.len()`, or the call
    /// for the members at `indices`.
    #[allow(clippy::too_many_arguments)]
    fn dispatch_arms(
        &mut self,
        expr: ExprId,
        dispatch: &Dispatch<'db>,
        functions: &[Instance<'db>],
        args: &[(Local, Ty<'db>)],
        indices: &mut Vec<usize>,
        dst: Local,
        join: BlockId,
    ) {
        let level = indices.len();
        if level < dispatch.args.len() {
            let members: Vec<Ty<'db>> = dispatch.members[level]
                .iter()
                .map(|&m| self.subst(m))
                .collect();
            let blocks: Vec<BlockId> = members.iter().map(|_| self.new_block()).collect();
            let fail = self.new_block();
            self.terminate(Terminator::Switch {
                place: Place::local(args[dispatch.args[level]].0),
                cases: members.into_iter().zip(blocks.iter().copied()).collect(),
                otherwise: fail,
            });
            self.switch_to(fail);
            self.trap(TrapKind::NoMatch, Some(expr));
            for (i, block) in blocks.into_iter().enumerate() {
                self.switch_to(block);
                indices.push(i);
                self.dispatch_arms(expr, dispatch, functions, args, indices, dst, join);
                indices.pop();
            }
            return;
        }
        let index = indices
            .iter()
            .zip(&dispatch.members)
            .fold(0, |n, (&i, members)| n * members.len() + i);
        let function = &functions[index];
        let result = self.subst(dispatch.arms[index].result);
        let params = self.instance_signature(function).params;
        let mut ops = Vec::new();
        for (k, (&(local, ty), param)) in args.iter().zip(&params).enumerate() {
            let (op, from) = match dispatch.args.iter().position(|&a| a == k) {
                Some(level) => {
                    let member = self.subst(dispatch.members[level][indices[level]]);
                    (self.coerce(Operand::Local(local), ty, member), member)
                }
                None => (Operand::Local(local), ty),
            };
            ops.push(self.coerce(op, from, param.ty));
        }
        let op = match self.primitive_of(function) {
            Some(primitive) => self.primitive_ops(expr, primitive, result, ops),
            None => {
                let Some(func) = self.callable(expr, function) else {
                    return;
                };
                let out = self.temp(result);
                let target = self.new_block();
                self.terminate(Terminator::Call {
                    func,
                    args: ops,
                    dst: out,
                    target,
                    site: expr,
                    unwind: None,
                });
                self.switch_to(target);
                Operand::Local(out)
            }
        };
        self.assign_to(dst, op, result);
        self.terminate(Terminator::Jump(join));
    }

    /// A call of a concrete instance: a declared function, an instance of
    /// a generic one, or what fills a slot.
    fn call_function(
        &mut self,
        expr: ExprId,
        instance: &Instance<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        tail: bool,
    ) -> Operand<'db> {
        if fields.is_none()
            && let Some(primitive) = self.primitive_of(instance)
        {
            return self.primitive_call(expr, primitive, positional);
        }
        if fields.is_none()
            && let Some(value) = self.lazy_read(instance)
            && let [lazy] = positional
        {
            let op = self.expr(*lazy);
            let ty = self.ty(*lazy);
            let lazy = Operand::Local(self.materialize(op, ty));
            return self.lazy_value(expr, lazy, value);
        }
        if fields.is_none()
            && let Some(access) = self.cell_access(instance)
        {
            return self.ref_access(expr, access, instance, positional);
        }
        if fields.is_none()
            && let Some(intrinsic) = self.intrinsic(instance)
        {
            let ops = positional.iter().map(|&arg| self.expr(arg)).collect();
            return self.assign(self.ty(expr), Rvalue::Intrinsic(intrinsic, ops));
        }
        let Some(func) = self.callable(expr, instance) else {
            return self.unit();
        };
        let sig = self.instance_signature(instance);
        let Some(args) = self.arguments(expr, func, &sig, positional, fields) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
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
            unwind: None,
        });
        self.switch_to(target);
        Operand::Local(dst)
    }

    /// The arguments for the parameters of the code `func`, in the order
    /// they are written: positional, then named, or named arguments
    /// building the last parameter, a record (§5.6.2). A parameter left out
    /// takes its default, computed by the default's code from the
    /// parameters before it, after the written arguments. None when the
    /// arguments do not fit, which inference reported.
    fn arguments(
        &mut self,
        expr: ExprId,
        func: InstanceKey<'db>,
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
        // As inference places them: the named arguments, then the
        // positional ones.
        let mut slots: Vec<Option<ExprId>> = vec![None; params.len()];
        let mut fits = positional.len() <= params.len();
        if fits {
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
            let defaults: Vec<bool> = params.iter().map(|p| p.default).collect();
            let taken: Vec<bool> = slots.iter().map(Option::is_some).collect();
            match crag_types::place_positional(&defaults, &taken, positional.len()) {
                Some(places) => {
                    for (&arg, i) in positional.iter().zip(places) {
                        slots[i] = Some(arg);
                    }
                }
                None => fits = false,
            }
        }
        if fits
            && slots
                .iter()
                .zip(params)
                .all(|(s, p)| s.is_some() || p.default)
        {
            let mut ops: Vec<Option<Operand<'db>>> = vec![None; params.len()];
            let order = positional
                .iter()
                .chain(named.iter().flatten().map(|(_, v)| v));
            for &arg in order {
                let i = slots.iter().position(|s| *s == Some(arg))?;
                let op = self.expr(arg);
                ops[i] = Some(self.coerce(op, self.ty(arg), params[i].ty));
            }
            if ops.iter().any(Option::is_none) {
                let Owner::Item(function) = *func.owner(db) else {
                    return None;
                };
                let callee = hir_body(db, self.program, Owner::Item(function));
                for i in 0..params.len() {
                    if ops[i].is_some() {
                        continue;
                    }
                    // The default and the call each take the parameters
                    // before it.
                    let before = (0..i)
                        .map(|k| {
                            let op = ops[k].clone()?;
                            let local = self.materialize(op, params[k].ty);
                            ops[k] = Some(Operand::Local(local));
                            Some(Operand::Local(local))
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let code = func.with_entry(db, Entry::Default(callee.params.get(i)?.default?));
                    let local = self.call_code(code, before, params[i].ty, expr);
                    ops[i] = Some(Operand::Local(local));
                }
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
        ops.push(self.record_value(expr, last.ty, &[], fields.unwrap_or(&[])));
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
        // `-1` is a constant, so `Int8.min` can be written.
        if let (Primitive::Negate(_), [x]) = (primitive, args)
            && let Expr::Literal(literal) = self.body.expr(*x)
        {
            return Operand::Const(self.literal(literal, ty, true));
        }
        let ops = args.iter().map(|&arg| self.expr(arg)).collect();
        self.primitive_ops(expr, primitive, ty, ops)
    }

    /// The operation of a primitive on operands, giving a `ty`.
    fn primitive_ops(
        &mut self,
        expr: ExprId,
        primitive: Primitive,
        ty: Ty<'db>,
        ops: Vec<Operand<'db>>,
    ) -> Operand<'db> {
        let mut ops = ops.into_iter();
        match (primitive, ops.next(), ops.next()) {
            (Primitive::Arith { op, ty: b, checked }, Some(a), Some(c)) => {
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
            (Primitive::Negate(b), Some(a), None) => {
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
            (Primitive::Compare(op, b), Some(a), Some(c)) => {
                self.assign(ty, Rvalue::Compare { op, ty: b, a, b: c })
            }
            _ => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    /// A call of a type: a tag's value, or a record built from arguments.
    /// Calls code with arguments and gives the local of its result, of
    /// type `ty`.
    fn call_code(
        &mut self,
        func: InstanceKey<'db>,
        args: Vec<Operand<'db>>,
        ty: Ty<'db>,
        site: ExprId,
    ) -> Local {
        let dst = self.temp(ty);
        let target = self.new_block();
        self.terminate(Terminator::Call {
            func,
            args,
            dst,
            target,
            site,
            unwind: None,
        });
        self.switch_to(target);
        dst
    }

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
        self.record_value(expr, ty, positional, fields)
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
            let default = self.field_default(ty, name, field_ty);
            slots.push(Slot {
                name,
                ty: field_ty,
                given,
                spread,
                default,
            });
        }
        Some(slots)
    }

    fn record_fits(&self, ty: Ty<'db>, positional: &[ExprId], fields: &[FieldArg<'db>]) -> bool {
        self.record_slots(ty, positional, fields)
            .is_some_and(|slots| {
                slots
                    .iter()
                    .all(|s| s.given.is_some() || s.spread.is_some() || s.default.is_some())
            })
    }

    /// The default of a field of a named record type, as the type that
    /// declares the field last gives it.
    fn field_default(
        &self,
        ty: Ty<'db>,
        name: crag_hir::Name<'db>,
        field_ty: Ty<'db>,
    ) -> Option<FieldDefault<'db>> {
        let db = self.db;
        let mut current = Some(ty);
        while let Some(t) = current {
            let TyKind::Named(item, args) = t.kind(db) else {
                return None;
            };
            let body = hir_body(db, self.program, Owner::Item(*item));
            if let Some(field) = body
                .type_decl
                .as_ref()?
                .fields
                .iter()
                .find(|f| f.name == name)
            {
                let default = field.default?;
                if let Expr::Literal(literal) = body.expr(default) {
                    let constant = self.literal(literal, field_ty, false);
                    return Some(FieldDefault::Constant(constant));
                }
                let code = InstanceKey::new(
                    db,
                    Owner::Item(*item),
                    args.clone(),
                    Vec::new(),
                    Entry::Default(default),
                );
                return Some(FieldDefault::Code(code));
            }
            current = crag_types::parent(db, self.program, t);
        }
        None
    }

    /// Builds a record: the written values in their order, then the
    /// fields spreads give, then the defaults of the rest.
    fn record_value(
        &mut self,
        site: ExprId,
        ty: Ty<'db>,
        positional: &[ExprId],
        fields: &[FieldArg<'db>],
    ) -> Operand<'db> {
        let Some(slots) = self.record_slots(ty, positional, fields) else {
            return self.trap(TrapKind::Error, Some(site));
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
            default,
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
                (None, None) => match default {
                    Some(FieldDefault::Constant(constant)) => Operand::Const(constant),
                    // The type that declares the field last gives it the
                    // type it has here.
                    Some(FieldDefault::Code(code)) => {
                        Operand::Local(self.call_code(code, Vec::new(), field_ty, site))
                    }
                    None => return self.trap(TrapKind::Error, Some(site)),
                },
            };
            out.push((name, op));
        }
        let dispose = self.dispose_code(ty);
        self.assign(
            ty,
            Rvalue::Record {
                ty,
                fields: out,
                dispose,
            },
        )
    }

    // Statements.

    /// A step where the debugger may stop before what starts at `at`, with
    /// every named local made so far; liveness keeps those that hold
    /// values there.
    fn step(&mut self, at: Option<ExprId>) {
        let locals = (0..self.locals.len())
            .filter(|&i| self.locals[i].binding.is_some())
            .map(|i| Local(i as u32))
            .collect();
        self.push(Statement::Step { at, locals });
    }

    fn stmt(&mut self, stmt: &Stmt) {
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
                otherwise,
            } => {
                let test = ty.map(|t| self.type_ref(t));
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
                let local = self.binding(*binding);
                match body.binding(*binding).kind {
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
                    _ => {
                        self.trap(TrapKind::Error, Some(*value));
                    }
                }
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
        let Some(tree) = decision_tree_with(
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

    fn for_loop(&mut self, pat: PatId, iterable: ExprId, body: ExprId) {
        let db = self.db;
        let ty = self.ty(iterable);
        let range = |name: &str| prelude_item(db, self.program, name);
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

    fn case(&mut self, expr: ExprId, subject: ExprId, arms: &[Arm], dest: Dest) {
        let local = self.place_of(subject);
        let ty = self.ty(subject);
        let spec: Vec<(PatId, bool)> = arms.iter().map(|a| (a.pat, a.guard.is_some())).collect();
        let Some(tree) =
            decision_tree_with(self.db, self.program, self.owner, &self.pats, ty, &spec)
        else {
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
            let Some(block) = block else {
                continue;
            };
            self.switch_to(block);
            if let Expr::Pass = self.body.expr(arm.body) {
                // The values no earlier arm handled go to the caller
                // (§8.2).
                let passed = self.ty(arm.body);
                let op = match self.converts(ty, passed) {
                    true => self.assign(passed, Rvalue::Convert(Operand::Local(local))),
                    false => Operand::Local(local),
                };
                self.finish_dest(op, passed, Dest::Return);
                continue;
            }
            self.eval(arm.body, dest);
            self.join(dest, join);
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

/// The local function whose body is `root`, with its name's binding.
fn local_fn_of<'a>(body: &'a Body<'_>, root: ExprId) -> Option<(BindingId, &'a LocalFn)> {
    body.exprs.iter().find_map(|expr| match expr {
        Expr::Block { stmts, .. } => stmts.iter().find_map(|stmt| match stmt {
            Stmt::Fn { binding, function } if function.body == Some(root) => {
                Some((*binding, function))
            }
            _ => None,
        }),
        _ => None,
    })
}

fn int<'db>(n: i128) -> Operand<'db> {
    Operand::Const(Constant::Int(n))
}
