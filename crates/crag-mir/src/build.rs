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
    Builtin, CForm, Callee, DecisionTree, Dispatch, EscapeLevel, Filling, Handler, HandlerCode,
    InferenceResult, Instance, Iteration, ListLen, Position, SigParam, Signature, Step, Ty, TyKind,
    TypeDefKind, Value, body_types, decision_tree, declared_fields, derived_op, dispose_handler,
    fields_of, is_text, lifecycle_handler, literal_value, prelude_item, result_type, signature,
    subst, type_def, type_header, value_type,
};

use crate::ir::{
    BUDGET, BinOp, Block, BlockId, CastOp, ClosurePlacement, CmpOp, Constant, Intrinsic, Local,
    LocalDecl, MirBody, Operand, Place, Rvalue, Statement, TREE, TREE_HASH, Terminator, TrapKind,
    WIRE,
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
    if let Owner::Item(item) = owner
        && entry != Entry::Adapter
    {
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
    let c = match owner {
        Owner::Item(item) => crag_hir::c_function(db, item).map(|_| item),
        Owner::Test(_) => None,
    };
    // The derived walk of a type that meets parts with functions of their
    // own has code for its structure.
    let derived = match (owner, instance.args(db).as_slice()) {
        (Owner::Item(item), &[ty]) if derive::has_derived_code(db, instance) => {
            derive::value_op(db, item).map(|op| (op, ty))
        }
        _ => None,
    };
    let start = match entry {
        Entry::Body if derived.is_some() => derived.and_then(|(op, ty)| b.derived_entry(op, ty)),
        Entry::Body if c.is_some() => c.and_then(|item| b.c_entry(item)),
        Entry::Body => b.body_entry(lowered.body.root?),
        Entry::Closure(frame) => b.closure_entry(frame),
        Entry::Function(expr) => b.function_entry(expr),
        Entry::Default(expr) => b.default_entry(expr),
        Entry::Dispose => b.dispose_entry(),
        Entry::Part => b.part_entry(),
        Entry::Check => b.check_entry(),
        Entry::Adapter => b.adapter_entry(),
    };
    match start {
        Some(start) if ok => start(&mut b),
        _ => {
            b.terminate(Terminator::Trap {
                kind: TrapKind::Error,
                site: None,
                detail: None,
                catch: None,
            });
        }
    }
    Some(b.finish())
}

mod call;
mod case;
mod cell;
mod convert;
mod derive;
mod entry;
mod expr;
mod record;
mod stmt;

pub use derive::has_derived_code;

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
                | Builtin::Ref
                | Builtin::Ext
                | Builtin::Lazy
                | Builtin::Expr
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
        TyKind::Builtin(Builtin::Str | Builtin::Bytes | Builtin::Expr, _) | TyKind::Fn { .. }
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

/// An operator of the prelude that is an operation on numbers or text.
#[derive(Clone, Copy, PartialEq)]
enum Primitive {
    Arith {
        op: BinOp,
        ty: Builtin,
        checked: bool,
    },
    Negate(Builtin),
    Compare(CmpOp, Builtin),
    /// Strings or bytes joined, or a string's bytes: a `Concat`.
    Concat,
    /// A number as another number type (§19.13).
    Cast(CastOp, Builtin),
}

/// A field of a record being built: the expression written for it, or
/// the last spread that has it.
struct Slot<'db> {
    name: crag_hir::Name<'db>,
    ty: Ty<'db>,
    given: Option<ExprId>,
    /// Paths into the field below its name, with their values (§6.7).
    paths: Vec<(Vec<crag_hir::Name<'db>>, ExprId)>,
    spread: Option<ExprId>,
    default: Option<FieldDefault<'db>>,
}

/// The default of a field: a literal, or code of the type that declares
/// the field.
enum FieldDefault<'db> {
    Constant(Constant<'db>),
    Code(InstanceKey<'db>),
}

/// The named arguments of a lifted call, evaluated once: each with its
/// name, or the record they build.
enum Named<'db> {
    Params(Vec<(Name<'db>, Local, Ty<'db>)>),
    Record(Local, Ty<'db>),
}

/// Where a call puts its arguments, as inference does: the named ones by
/// name, then the positional ones around them; the positional ones'
/// places first. None when they do not fit the parameters.
fn named_places<'db>(
    params: &[SigParam<'db>],
    positional: usize,
    names: &[Name<'db>],
) -> Option<Vec<usize>> {
    let mut taken = vec![false; params.len()];
    let mut named = Vec::new();
    for name in names {
        let i = params.iter().position(|p| p.name == Some(*name))?;
        if std::mem::replace(&mut taken[i], true) {
            return None;
        }
        named.push(i);
    }
    let defaults: Vec<bool> = params.iter().map(|p| p.default).collect();
    let mut places = crag_types::place_positional(&defaults, &taken, positional)?;
    for &i in &places {
        taken[i] = true;
    }
    let complete = taken.iter().zip(params).all(|(&t, p)| t || p.default);
    places.extend(named);
    complete.then_some(places)
}

/// The `else` part of a `let`, and the pattern of `{ rest -> … }`.
#[derive(Clone, Copy)]
struct Otherwise {
    rest: Option<PatId>,
    body: ExprId,
}

/// The trap kinds a handler may take, with the prelude's types for them
/// (§8.3).
const TRAP_TYPES: [(crag_abi::TrapKind, &str); 15] = [
    (crag_abi::TrapKind::Overflow, "Overflow"),
    (crag_abi::TrapKind::DivideByZero, "DivisionByZero"),
    (crag_abi::TrapKind::Index, "OutOfBounds"),
    (crag_abi::TrapKind::Hole, "Unfinished"),
    (crag_abi::TrapKind::NoMatch, "Fault"),
    (crag_abi::TrapKind::OutOfSteps, "Exhausted"),
    (crag_abi::TrapKind::OutOfMemory, "Exhausted"),
    (crag_abi::TrapKind::Cycle, "Cycle"),
    (crag_abi::TrapKind::Fault, "Fault"),
    (crag_abi::TrapKind::Unordered, "Unordered"),
    (crag_abi::TrapKind::Expectation, "Expectation"),
    (crag_abi::TrapKind::ConditionFailed, "ConditionFailed"),
    (crag_abi::TrapKind::NotFinite, "NotFinite"),
    (crag_abi::TrapKind::ForeignFault, "ForeignFault"),
    (crag_abi::TrapKind::StackOverflow, "StackOverflow"),
];

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
    /// The handlers of the trap handlers around what is being built, the
    /// innermost last (§8.3.1), and the one around each block's code.
    catches: Vec<BlockId>,
    block_catch: Vec<Option<BlockId>>,
    /// Expressions already evaluated, by the local holding their value
    /// and its type: the receiver of a `?.` access narrowed to what is
    /// not `Empty` (§6.8), and the access itself then.
    given: HashMap<ExprId, (Option<Local>, Ty<'db>)>,
    unsupported: Vec<(ExprId, &'static str)>,
    params: usize,
    /// Whether local 0 is an environment.
    env: bool,
    /// The module values an `Expr`'s code reads out of its environment,
    /// where it captured them (§18.6).
    module_locals: Vec<(ItemId<'db>, Local)>,
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
        // An adapter's type arguments are its types, concrete already.
        let generic = match owner {
            _ if *instance.entry(db) == Entry::Adapter => None,
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
            catches: Vec::new(),
            block_catch: Vec::new(),
            given: HashMap::new(),
            unsupported: Vec::new(),
            params: 0,
            env: false,
            module_locals: Vec::new(),
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

    /// A type with the instance's type arguments in place.
    fn subst(&self, ty: Ty<'db>) -> Ty<'db> {
        match &self.generic {
            Some((item, args)) => subst(self.db, self.program, ty, *item, args),
            None => ty,
        }
    }

    fn expr_ty(&self, expr: ExprId) -> Option<Ty<'db>> {
        if let Some(&(_, ty)) = self.given.get(&expr) {
            return Some(ty);
        }
        self.types.expr(expr).map(|t| self.subst(t))
    }

    /// Whether `expr` is a `?.` access still to branch on its receiver.
    fn is_optional(&self, expr: ExprId) -> bool {
        self.types.optional(expr).is_some() && !self.given.contains_key(&expr)
    }

    /// `receiver?.name` or `receiver?.name(args)`: the access on the
    /// receiver narrowed to what is not `Empty`, else `Empty` (§6.8).
    fn optional(&mut self, expr: ExprId) -> Operand<'db> {
        let Some(optional) = self.types.optional(expr) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let (present, result, empty) = (
            self.subst(optional.present),
            self.subst(optional.result),
            self.subst(optional.empty),
        );
        let receiver = match self.body.expr(expr) {
            Expr::Field { receiver, .. } | Expr::MethodCall { receiver, .. } => *receiver,
            _ => return self.trap(TrapKind::Error, Some(expr)),
        };
        let receiver_ty = self.ty(receiver);
        let subject = self.place_of(receiver);
        let ty = self.ty(expr);
        let value = self.temp(ty);
        let (some, none, join) = (self.new_block(), self.new_block(), self.new_block());
        let cases = present
            .members(self.db)
            .into_iter()
            .map(|m| (m, some))
            .collect();
        self.terminate(Terminator::Switch {
            place: Place::local(subject),
            cases,
            otherwise: none,
        });
        self.switch_to(some);
        let narrowed = self.temp(present);
        self.assign_to(narrowed, Operand::Local(subject), receiver_ty);
        self.given.insert(receiver, (Some(narrowed), present));
        self.given.insert(expr, (None, result));
        let op = self.expr(expr);
        self.given.remove(&receiver);
        self.given.remove(&expr);
        self.assign_to(value, op, result);
        self.terminate(Terminator::Jump(join));
        self.switch_to(none);
        self.assign_to(value, Operand::Const(Constant::Tag(empty)), empty);
        self.terminate(Terminator::Jump(join));
        self.switch_to(join);
        Operand::Local(value)
    }

    fn binding_ty(&self, binding: BindingId) -> Option<Ty<'db>> {
        let ty = self.types.binding(binding).map(|t| self.subst(t))?;
        Some(match self.celled(binding) {
            true => Ty::new(self.db, TyKind::Builtin(Builtin::Ref, vec![ty])),
            false => ty,
        })
    }

    /// Whether a binding is a `var` that a closure captures, which then
    /// lives in a cell that the frame and the closure share, so the
    /// closure reads it as it is when it runs (§6.4.1).
    fn celled(&self, binding: BindingId) -> bool {
        self.body.binding(binding).kind == BindingKind::Var
            && self
                .types
                .escapes
                .captures
                .iter()
                .any(|(_, captured)| captured.contains(&binding))
    }

    /// The type a type written in the body stands for.
    fn type_ref(&self, ty: crag_hir::TypeRefId) -> Option<Ty<'db>> {
        let ty = self.types.types.get(ty.index()).copied().flatten()?;
        Some(self.subst(ty))
    }

    /// An instance a call in the body names, with the instance's type
    /// arguments in place and its slots replaced by their fillings: one
    /// that names no slot. A part that a slot fills with the derived
    /// function itself is left to the walk.
    fn concrete(&self, instance: &Instance<'db>) -> Option<Instance<'db>> {
        let concrete = |f: &Filling<'db>| match f {
            Filling::Function(i) => self.concrete(i).map(Filling::Function),
            Filling::Slot(k) => self
                .fillings
                .get(*k as usize)
                .cloned()
                .map(Filling::Function),
        };
        let fillings = instance
            .fillings
            .iter()
            .map(concrete)
            .collect::<Option<Vec<_>>>()?;
        let mut parts = Vec::new();
        for (ty, f) in &instance.parts {
            let filling = concrete(f)?;
            let walked = matches!(&filling, Filling::Function(i)
                if i.parts.is_empty() && derived_op(self.db, self.program, i.function).is_some());
            if !walked {
                parts.push((self.subst(*ty), filling));
            }
        }
        Some(Instance {
            function: instance.function,
            args: instance.args.iter().map(|&t| self.subst(t)).collect(),
            fillings,
            parts,
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
                parts: Vec::new(),
            }),
            Callee::Instance(instance) => self.concrete(instance),
            Callee::Slot(slot) => self.fillings.get(*slot as usize).cloned(),
            _ => None,
        }
    }

    /// The signature of a concrete instance, its type arguments in place,
    /// with the result inference gives when none is written.
    /// Whether a union has members that interpolation writes as they are.
    fn has_text_member(&self, ty: Ty<'db>) -> bool {
        let members = ty.members(self.db);
        members.len() > 1 && members.iter().any(|&m| is_text(self.db, self.program, m))
    }

    /// An interpolated union value as text: a member that is text as it
    /// is, any other as its `show` writes it (§19.11).
    fn text_or_shown(&mut self, e: ExprId, str_ty: Ty<'db>) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        let ty = self.ty(e);
        let op = self.expr(e);
        let value = self.materialize(op, ty);
        let (text, rest): (Vec<Ty<'db>>, Vec<Ty<'db>>) = ty
            .members(db)
            .into_iter()
            .partition(|&m| is_text(db, program, m));
        let out = self.temp(str_ty);
        let join = self.new_block();
        let blocks: Vec<BlockId> = text.iter().map(|_| self.new_block()).collect();
        let otherwise = self.new_block();
        self.terminate(Terminator::Switch {
            place: Place::local(value),
            cases: text.iter().copied().zip(blocks.iter().copied()).collect(),
            otherwise,
        });
        for (&member, block) in text.iter().zip(blocks) {
            self.switch_to(block);
            let part = self.coerce(Operand::Local(value), ty, member);
            let part = Operand::Local(self.materialize(part, member));
            let written = self.assign(str_ty, Rvalue::Concat(vec![part]));
            self.assign_to(out, written, str_ty);
            self.terminate(Terminator::Jump(join));
        }
        self.switch_to(otherwise);
        let rest = crag_types::normalize(db, program, rest).0;
        let part = self.coerce(Operand::Local(value), ty, rest);
        let shown = match self.types.show(e).cloned() {
            Some(filling) if self.writes_text(Some(&filling)) => {
                match self.call_filled(&filling, vec![(part, rest)], e) {
                    Some((text, text_ty)) => self.coerce(Operand::Local(text), text_ty, str_ty),
                    None => return self.trap(TrapKind::Error, Some(e)),
                }
            }
            _ => {
                let part = Operand::Local(self.materialize(part, rest));
                self.assign(str_ty, Rvalue::Concat(vec![part]))
            }
        };
        self.assign_to(out, shown, str_ty);
        self.terminate(Terminator::Jump(join));
        self.switch_to(join);
        Operand::Local(out)
    }

    /// Whether a type's own `show` gives a plain `Str`, so it writes the
    /// value; one that may fail leaves it to the derived `show`.
    fn writes_text(&self, show: Option<&Filling<'db>>) -> bool {
        let (db, program) = (self.db, self.program);
        let Some(instance) = show.and_then(|f| self.filled(f)) else {
            return false;
        };
        let result = result_type(db, program, instance.function);
        result.is_some_and(|t| matches!(t.as_builtin(db), Some((Builtin::Str, _))))
    }

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
            // The checks of arithmetic, which come later, may go there.
            stack.extend(self.block_catch[b].map(|c| forward[c.index()].index()));
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
            let catch = self.block_catch[old].map(|c| renumber[forward[c.index()].index()]);
            blocks.push(Block {
                statements,
                terminator,
                catch,
                inlined: None,
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
            inlined: Vec::new(),
        }
    }

    // Blocks and locals.

    fn new_block(&mut self) -> BlockId {
        self.blocks.push((Vec::new(), None));
        self.block_catch.push(None);
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
        // So does a trap in a trap handler's block, and in the code a call
        // there calls, to its handler (§8.3.1).
        let landing = self.catches.last().copied();
        match &mut terminator {
            Terminator::Call { catch, .. } | Terminator::CallValue { catch, .. } => {
                *catch = landing
            }
            Terminator::Trap { kind, catch, .. }
                if !matches!(kind, TrapKind::Error | TrapKind::Unsupported) =>
            {
                *catch = landing
            }
            _ => {}
        }
        self.block_catch[self.current.index()] = landing;
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
            split: false,
            borrowed: false,
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
        if let Some(adapted) = self.adapted(op.clone(), from, to) {
            return adapted;
        }
        if let Some(rebuilt) = self.rebuilt(op.clone(), from, to) {
            return rebuilt;
        }
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
        if let Some(adapted) = self.adapted(op.clone(), from, to) {
            self.push(Statement::Assign(local, Rvalue::Use(adapted)));
        } else if let Some(rebuilt) = self.rebuilt(op.clone(), from, to) {
            self.push(Statement::Assign(local, Rvalue::Use(rebuilt)));
        } else if self.converts(from, to) {
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
        self.terminate(Terminator::Trap {
            kind,
            site,
            detail: None,
            catch: None,
        });
        self.unit()
    }

    fn unsupported(&mut self, expr: ExprId, what: &'static str) -> Operand<'db> {
        self.unsupported.push((expr, what));
        self.trap(TrapKind::Unsupported, Some(expr))
    }

    // Expressions.

    /// Whether a value of the type is an assertion's result: `()` or an
    /// `AssertionFailed` of `std.test`, and the latter possible.
    fn is_assertion(&self, ty: Ty<'db>) -> bool {
        let db = self.db;
        let failed = |m: Ty<'db>| {
            matches!(m.kind(db), TyKind::Named(item, _)
                if item.module(db).path(db) == "std.test" && item.name(db).text(db) == "AssertionFailed")
        };
        let members = ty.members(db);
        members.iter().any(|&m| failed(m))
            && members.iter().all(|&m| failed(m) || m == Ty::unit(db))
    }

    /// Hands an assertion's result in a test to `std.test`'s `testRecord`,
    /// with where the assertion is.
    fn record_assertion(&mut self, op: Operand<'db>, ty: Ty<'db>, expr: ExprId) {
        let db = self.db;
        let index = crag_hir::module_index(db, self.program);
        let Some(item) = index.modules.get("std.test").and_then(|m| {
            crag_hir::item_tree(db, *m)
                .items
                .iter()
                .map(|i| i.id)
                .find(|id| {
                    *id.kind(db) == ItemKind::Function && id.name(db).text(db) == "testRecord"
                })
        }) else {
            return;
        };
        let param = signature(db, self.program, item).params[0].ty;
        let op = self.coerce(op, ty, param);
        let int = self.int();
        let site = self.assign(int, Rvalue::Intrinsic(Intrinsic::Site(expr), Vec::new()));
        let key = InstanceKey::body(db, Owner::Item(item));
        let unit = Ty::unit(db);
        self.call_code(key, vec![op, site], unit, expr);
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
