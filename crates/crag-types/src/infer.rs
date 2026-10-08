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

//! Core inference (Implementation Plan §11.4.7): bidirectional checking of
//! one body. An expression is either checked against a type the context
//! expects or synthesizes its own; literals, closures, collection and
//! record literals and generic tags take their types from the context.
//!
//! Core inference covers primitives, records, functions and unions as
//! written. Narrowing by `is`, error propagation, generic calls and forms,
//! overload ranking and union lifting come with M2 (§11.5); what needs
//! them is reported as not supported yet rather than guessed.

use crag_db::Db;
use crag_hir::{
    BindingId, Body, Expr, ExprId, FieldArg, ItemId, ItemKind, Literal, LocalFn, ModuleId, Name,
    Owner, Pat, PatId, Program, Resolution, Stmt, TypeArg, TypeRef, TypeRefId, TypeTarget,
    hir_body, module_scope, type_identity,
};

use crate::def::{
    HeaderKind, TypeLowerer, alias_target, prelude_item, signature, success_type, type_header,
    value_type,
};
use crate::relate::{declared_fields, fields_of, is_subtype, join, normalize};
use crate::result::{Callee, ErrorKind, InferenceResult, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// The types of one body. Runs apart from `body_types` for the queries
/// that ask for a success type or a value's type.
pub fn infer<'db>(db: &'db dyn Db, program: Program, owner: Owner<'db>) -> InferenceResult<'db> {
    let body = hir_body(db, program, owner);
    let generic_owner = match owner {
        Owner::Item(item) => Some(item),
        Owner::Test(_) => None,
    };
    let mut cx = Infer {
        db,
        program,
        body,
        lower: TypeLowerer::new(db, program, body, generic_owner),
        exprs: vec![None; body.exprs.len()],
        pats: vec![None; body.pats.len()],
        bindings: vec![None; body.bindings.len()],
        callees: Vec::new(),
        holes: Vec::new(),
        frames: Vec::new(),
        negative: false,
        bool_ty: prelude_type(db, program, "Bool"),
        empty: prelude_item(db, program, "Empty").map(|e| type_identity(db, program, e)),
        range: prelude_item(db, program, "Range").map(|e| type_identity(db, program, e)),
        range_from: prelude_item(db, program, "RangeFrom").map(|e| type_identity(db, program, e)),
        module: owner.module(db),
    };
    let result = match owner {
        Owner::Item(item) => match *item.kind(db) {
            ItemKind::Function => cx.function(),
            ItemKind::Value => cx.module_value(),
            ItemKind::Type => {
                cx.type_defaults();
                None
            }
            _ => None,
        },
        Owner::Test(_) => {
            if let Some(root) = body.root {
                cx.synth(root);
            }
            None
        }
    };
    InferenceResult {
        exprs: cx.exprs,
        pats: cx.pats,
        bindings: cx.bindings,
        types: cx.lower.types,
        callees: cx.callees,
        result,
        holes: cx.holes,
        errors: cx.lower.errors,
    }
}

fn prelude_type<'db>(db: &'db dyn Db, program: Program, name: &str) -> Ty<'db> {
    let Some(item) = prelude_item(db, program, name) else {
        return Ty::error(db);
    };
    match type_header(db, program, item).kind {
        HeaderKind::Alias => alias_target(db, program, item).unwrap_or_else(|| Ty::error(db)),
        _ => Ty::new(
            db,
            TyKind::Named(type_identity(db, program, item), Vec::new()),
        ),
    }
}

struct Infer<'a, 'db> {
    db: &'db dyn Db,
    program: Program,
    body: &'a Body<'db>,
    /// Lowers written types; its errors are all of the body's.
    lower: TypeLowerer<'a, 'db>,
    exprs: Vec<Option<Ty<'db>>>,
    pats: Vec<Option<Ty<'db>>>,
    bindings: Vec<Option<Ty<'db>>>,
    callees: Vec<(ExprId, Callee<'db>)>,
    holes: Vec<(ExprId, Ty<'db>)>,
    /// The function and closures being checked, innermost last, for
    /// `return`.
    frames: Vec<Frame<'db>>,
    /// Whether the literal being checked is the operand of `negate`, so
    /// `-128` fits an `Int8`.
    negative: bool,
    bool_ty: Ty<'db>,
    empty: Option<ItemId<'db>>,
    /// The prelude's `Range` and `RangeFrom` (§7.4).
    range: Option<ItemId<'db>>,
    range_from: Option<ItemId<'db>>,
    /// The module of the body, whose scope says which types are discrete.
    module: ModuleId,
}

struct Frame<'db> {
    /// The written result type; the `return`s are checked against it.
    expected: Option<Ty<'db>>,
    /// Without one, the types the `return`s give.
    returned: Vec<Ty<'db>>,
}

/// An argument of a call being resolved: typed, or waiting for the
/// parameter type, because its type comes from the context.
#[derive(Clone, Copy)]
enum Arg<'db> {
    Typed(ExprId, Ty<'db>),
    Pending(ExprId),
    /// The receiver of a method call, typed before the call.
    Receiver(ExprId, Ty<'db>),
}

/// How the arguments of a call meet one candidate's parameters.
enum Plan {
    /// For every parameter, the argument it gets, or its default.
    Params(Vec<Option<usize>>),
    /// The named arguments build the last parameter, a record (§5.6.2).
    Record,
}

impl<'a, 'db> Infer<'a, 'db> {
    fn error(&mut self, site: Site, kind: ErrorKind<'db>) {
        self.lower.errors.push(TypeError { site, kind });
    }

    fn err_ty(&self) -> Ty<'db> {
        Ty::error(self.db)
    }

    fn builtin(&self, builtin: Builtin) -> Ty<'db> {
        Ty::builtin(self.db, builtin)
    }

    fn builtin_of(&self, builtin: Builtin, args: Vec<Ty<'db>>) -> Ty<'db> {
        Ty::new(self.db, TyKind::Builtin(builtin, args))
    }

    fn fits(&self, s: Ty<'db>, t: Ty<'db>) -> bool {
        is_subtype(self.db, self.program, s, t)
    }

    fn join(&self, a: Ty<'db>, b: Ty<'db>) -> Ty<'db> {
        join(self.db, self.program, a, b)
    }

    fn join_all(&self, types: Vec<Ty<'db>>) -> Ty<'db> {
        normalize(self.db, self.program, types).0
    }

    /// Reports a mismatch unless `found` fits `expected`.
    fn expect(&mut self, site: Site, found: Ty<'db>, expected: Ty<'db>) {
        if !self.fits(found, expected) {
            self.error(site, ErrorKind::Mismatch { expected, found });
        }
    }

    fn lower_type(&mut self, id: TypeRefId) -> Ty<'db> {
        self.lower.lower(id)
    }

    /// A written type, or none for `_` or no type.
    fn written(&mut self, id: Option<TypeRefId>) -> Option<Ty<'db>> {
        let id = id?;
        match self.body.type_ref(id) {
            TypeRef::Infer => None,
            _ => Some(self.lower_type(id)),
        }
    }

    // Owners.

    fn function(&mut self) -> Option<Ty<'db>> {
        let body = self.body;
        for param in &body.params {
            let ty = self.lower_type(param.ty);
            self.bindings[param.binding.index()] = Some(ty);
            if let Some(default) = param.default {
                self.check(default, ty);
            }
        }
        let expected = self.written(body.result);
        let Some(root) = body.root else {
            return expected;
        };
        Some(self.frame(expected, root))
    }

    /// Checks a function or closure body against its written result type,
    /// or infers it from the body and its `return`s.
    fn frame(&mut self, expected: Option<Ty<'db>>, root: ExprId) -> Ty<'db> {
        self.frames.push(Frame {
            expected,
            returned: Vec::new(),
        });
        let ty = match expected {
            Some(expected) => self.check(root, expected),
            None => self.synth(root),
        };
        let frame = self.frames.pop().expect("pushed above");
        match expected {
            Some(expected) => expected,
            None => {
                let mut types = frame.returned;
                types.push(ty);
                self.join_all(types)
            }
        }
    }

    fn module_value(&mut self) -> Option<Ty<'db>> {
        let body = self.body;
        let (pat, ty) = body.pattern?;
        let root = body.root?;
        let ty = match self.written(ty) {
            Some(ty) => {
                self.check(root, ty);
                ty
            }
            None => self.synth(root),
        };
        self.pattern(pat, ty);
        Some(ty)
    }

    /// The defaults of a type's fields, against the fields' types. The
    /// types themselves are the declaration's, which reports their errors.
    fn type_defaults(&mut self) {
        let Some(decl) = &self.body.type_decl else {
            return;
        };
        let fields: Vec<_> = decl
            .fields
            .iter()
            .map(|f| (self.lower_type(f.ty), f.default))
            .collect();
        self.lower.errors.clear();
        for (ty, default) in fields {
            if let Some(default) = default {
                self.check(default, ty);
            }
        }
    }

    // Expressions.

    fn synth(&mut self, id: ExprId) -> Ty<'db> {
        self.infer(id, None)
    }

    /// Checks an expression against an expected type and returns its own.
    fn check(&mut self, id: ExprId, expected: Ty<'db>) -> Ty<'db> {
        let ty = self.infer(id, Some(expected));
        self.expect(Site::Expr(id), ty, expected);
        ty
    }

    fn infer(&mut self, id: ExprId, expected: Option<Ty<'db>>) -> Ty<'db> {
        let ty = self.infer_expr(id, expected);
        self.exprs[id.index()] = Some(ty);
        ty
    }

    fn infer_expr(&mut self, id: ExprId, expected: Option<Ty<'db>>) -> Ty<'db> {
        let db = self.db;
        let body = self.body;
        match body.expr(id) {
            Expr::Missing => self.err_ty(),
            Expr::Hole => {
                let ty = expected.unwrap_or_else(|| self.err_ty());
                self.holes.push((id, ty));
                ty
            }
            Expr::Literal(literal) => self.literal(id, literal, expected),
            Expr::Str(parts) => {
                for part in parts {
                    if let crag_hir::StrPart::Expr(e) = part {
                        self.synth(*e);
                    }
                }
                self.builtin(Builtin::Str)
            }
            Expr::Name { name, local, item } => self.name(id, *name, *local, item, expected),
            Expr::Call {
                callee,
                args,
                fields,
            } => self.call(id, *callee, args, fields.as_deref(), expected),
            Expr::MethodCall {
                receiver,
                name,
                functions,
                optional,
                args,
                fields,
            } => {
                if *optional {
                    self.error(Site::Expr(id), ErrorKind::Unsupported("`?.` calls"));
                }
                let receiver_ty = self.synth(*receiver);
                if let Some(field) = self.field_ty(receiver_ty, *name)
                    && let TyKind::Fn { .. } = field.kind(db)
                {
                    self.callees.push((id, Callee::Value));
                    return self.call_value(id, field, args, fields.as_deref());
                }
                if functions.is_empty() {
                    self.error(
                        Site::Expr(id),
                        ErrorKind::NoField {
                            ty: receiver_ty,
                            name: *name,
                        },
                    );
                    self.synth_args(args, fields.as_deref());
                    return self.err_ty();
                }
                let receiver = Some(Arg::Receiver(*receiver, receiver_ty));
                self.resolve(
                    id,
                    None,
                    *name,
                    functions,
                    receiver,
                    args,
                    fields.as_deref(),
                    expected,
                    None,
                )
            }
            Expr::TypedCall {
                ty,
                name,
                functions,
                args,
                fields,
            } => {
                let success = self.lower_type(*ty);
                self.resolve(
                    id,
                    None,
                    *name,
                    functions,
                    None,
                    args,
                    fields.as_deref(),
                    expected,
                    Some(success),
                )
            }
            Expr::Field {
                receiver,
                name,
                functions,
                optional,
            } => {
                if *optional {
                    self.error(Site::Expr(id), ErrorKind::Unsupported("`?.` fields"));
                }
                let receiver_ty = self.synth(*receiver);
                if let Some(field) = self.field_ty(receiver_ty, *name) {
                    return field;
                }
                if receiver_ty.is_error(db) {
                    return receiver_ty;
                }
                if functions.is_empty() {
                    let kind = ErrorKind::NoField {
                        ty: receiver_ty,
                        name: *name,
                    };
                    self.error(Site::Expr(id), kind);
                    return self.err_ty();
                }
                let receiver = Some(Arg::Receiver(*receiver, receiver_ty));
                self.resolve(
                    id,
                    None,
                    *name,
                    functions,
                    receiver,
                    &[],
                    None,
                    expected,
                    None,
                )
            }
            Expr::Index { base, args } => self.index(id, *base, args),
            Expr::TypeArgs { base, args } => match body.expr(*base) {
                Expr::Name {
                    name,
                    local: None,
                    item: Some(Resolution::Type(item)),
                } => {
                    let args = self.type_args(args);
                    let ty = self.type_value(id, *name, *item, args, expected);
                    self.exprs[base.index()] = Some(ty);
                    ty
                }
                _ => {
                    let kind = ErrorKind::Unsupported("type arguments of functions");
                    self.error(Site::Expr(id), kind);
                    self.err_ty()
                }
            },
            Expr::And(a, b) | Expr::Or(a, b) => {
                let bool_ty = self.bool_ty;
                self.check(*a, bool_ty);
                self.check(*b, bool_ty);
                bool_ty
            }
            Expr::Not(a) => {
                let bool_ty = self.bool_ty;
                self.check(*a, bool_ty);
                bool_ty
            }
            Expr::Range { start, end } => self.range(id, *start, *end, expected),
            Expr::Is { expr, ty } => {
                self.synth(*expr);
                self.lower_type(*ty);
                self.bool_ty
            }
            Expr::Record(fields) => self.record_literal(fields, expected),
            Expr::List(items) => {
                self.collection(id, items, expected, &[Builtin::List, Builtin::Set])
            }
            Expr::Map(entries) => self.map_literal(id, entries, expected),
            Expr::Grid(rows) => {
                let items: Vec<ExprId> = rows.iter().flatten().copied().collect();
                self.collection(id, &items, expected, &[Builtin::Grid])
            }
            Expr::Block { stmts, tail } => {
                let mut leaves = false;
                for stmt in stmts {
                    leaves |= self.stmt(stmt).is_never(db);
                }
                let ty = match tail {
                    Some(tail) => self.infer(*tail, expected),
                    None => Ty::unit(db),
                };
                if leaves { Ty::never(db) } else { ty }
            }
            Expr::Closure { params, body: root } => self.closure(params, *root, expected),
            Expr::If {
                condition,
                then,
                otherwise,
            } => {
                let bool_ty = self.bool_ty;
                self.check(*condition, bool_ty);
                match otherwise {
                    Some(otherwise) => {
                        let a = self.infer(*then, expected);
                        let b = self.infer(*otherwise, expected);
                        self.join(a, b)
                    }
                    None => {
                        self.synth(*then);
                        Ty::unit(db)
                    }
                }
            }
            Expr::Case { subject, arms } => {
                let subject_ty = self.synth(*subject);
                let mut types = Vec::new();
                for arm in arms {
                    self.pattern(arm.pat, subject_ty);
                    if let Some(guard) = arm.guard {
                        let bool_ty = self.bool_ty;
                        self.check(guard, bool_ty);
                    }
                    types.push(self.infer(arm.body, expected));
                }
                self.join_all(types)
            }
            Expr::Pass => {
                self.error(Site::Expr(id), ErrorKind::Unsupported("`pass` arms"));
                self.err_ty()
            }
            Expr::Atomic(inner) => {
                self.error(Site::Expr(id), ErrorKind::Unsupported("`atomic` blocks"));
                self.synth(*inner);
                self.err_ty()
            }
            Expr::Lazy(inner) => {
                let wanted = expected.and_then(|e| self.member_builtin(e, &[Builtin::Lazy]));
                let ty = match wanted {
                    Some((_, args)) if args.len() == 1 => self.check(*inner, args[0]),
                    _ => self.synth(*inner),
                };
                self.builtin_of(Builtin::Lazy, vec![ty])
            }
        }
    }

    /// The type of a literal, from the context when it gives one (§2.6).
    fn literal(&mut self, id: ExprId, literal: &Literal, expected: Option<Ty<'db>>) -> Ty<'db> {
        let ty = self.literal_ty(literal, expected);
        if !self.literal_fits(literal, ty) {
            self.error(Site::Expr(id), ErrorKind::Literal { ty });
        }
        ty
    }

    fn literal_ty(&self, literal: &Literal, expected: Option<Ty<'db>>) -> Ty<'db> {
        let db = self.db;
        let numeric = |b: Builtin, int: bool| match b {
            Builtin::Float | Builtin::Fixed(_) => true,
            _ => int && b.int_range().is_some(),
        };
        let pick = |int: bool, default: Builtin| {
            let candidates: Vec<Builtin> = expected
                .map(|e| e.members(db))
                .unwrap_or_default()
                .into_iter()
                .filter_map(|m| match m.kind(db) {
                    TyKind::Builtin(b, _) if numeric(*b, int) => Some(*b),
                    _ => None,
                })
                .collect();
            match candidates.as_slice() {
                [one] => *one,
                _ => default,
            }
        };
        match literal {
            Literal::Int(_) => self.builtin(pick(true, Builtin::Int)),
            Literal::Float(_) => self.builtin(pick(false, Builtin::Float)),
            Literal::Str(_) => self.builtin(Builtin::Str),
            Literal::Bytes(_) => self.builtin(Builtin::Bytes),
            Literal::CodePoint(_) => self.builtin(Builtin::CodePoint),
        }
    }

    fn literal_fits(&self, literal: &Literal, ty: Ty<'db>) -> bool {
        let Some((builtin, _)) = ty.as_builtin(self.db) else {
            return true;
        };
        let sign = if self.negative { -1 } else { 1 };
        match (literal, builtin) {
            (Literal::Int(n), Builtin::Fixed(scale)) => i128::try_from(*n)
                .ok()
                .and_then(|n| n.checked_mul(10i128.pow(scale)))
                .is_some_and(|n| i64::try_from(sign * n).is_ok()),
            (Literal::Int(_), Builtin::Float) => true,
            (Literal::Int(n), b) => match (b.int_range(), i128::try_from(*n)) {
                (Some((least, greatest)), Ok(n)) => (least..=greatest).contains(&(sign * n)),
                _ => false,
            },
            (Literal::Float(_), Builtin::Float) => true,
            (Literal::Float(text), Builtin::Fixed(scale)) => fixed_fits(text, scale, sign),
            (Literal::Float(_), _) => false,
            _ => true,
        }
    }

    fn name(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        local: Option<BindingId>,
        item: &Option<Resolution<'db>>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        if let Some(binding) = local {
            return match self.bindings[binding.index()] {
                Some(ty) => ty,
                None => {
                    // A local function used before its success type is
                    // known, or a binding whose pattern failed.
                    if self.body.binding(binding).kind == crag_hir::BindingKind::Fn {
                        self.error(Site::Expr(id), ErrorKind::CannotInfer);
                    }
                    self.err_ty()
                }
            };
        }
        match item {
            Some(Resolution::Value {
                value: Some(value), ..
            }) => match value_type(self.db, self.program, *value) {
                Some(ty) => ty,
                None => {
                    self.error(Site::Expr(id), ErrorKind::ValueCycle { value: *value });
                    self.err_ty()
                }
            },
            Some(Resolution::Value {
                value: None,
                functions,
            }) => self.function_value(id, name, functions, expected),
            Some(Resolution::Type(item)) => self.type_value(id, name, *item, Vec::new(), expected),
            Some(Resolution::Form(_)) => {
                self.error(Site::Expr(id), ErrorKind::NotAValue { name });
                self.err_ty()
            }
            None => self.err_ty(),
        }
    }

    /// The type of a function as a value.
    fn fn_ty(&mut self, id: ExprId, function: ItemId<'db>) -> Ty<'db> {
        let db = self.db;
        let params = signature(db, self.program, function)
            .params
            .iter()
            .map(|p| p.ty)
            .collect();
        let result = self.success(id, function);
        Ty::new(db, TyKind::Fn { params, result })
    }

    fn success(&mut self, id: ExprId, function: ItemId<'db>) -> Ty<'db> {
        match success_type(self.db, self.program, function) {
            Some(ty) => ty,
            None => {
                self.error(Site::Expr(id), ErrorKind::RecursiveSuccess { function });
                self.err_ty()
            }
        }
    }

    /// An overloaded name used as a value: the function whose type fits
    /// the expected one, or the only one (§5.6.1).
    fn function_value(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let (generic, concrete): (Vec<ItemId>, Vec<ItemId>) = functions
            .iter()
            .partition(|&&f| signature(db, self.program, f).type_params > 0);
        let fitting: Vec<ItemId> = match expected {
            Some(expected) if concrete.len() > 1 => concrete
                .iter()
                .copied()
                .filter(|&f| {
                    let sig = signature(db, self.program, f);
                    let params = sig.params.iter().map(|p| p.ty).collect();
                    let result = success_type(db, self.program, f).unwrap_or_else(|| Ty::error(db));
                    self.fits(Ty::new(db, TyKind::Fn { params, result }), expected)
                })
                .collect(),
            _ => concrete,
        };
        match fitting.as_slice() {
            [function] => {
                self.callees.push((id, Callee::Function(*function)));
                self.fn_ty(id, *function)
            }
            [] if !generic.is_empty() => {
                let kind = ErrorKind::Unsupported("generic functions as values");
                self.error(Site::Expr(id), kind);
                self.err_ty()
            }
            [] => {
                let kind = ErrorKind::NoMatch {
                    name,
                    args: Vec::new(),
                };
                self.error(Site::Expr(id), kind);
                self.err_ty()
            }
            candidates => {
                let kind = ErrorKind::Ambiguous {
                    name,
                    candidates: candidates.to_vec(),
                };
                self.error(Site::Expr(id), kind);
                self.err_ty()
            }
        }
    }

    /// A type named where a value is expected: a tag, whose type
    /// arguments the context may give (§3.6.1).
    fn type_value(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        item: ItemId<'db>,
        args: Vec<Ty<'db>>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let header = type_header(db, self.program, item);
        let is_tag = header.kind == HeaderKind::Nominal
            && matches!(
                crate::def::type_def(db, self.program, item).kind,
                crate::def::TypeDefKind::Tag
            );
        if !is_tag {
            self.error(Site::Expr(id), ErrorKind::NotAValue { name });
            return self.err_ty();
        }
        let identity = type_identity(db, self.program, item);
        if header.params.is_empty() || !args.is_empty() {
            if args.len() != header.params.len() {
                let kind = ErrorKind::TypeArgCount {
                    expected: header.params.len(),
                    found: args.len(),
                };
                self.error(Site::Expr(id), kind);
                return self.err_ty();
            }
            return Ty::new(db, TyKind::Named(identity, args));
        }
        let levels: Vec<Ty<'db>> = expected
            .map(|e| e.members(db))
            .unwrap_or_default()
            .into_iter()
            .filter(|m| matches!(m.kind(db), TyKind::Named(i, _) if *i == identity))
            .collect();
        match levels.as_slice() {
            [one] => *one,
            _ => {
                self.error(Site::Expr(id), ErrorKind::CannotInfer);
                self.err_ty()
            }
        }
    }

    fn type_args(&mut self, args: &[TypeArg]) -> Vec<Ty<'db>> {
        args.iter()
            .map(|arg| match arg {
                TypeArg::Type(t) => self.lower_type(*t),
                _ => Ty::error(self.db),
            })
            .collect()
    }

    // Calls.

    fn call(
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
                    let targs = self.type_args(targs);
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
                _ => {
                    let kind = ErrorKind::Unsupported("type arguments of functions");
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

    fn synth_args(&mut self, args: &[ExprId], fields: Option<&[FieldArg<'db>]>) {
        for &arg in args {
            self.synth(arg);
        }
        for field in fields.unwrap_or_default() {
            self.synth(field_value(field));
        }
    }

    /// A call of a function value: positional arguments only.
    fn call_value(
        &mut self,
        id: ExprId,
        ty: Ty<'db>,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Ty<'db> {
        let db = self.db;
        let TyKind::Fn { params, result } = ty.kind(db) else {
            if !ty.is_error(db) {
                self.error(Site::Expr(id), ErrorKind::NotCallable { ty });
            }
            self.synth_args(args, fields);
            return self.err_ty();
        };
        if let Some(fields) = fields {
            let kind = ErrorKind::Unsupported("named arguments to function values");
            self.error(Site::Expr(id), kind);
            for field in fields {
                self.synth(field_value(field));
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
        *result
    }

    /// Whether an expression takes its type from the context, so an
    /// argument is typed only once its parameter is known.
    fn is_pending(&self, id: ExprId) -> bool {
        match self.body.expr(id) {
            Expr::Literal(Literal::Int(_) | Literal::Float(_))
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

    fn is_negation(&self, callee: ExprId) -> bool {
        matches!(self.body.expr(callee), Expr::Name { name, local: None, .. } if name.text(self.db) == "negate")
    }

    /// Whether a pending argument could take the type `param`.
    fn could_fit(&self, id: ExprId, param: Ty<'db>) -> bool {
        let db = self.db;
        let members = param.members(db);
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
            Expr::Call { args, .. } => self.could_fit(args[0], param),
            Expr::Hole => true,
            Expr::Closure { params, .. } => {
                any(&|k| matches!(k, TyKind::Fn { params: p, .. } if p.len() == params.len()))
            }
            Expr::List(_) => builtin(&[Builtin::List, Builtin::Set]),
            Expr::Map(_) => builtin(&[Builtin::Map]),
            Expr::Grid(_) => builtin(&[Builtin::Grid]),
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
            _ => true,
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
            Expr::Call { args, .. } => self.default_fits(args[0], param),
            Expr::Range { start, .. } => param
                .members(db)
                .into_iter()
                .filter_map(|m| self.range_element(m))
                .any(|element| self.default_fits(*start, element)),
            _ => true,
        }
    }

    /// Resolves a call of one of `functions` (§5.6.1) and checks its
    /// arguments. M1 picks the only candidate that fits, filtered by the
    /// expected type and then by the default types of literals; ranking
    /// by specificity comes with M2.
    #[allow(clippy::too_many_arguments)]
    fn resolve(
        &mut self,
        id: ExprId,
        callee: Option<ExprId>,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        receiver: Option<Arg<'db>>,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        expected: Option<Ty<'db>>,
        success: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let program = self.program;
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
        let (generic, concrete): (Vec<ItemId>, Vec<ItemId>) = functions
            .iter()
            .partition(|&&f| signature(db, program, f).type_params > 0);
        let plans: Vec<(ItemId<'db>, Option<Plan>)> = concrete
            .iter()
            .map(|&f| (f, self.plan(f, &positional, &named, builds_record)))
            .collect();
        let chosen = if plans.len() == 1 && generic.is_empty() {
            Some(plans[0].0)
        } else {
            let mut viable: Vec<ItemId<'db>> = plans
                .iter()
                .filter(|(f, plan)| {
                    plan.as_ref()
                        .is_some_and(|p| self.plan_fits(*f, p, &positional, &named))
                })
                .map(|(f, _)| *f)
                .collect();
            if let Some(success) = success {
                viable.retain(|&f| {
                    success_type(db, program, f).is_some_and(|r| self.fits(success, r))
                });
            }
            if viable.len() > 1
                && let Some(expected) = expected
            {
                let fitting: Vec<_> = viable
                    .iter()
                    .copied()
                    .filter(|&f| {
                        success_type(db, program, f).is_some_and(|r| self.fits(r, expected))
                    })
                    .collect();
                if !fitting.is_empty() {
                    viable = fitting;
                }
            }
            if viable.len() > 1 {
                let defaults: Vec<_> = viable
                    .iter()
                    .copied()
                    .filter(|&f| self.defaults_fit(f, &positional))
                    .collect();
                if !defaults.is_empty() {
                    viable = defaults;
                }
            }
            match viable.as_slice() {
                [one] => Some(*one),
                [] => {
                    let kind = if generic.is_empty() {
                        let args = positional
                            .iter()
                            .map(|&a| match a {
                                Arg::Typed(_, t) | Arg::Receiver(_, t) => t,
                                Arg::Pending(e) => self.synth(e),
                            })
                            .collect();
                        ErrorKind::NoMatch { name, args }
                    } else {
                        ErrorKind::Unsupported("calls of generic functions")
                    };
                    if !self.any_error(&positional) {
                        self.error(Site::Expr(id), kind);
                    }
                    None
                }
                candidates => {
                    let kind = ErrorKind::Ambiguous {
                        name,
                        candidates: candidates.to_vec(),
                    };
                    self.error(Site::Expr(id), kind);
                    None
                }
            }
        };
        let Some(function) = chosen else {
            for arg in positional {
                if let Arg::Pending(e) = arg {
                    self.unchecked(e);
                }
            }
            for field in fields.unwrap_or_default() {
                if self.exprs[field_value(field).index()].is_none() {
                    self.synth(field_value(field));
                }
            }
            return self.err_ty();
        };
        self.apply(
            id,
            function,
            &positional,
            fields.unwrap_or_default(),
            &named,
            builds_record,
        );
        self.callees.push((id, Callee::Function(function)));
        let result = self.success(id, function);
        if let Some(callee) = callee {
            let params = signature(db, program, function)
                .params
                .iter()
                .map(|p| p.ty)
                .collect();
            self.exprs[callee.index()] = Some(Ty::new(db, TyKind::Fn { params, result }));
        }
        result
    }

    /// Types an argument of a call that failed to resolve, without errors
    /// that only follow from that: a closure's parameters stay unknown.
    fn unchecked(&mut self, arg: ExprId) {
        let db = self.db;
        match self.body.expr(arg) {
            Expr::Closure { params, .. } => {
                let params = vec![Ty::error(db); params.len()];
                let result = Ty::error(db);
                self.infer(arg, Some(Ty::new(db, TyKind::Fn { params, result })));
            }
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
    fn plan(
        &self,
        function: ItemId<'db>,
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
    ) -> Option<Plan> {
        let sig = signature(self.db, self.program, function);
        let params = &sig.params;
        if positional.len() > params.len() {
            return None;
        }
        if !builds_record {
            let mut given: Vec<Option<usize>> = (0..params.len())
                .map(|i| (i < positional.len()).then_some(i))
                .collect();
            let mut fits = true;
            for (j, (name, _)) in named.iter().enumerate() {
                match params.iter().position(|p| p.name == Some(*name)) {
                    Some(i) if given[i].is_none() => given[i] = Some(positional.len() + j),
                    _ => fits = false,
                }
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
    fn plan_fits(
        &self,
        function: ItemId<'db>,
        plan: &Plan,
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
    ) -> bool {
        let sig = signature(self.db, self.program, function);
        let arg_fits = |arg: Arg<'db>, param: Ty<'db>| match arg {
            Arg::Typed(_, t) | Arg::Receiver(_, t) => self.fits(t, param),
            Arg::Pending(e) => self.could_fit(e, param),
        };
        match plan {
            Plan::Params(given) => given.iter().zip(&sig.params).all(|(g, p)| match g {
                Some(i) if *i < positional.len() => arg_fits(positional[*i], p.ty),
                Some(i) => arg_fits(named[*i - positional.len()].1, p.ty),
                None => true,
            }),
            Plan::Record => {
                let record = sig.params[positional.len()].ty;
                let fields = fields_of(self.db, self.program, record).unwrap_or_default();
                positional
                    .iter()
                    .zip(&sig.params)
                    .all(|(&a, p)| arg_fits(a, p.ty))
                    && named
                        .iter()
                        .all(|(n, a)| fields.iter().any(|(f, t)| f == n && arg_fits(*a, *t)))
            }
        }
    }

    fn defaults_fit(&self, function: ItemId<'db>, positional: &[Arg<'db>]) -> bool {
        let sig = signature(self.db, self.program, function);
        positional.iter().zip(&sig.params).all(|(a, p)| match a {
            Arg::Pending(e) => self.default_fits(*e, p.ty),
            _ => true,
        })
    }

    /// Checks the arguments of a call against the chosen function.
    fn apply(
        &mut self,
        id: ExprId,
        function: ItemId<'db>,
        positional: &[Arg<'db>],
        fields: &[FieldArg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
    ) {
        let db = self.db;
        let sig = signature(db, self.program, function);
        let negative = self.negative;
        self.negative = function.name(db).text(db) == "negate";
        let plan = self.plan(function, positional, named, builds_record);
        match plan {
            Some(Plan::Params(given)) => {
                for (i, g) in given.iter().enumerate() {
                    let Some(g) = *g else { continue };
                    let arg = if g < positional.len() {
                        positional[g]
                    } else {
                        named[g - positional.len()].1
                    };
                    self.check_arg(arg, sig.params[i].ty);
                }
            }
            Some(Plan::Record) => {
                for (&arg, param) in positional.iter().zip(&sig.params) {
                    self.check_arg(arg, param.ty);
                }
                let record = sig.params[positional.len()].ty;
                self.build_record(id, record, fields);
            }
            None => {
                // Only a lone candidate gets here; say what is wrong.
                let mut seen = vec![false; sig.params.len()];
                for (i, &arg) in positional.iter().enumerate() {
                    match sig.params.get(i) {
                        Some(param) => {
                            seen[i] = true;
                            self.check_arg(arg, param.ty);
                        }
                        None => self.check_arg(arg, Ty::error(db)),
                    }
                }
                if positional.len() > sig.params.len() {
                    let kind = ErrorKind::ArgCount {
                        expected: sig.params.len(),
                        found: positional.len(),
                    };
                    self.error(Site::Expr(id), kind);
                }
                for field in fields {
                    let value = field_value(field);
                    let param = match field {
                        FieldArg::Field { path, .. } if path.len() == 1 => {
                            sig.params.iter().position(|p| p.name == Some(path[0]))
                        }
                        _ => None,
                    };
                    match param {
                        Some(i) if !seen[i] => {
                            seen[i] = true;
                            self.check(value, sig.params[i].ty);
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
                for (i, param) in sig.params.iter().enumerate() {
                    if !seen[i] && !param.default {
                        let kind = match param.name {
                            Some(name) => ErrorKind::MissingArg { name },
                            None => ErrorKind::ArgCount {
                                expected: sig.params.len(),
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
            Arg::Typed(e, t) | Arg::Receiver(e, t) => self.expect(Site::Expr(e), t, param),
        }
    }

    /// A call of a type: the construction of a record, or of an empty
    /// collection with its type arguments (§6.5, §6.7).
    #[allow(clippy::too_many_arguments)]
    fn construct(
        &mut self,
        id: ExprId,
        callee: ExprId,
        name: Name<'db>,
        item: ItemId<'db>,
        targs: Option<Vec<Ty<'db>>>,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let program = self.program;
        let header = type_header(db, program, item);
        let arity = header.params.len();
        let ty = match header.kind {
            HeaderKind::Builtin(
                builtin @ (Builtin::List | Builtin::Map | Builtin::Set | Builtin::Grid),
            ) if args.is_empty() && fields.is_none() => {
                let targs = targs.or_else(|| {
                    let (b, a) = expected.and_then(|e| self.member_builtin(e, &[builtin]))?;
                    (b == builtin).then_some(a)
                });
                match targs {
                    Some(targs) if targs.len() == arity => self.builtin_of(builtin, targs),
                    _ => {
                        self.error(Site::Expr(id), ErrorKind::CannotInfer);
                        self.err_ty()
                    }
                }
            }
            HeaderKind::Nominal | HeaderKind::Alias => {
                let identity = type_identity(db, program, item);
                let target = match header.kind {
                    HeaderKind::Alias => match (alias_target(db, program, item), &targs) {
                        (Some(t), Some(targs)) => {
                            Some(crate::relate::subst(db, program, t, item, targs))
                        }
                        (Some(t), None) if arity == 0 => Some(t),
                        _ => None,
                    },
                    _ => {
                        let targs = targs.clone().or_else(|| {
                            expected?
                                .members(db)
                                .into_iter()
                                .find_map(|m| match m.kind(db) {
                                    TyKind::Named(i, a) if *i == identity => Some(a.clone()),
                                    _ => None,
                                })
                        });
                        match targs {
                            Some(targs) if targs.len() == arity => {
                                Some(Ty::new(db, TyKind::Named(identity, targs)))
                            }
                            None if arity == 0 => {
                                Some(Ty::new(db, TyKind::Named(identity, Vec::new())))
                            }
                            _ => None,
                        }
                    }
                };
                let Some(ty) = target else {
                    let kind = ErrorKind::Unsupported("inferred type arguments of constructions");
                    self.error(Site::Expr(id), kind);
                    self.synth_args(args, fields);
                    return self.err_ty();
                };
                if declared_fields(db, program, ty).is_none() {
                    self.error(Site::Expr(id), ErrorKind::NotAValue { name });
                    self.synth_args(args, fields);
                    return self.err_ty();
                }
                if !args.is_empty() {
                    let kind = if args.len() == 1 && fields.is_none() {
                        ErrorKind::Unsupported("conversions")
                    } else {
                        ErrorKind::ArgCount {
                            expected: 0,
                            found: args.len(),
                        }
                    };
                    self.error(Site::Expr(id), kind);
                    self.synth_args(args, None);
                }
                self.build_record(id, ty, fields.unwrap_or_default());
                ty
            }
            _ => {
                let kind = if args.len() == 1 && fields.is_none() {
                    ErrorKind::Unsupported("conversions")
                } else {
                    ErrorKind::NotAValue { name }
                };
                self.error(Site::Expr(id), kind);
                self.synth_args(args, fields);
                return self.err_ty();
            }
        };
        self.exprs[callee.index()] = Some(ty);
        self.callees.push((id, Callee::Construct(ty)));
        ty
    }

    /// Checks a field list that builds a record of type `ty`: each field
    /// given once, by name, by a spread or by its default (§6.7).
    fn build_record(&mut self, site: ExprId, ty: Ty<'db>, fields: &[FieldArg<'db>]) {
        let db = self.db;
        let program = self.program;
        let declared: Vec<(Name<'db>, Ty<'db>, bool)> = match declared_fields(db, program, ty) {
            Some(fields) => fields,
            None => fields_of(db, program, ty)
                .unwrap_or_default()
                .into_iter()
                .map(|(n, t)| (n, t, false))
                .collect(),
        };
        let mut given = vec![false; declared.len()];
        for field in fields {
            match field {
                FieldArg::Spread(value) => {
                    let spread = self.synth(*value);
                    let Some(supplied) = fields_of(db, program, spread) else {
                        if !spread.is_error(db) {
                            let kind = ErrorKind::Unsupported("spreads of non-records");
                            self.error(Site::Expr(*value), kind);
                        }
                        given.iter_mut().for_each(|g| *g = true);
                        continue;
                    };
                    for (i, (name, field_ty, _)) in declared.iter().enumerate() {
                        if let Some((_, t)) = supplied.iter().find(|(n, _)| n == name) {
                            given[i] = true;
                            let found = *t;
                            self.expect(Site::Expr(*value), found, *field_ty);
                        }
                    }
                }
                FieldArg::Field { path, value } => {
                    if path.len() > 1 {
                        self.error(Site::Expr(*value), ErrorKind::Unsupported("field paths"));
                        self.synth(*value);
                        continue;
                    }
                    let name = path[0];
                    match declared.iter().position(|(n, ..)| *n == name) {
                        Some(i) => {
                            if given[i] && !self.spread_supplies(fields, name) {
                                self.error(Site::Expr(*value), ErrorKind::DuplicateField { name });
                            }
                            given[i] = true;
                            let field_ty = declared[i].1;
                            if matches!(self.body.expr(*value), Expr::Closure { .. })
                                && !matches!(field_ty.kind(db), TyKind::Fn { .. })
                            {
                                self.error(
                                    Site::Expr(*value),
                                    ErrorKind::Unsupported("field transforms"),
                                );
                                self.synth(*value);
                            } else {
                                self.check(*value, field_ty);
                            }
                        }
                        None => {
                            self.error(Site::Expr(*value), ErrorKind::UnknownField { name });
                            self.synth(*value);
                        }
                    }
                }
            }
        }
        for (i, (name, _, default)) in declared.iter().enumerate() {
            if !given[i] && !default {
                self.error(Site::Expr(site), ErrorKind::MissingField { name: *name });
            }
        }
    }

    /// Whether a spread in the list supplies the field, which a named
    /// field may then override.
    fn spread_supplies(&self, fields: &[FieldArg<'db>], name: Name<'db>) -> bool {
        fields.iter().any(|f| match f {
            FieldArg::Spread(value) => self.exprs[value.index()]
                .and_then(|t| fields_of(self.db, self.program, t))
                .is_some_and(|fs| fs.iter().any(|(n, _)| *n == name)),
            _ => false,
        })
    }

    /// An anonymous record literal, against the record type expected if
    /// there is one (§3.4).
    fn record_literal(&mut self, fields: &[FieldArg<'db>], expected: Option<Ty<'db>>) -> Ty<'db> {
        let db = self.db;
        let wanted: Vec<(Name<'db>, Ty<'db>)> = expected
            .and_then(|e| {
                e.members(db)
                    .into_iter()
                    .find(|m| matches!(m.kind(db), TyKind::Record { .. }))
            })
            .and_then(|r| fields_of(db, self.program, r))
            .unwrap_or_default();
        let mut built: Vec<(Name<'db>, Ty<'db>)> = Vec::new();
        for field in fields {
            match field {
                FieldArg::Spread(value) => {
                    let spread = self.synth(*value);
                    match fields_of(db, self.program, spread) {
                        Some(supplied) => {
                            for (name, ty) in supplied {
                                if !built.iter().any(|(n, _)| *n == name) {
                                    built.push((name, ty));
                                }
                            }
                        }
                        None if spread.is_error(db) => {}
                        None => {
                            let kind = ErrorKind::Unsupported("spreads of non-records");
                            self.error(Site::Expr(*value), kind);
                        }
                    }
                }
                FieldArg::Field { path, value } => {
                    if path.len() > 1 {
                        self.error(Site::Expr(*value), ErrorKind::Unsupported("field paths"));
                        self.synth(*value);
                        continue;
                    }
                    let name = path[0];
                    let spread = built.iter().position(|(n, _)| *n == name);
                    let explicit = fields
                        .iter()
                        .take_while(|f| !std::ptr::eq(*f, field))
                        .any(|f| matches!(f, FieldArg::Field { path, .. } if path == &[name]));
                    if explicit {
                        self.error(Site::Expr(*value), ErrorKind::DuplicateField { name });
                    }
                    if spread.is_some() && matches!(self.body.expr(*value), Expr::Closure { .. }) {
                        self.error(
                            Site::Expr(*value),
                            ErrorKind::Unsupported("field transforms"),
                        );
                    }
                    let field_expected = wanted.iter().find(|(n, _)| *n == name).map(|(_, t)| *t);
                    let ty = self.infer(*value, field_expected);
                    match spread {
                        Some(i) => built[i].1 = ty,
                        None => built.push((name, ty)),
                    }
                }
            }
        }
        Ty::record(db, built, false)
    }

    /// A list, set or grid literal: the element type comes from the
    /// expected collection type, or is the union of the elements.
    fn collection(
        &mut self,
        id: ExprId,
        items: &[ExprId],
        expected: Option<Ty<'db>>,
        kinds: &[Builtin],
    ) -> Ty<'db> {
        if let Some((builtin, args)) = expected.and_then(|e| self.member_builtin(e, kinds))
            && args.len() == 1
        {
            for &item in items {
                self.check(item, args[0]);
            }
            return self.builtin_of(builtin, args);
        }
        if items.is_empty() {
            self.error(Site::Expr(id), ErrorKind::CannotInfer);
            return self.err_ty();
        }
        let types = items.iter().map(|&i| self.synth(i)).collect();
        let element = self.join_all(types);
        self.builtin_of(kinds[0], vec![element])
    }

    fn map_literal(
        &mut self,
        id: ExprId,
        entries: &[(ExprId, ExprId)],
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        if let Some((_, args)) = expected.and_then(|e| self.member_builtin(e, &[Builtin::Map]))
            && args.len() == 2
        {
            for &(key, value) in entries {
                self.check(key, args[0]);
                self.check(value, args[1]);
            }
            return self.builtin_of(Builtin::Map, args);
        }
        if entries.is_empty() {
            self.error(Site::Expr(id), ErrorKind::CannotInfer);
            return self.err_ty();
        }
        let keys = entries.iter().map(|&(k, _)| self.synth(k)).collect();
        let values = entries.iter().map(|&(_, v)| self.synth(v)).collect();
        let (keys, values) = (self.join_all(keys), self.join_all(values));
        self.builtin_of(Builtin::Map, vec![keys, values])
    }

    /// The one member of `ty` that is one of the builtins, with its
    /// arguments.
    fn member_builtin(&self, ty: Ty<'db>, kinds: &[Builtin]) -> Option<(Builtin, Vec<Ty<'db>>)> {
        let db = self.db;
        let found: Vec<(Builtin, Vec<Ty<'db>>)> = ty
            .members(db)
            .into_iter()
            .filter_map(|m| match m.kind(db) {
                TyKind::Builtin(b, args) if kinds.contains(b) => Some((*b, args.clone())),
                _ => None,
            })
            .collect();
        match <[_; 1]>::try_from(found) {
            Ok([one]) => Some(one),
            Err(_) => None,
        }
    }

    fn field_ty(&self, ty: Ty<'db>, name: Name<'db>) -> Option<Ty<'db>> {
        fields_of(self.db, self.program, ty)?
            .into_iter()
            .find(|(n, _)| *n == name)
            .map(|(_, t)| t)
    }

    /// `e[i]`: a list element, or a map value as an option (§6.5).
    fn index(&mut self, id: ExprId, base: ExprId, args: &[ExprId]) -> Ty<'db> {
        let db = self.db;
        let base_ty = self.synth(base);
        match (base_ty.kind(db), args) {
            (TyKind::Builtin(Builtin::List, element), [i]) => {
                let element = element[0];
                let int = self.builtin(Builtin::Int);
                self.check(*i, int);
                element
            }
            (TyKind::Builtin(Builtin::Map, kv), [key]) => {
                let (k, v) = (kv[0], kv[1]);
                self.check(*key, k);
                self.option(v)
            }
            _ => {
                if !base_ty.is_error(db) {
                    self.error(Site::Expr(id), ErrorKind::NotIndexable { ty: base_ty });
                }
                for &arg in args {
                    self.synth(arg);
                }
                self.err_ty()
            }
        }
    }

    /// `Option[T]`, which is `T | Empty[T]` (§3.6.1).
    fn option(&self, ty: Ty<'db>) -> Ty<'db> {
        match self.empty {
            Some(empty) => {
                let empty = Ty::new(self.db, TyKind::Named(empty, vec![ty]));
                self.join(ty, empty)
            }
            None => self.err_ty(),
        }
    }

    fn closure(
        &mut self,
        params: &[crag_hir::ClosureParam],
        root: ExprId,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let wanted = expected.and_then(|e| {
            e.members(db).into_iter().find_map(|m| match m.kind(db) {
                TyKind::Fn { params: p, result } if p.len() == params.len() => {
                    Some((p.clone(), *result))
                }
                _ => None,
            })
        });
        let mut param_tys = Vec::new();
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
                (None, None) => {
                    self.error(Site::Pat(param.pat), ErrorKind::CannotInfer);
                    self.err_ty()
                }
            };
            self.pattern(param.pat, ty);
            param_tys.push(ty);
        }
        let result = wanted.map(|(_, r)| r).filter(|r| !r.is_error(db));
        let result = self.frame(result, root);
        Ty::new(
            db,
            TyKind::Fn {
                params: param_tys,
                result,
            },
        )
    }

    // Statements.

    /// Checks a statement; `Never` when it leaves the block.
    fn stmt(&mut self, stmt: &Stmt) -> Ty<'db> {
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
                self.pattern(*pat, ty);
                if ty.is_never(db) { ty } else { unit }
            }
            Stmt::LetElse {
                pat,
                ty,
                value,
                otherwise,
            } => {
                let value_ty = self.synth(*value);
                let target = self.written(*ty).unwrap_or(value_ty);
                self.pattern(*pat, target);
                if let Expr::Closure { .. } = self.body.expr(*otherwise) {
                    let kind = ErrorKind::Unsupported("`else` closures");
                    self.error(Site::Expr(*otherwise), kind);
                    self.synth(*otherwise);
                } else {
                    let leaves = self.synth(*otherwise);
                    if !leaves.is_never(db) && !leaves.is_error(db) {
                        self.error(Site::Expr(*otherwise), ErrorKind::MustLeave);
                    }
                }
                unit
            }
            Stmt::Bind { binding, ty, value } => {
                if self.body.binding(*binding).kind != crag_hir::BindingKind::Var {
                    let kind = ErrorKind::Unsupported("`ref` and `ext` bindings");
                    self.error(Site::Binding(*binding), kind);
                    self.synth(*value);
                    self.bindings[binding.index()] = Some(self.err_ty());
                    return unit;
                }
                let ty = match self.written(*ty) {
                    Some(ty) => {
                        self.check(*value, ty);
                        ty
                    }
                    None => self.synth(*value),
                };
                self.bindings[binding.index()] = Some(ty);
                unit
            }
            Stmt::Assign { binding, value } => {
                let ty = self.bindings[binding.index()].unwrap_or_else(|| Ty::error(db));
                self.check(*value, ty);
                unit
            }
            Stmt::For {
                pat,
                iterable,
                body,
            } => {
                let element = self.iterable(*iterable);
                self.pattern(*pat, element);
                self.synth(*body);
                unit
            }
            Stmt::Emit { value, .. } => {
                self.error(Site::Expr(*value), ErrorKind::Unsupported("signals"));
                self.synth(*value);
                unit
            }
            Stmt::Return(value) => {
                let expected = self.frames.last().and_then(|f| f.expected);
                let ty = match (value, expected) {
                    (Some(value), Some(expected)) => self.check(*value, expected),
                    (Some(value), None) => self.synth(*value),
                    (None, expected) => {
                        if let Some(expected) = expected
                            && !self.fits(unit, expected)
                        {
                            // A bare `return` gives `()`.
                            let kind = ErrorKind::Mismatch {
                                expected,
                                found: unit,
                            };
                            let site = self.frame_site();
                            self.error(site, kind);
                        }
                        unit
                    }
                };
                if let Some(frame) = self.frames.last_mut() {
                    frame.returned.push(ty);
                }
                Ty::never(db)
            }
            Stmt::On { handler, .. } => {
                self.error(
                    Site::Expr(*handler),
                    ErrorKind::Unsupported("`on` handlers"),
                );
                self.synth(*handler);
                unit
            }
            Stmt::Fn { binding, function } => {
                self.local_fn(*binding, function);
                unit
            }
        }
    }

    fn frame_site(&self) -> Site {
        Site::Expr(self.body.root.unwrap_or(ExprId(0)))
    }

    /// `a..b` or `a..` (§7.4): a `Range[T]` or `RangeFrom[T]` whose ends
    /// have the same discrete type `T`.
    fn range(
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
                self.check(start, element);
                if let Some(end) = end {
                    self.check(end, element);
                }
                element
            }
            // `1..n` takes the type of `n`, if it is discrete.
            (None, Some(end)) if self.is_pending(start) && !self.is_pending(end) => {
                let end_ty = self.synth(end);
                if self.is_discrete(end_ty) {
                    self.check(start, end_ty);
                    end_ty
                } else {
                    let element = self.synth(start);
                    self.expect(Site::Expr(end), end_ty, element);
                    element
                }
            }
            (None, _) => {
                let element = self.synth(start);
                if let Some(end) = end {
                    self.check(end, element);
                }
                element
            }
        };
        if !self.is_discrete(element) {
            self.error(Site::Expr(id), ErrorKind::NotDiscrete { ty: element });
            return self.err_ty();
        }
        if let Some(end) = end
            && let (Some(lo), Some(hi)) = (self.constant_expr(start), self.constant_expr(end))
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

    /// The `T` of a `Range[T]` or `RangeFrom[T]`.
    fn range_element(&self, ty: Ty<'db>) -> Option<Ty<'db>> {
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
    /// `CodePoint`, and types with a `compare` and a `next` in scope.
    /// Type parameters pass; their bounds are checked with M2.
    fn is_discrete(&self, ty: Ty<'db>) -> bool {
        let db = self.db;
        match ty.kind(db) {
            TyKind::Error | TyKind::Param(..) => true,
            TyKind::Builtin(b, _) => b.int_range().is_some() || *b == Builtin::CodePoint,
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
                && success_type(db, self.program, function).is_some_and(|r| self.fits(r, result))
        })
    }

    /// The value of a range end written as a literal, possibly negated.
    fn constant_expr(&self, id: ExprId) -> Option<i128> {
        match self.body.expr(id) {
            Expr::Literal(literal) => constant(literal),
            Expr::Call { callee, args, .. } if args.len() == 1 && self.is_negation(*callee) => {
                self.constant_expr(args[0]).map(|n| -n)
            }
            _ => None,
        }
    }

    /// The element type of what `for` iterates (§7.3).
    fn iterable(&mut self, iterable: ExprId) -> Ty<'db> {
        let db = self.db;
        let ty = self.synth(iterable);
        if let Some(element) = self.range_element(ty) {
            return element;
        }
        match ty.kind(db) {
            TyKind::Builtin(Builtin::List | Builtin::Set | Builtin::Grid, args) => args[0],
            TyKind::Builtin(Builtin::Map, args) => {
                let key = Name::new(db, "key".to_string());
                let value = Name::new(db, "value".to_string());
                Ty::record(db, vec![(key, args[0]), (value, args[1])], false)
            }
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
                },
            );
            self.bindings[binding.index()] = Some(ty);
        }
        let result = match function.body {
            Some(root) => self.frame(expected, root),
            None => expected.unwrap_or_else(|| Ty::error(db)),
        };
        self.bindings[binding.index()] = Some(Ty::new(db, TyKind::Fn { params, result }));
    }

    // Patterns.

    /// Checks a pattern against the type of what it matches and returns the
    /// type it narrows that to.
    fn pattern(&mut self, id: PatId, subject: Ty<'db>) -> Ty<'db> {
        let ty = self.pattern_inner(id, subject);
        self.pats[id.index()] = Some(ty);
        ty
    }

    fn pattern_inner(&mut self, id: PatId, subject: Ty<'db>) -> Ty<'db> {
        let db = self.db;
        let body = self.body;
        match body.pat(id) {
            Pat::Missing => self.err_ty(),
            Pat::Wildcard => subject,
            Pat::Bind { binding, sub } => {
                let ty = match sub {
                    Some(sub) => self.pattern(*sub, subject),
                    None => subject,
                };
                // The alternatives of an or-pattern share their bindings.
                let ty = match self.bindings[binding.index()] {
                    Some(previous) => self.join(previous, ty),
                    None => ty,
                };
                self.bindings[binding.index()] = Some(ty);
                ty
            }
            Pat::Type(tref) => {
                let ty = self.pattern_type(*tref, subject);
                self.narrow(id, ty, subject)
            }
            Pat::Record { ty, fields } => {
                let matched = match ty {
                    Some(tref) => {
                        let ty = self.pattern_type(*tref, subject);
                        self.narrow(id, ty, subject)
                    }
                    None => subject,
                };
                let declared: Vec<(Name<'db>, Ty<'db>)> =
                    match declared_fields(db, self.program, matched) {
                        Some(fields) => fields.into_iter().map(|(n, t, _)| (n, t)).collect(),
                        None => match fields_of(db, self.program, matched) {
                            Some(fields) => fields,
                            None => {
                                if !matched.is_error(db) {
                                    let kind = ErrorKind::NeverMatches {
                                        pattern: Ty::unit(db),
                                        subject: matched,
                                    };
                                    self.error(Site::Pat(id), kind);
                                }
                                for field in fields {
                                    self.pattern(field.pat, Ty::error(db));
                                }
                                return self.err_ty();
                            }
                        },
                    };
                for (i, field) in fields.iter().enumerate() {
                    let field_ty = match field.name {
                        Some(name) => declared.iter().find(|(n, _)| *n == name).map(|(_, t)| *t),
                        None => declared.get(i).map(|(_, t)| *t),
                    };
                    let field_ty = match field_ty {
                        Some(t) => t,
                        None => {
                            if !matched.is_error(db) {
                                let kind = match field.name {
                                    Some(name) => ErrorKind::NoField { ty: matched, name },
                                    None => ErrorKind::ArgCount {
                                        expected: declared.len(),
                                        found: fields.len(),
                                    },
                                };
                                self.error(Site::Pat(field.pat), kind);
                            }
                            Ty::error(db)
                        }
                    };
                    self.pattern(field.pat, field_ty);
                }
                matched
            }
            Pat::List {
                before,
                rest,
                after,
            } => {
                let element = match self.member_builtin(subject, &[Builtin::List]) {
                    Some((_, args)) => args[0],
                    None => {
                        if !subject.is_error(db) {
                            let pattern = self.builtin_of(Builtin::List, vec![Ty::error(db)]);
                            let kind = ErrorKind::NeverMatches { pattern, subject };
                            self.error(Site::Pat(id), kind);
                        }
                        Ty::error(db)
                    }
                };
                for &p in before.iter().chain(after) {
                    self.pattern(p, element);
                }
                let list = self.builtin_of(Builtin::List, vec![element]);
                if let Some(Some(binding)) = rest {
                    self.bindings[binding.index()] = Some(list);
                }
                list
            }
            Pat::Literal(literal) | Pat::Range { start: literal, .. } => {
                let ty = self.literal_ty(literal, Some(subject));
                if !self.literal_fits(literal, ty) {
                    self.error(Site::Pat(id), ErrorKind::Literal { ty });
                }
                if let Pat::Range { start, end } = body.pat(id) {
                    if !self.literal_fits(end, ty) {
                        self.error(Site::Pat(id), ErrorKind::Literal { ty });
                    } else if !self.is_discrete(ty) {
                        self.error(Site::Pat(id), ErrorKind::NotDiscrete { ty });
                    } else if let (Some(lo), Some(hi)) = (constant(start), constant(end))
                        && lo > hi
                    {
                        self.error(Site::Pat(id), ErrorKind::Decreasing);
                    }
                }
                self.narrow(id, ty, subject)
            }
            Pat::Or(alternatives) => {
                let types = alternatives
                    .iter()
                    .map(|&alt| self.pattern(alt, subject))
                    .collect();
                self.join_all(types)
            }
        }
    }

    /// The type a type pattern names. A generic tag without arguments takes
    /// them from the one member of the subject it can be (§3.6.1).
    fn pattern_type(&mut self, tref: TypeRefId, subject: Ty<'db>) -> Ty<'db> {
        let db = self.db;
        if let TypeRef::Named {
            target: TypeTarget::Item(item),
            args,
            ..
        } = self.body.type_ref(tref)
            && args.is_empty()
            && *item.kind(db) == ItemKind::Type
            && !type_header(db, self.program, *item).params.is_empty()
        {
            let identity = type_identity(db, self.program, *item);
            let levels: Vec<Ty<'db>> = subject
                .members(db)
                .into_iter()
                .filter(|m| matches!(m.kind(db), TyKind::Named(i, _) if *i == identity))
                .collect();
            let ty = match levels.as_slice() {
                [one] => *one,
                _ => {
                    self.error(Site::Type(tref), ErrorKind::CannotInfer);
                    self.err_ty()
                }
            };
            self.lower.types[tref.index()] = Some(ty);
            return ty;
        }
        self.lower_type(tref)
    }

    /// What a pattern of type `ty` narrows the subject to: the members of
    /// the subject that fit it, or `ty` itself when it is part of one.
    fn narrow(&mut self, id: PatId, ty: Ty<'db>, subject: Ty<'db>) -> Ty<'db> {
        let db = self.db;
        if self.fits(ty, subject) {
            return ty;
        }
        let members: Vec<Ty<'db>> = subject
            .members(db)
            .into_iter()
            .filter(|&m| self.fits(m, ty))
            .collect();
        if !members.is_empty() {
            return self.join_all(members);
        }
        let kind = ErrorKind::NeverMatches {
            pattern: ty,
            subject,
        };
        self.error(Site::Pat(id), kind);
        ty
    }
}

/// The value of an integer or code point literal, which a range compares.
fn constant(literal: &Literal) -> Option<i128> {
    match literal {
        Literal::Int(n) => i128::try_from(*n).ok(),
        Literal::CodePoint(c) => Some(i128::from(u32::from(*c))),
        _ => None,
    }
}

fn field_value(field: &FieldArg) -> ExprId {
    match field {
        FieldArg::Field { value, .. } | FieldArg::Spread(value) => *value,
    }
}

/// Whether a decimal literal is exact at `scale` digits and fits the
/// representation of `Fixed` (Compiler Architecture §11).
fn fixed_fits(text: &str, scale: u32, sign: i128) -> bool {
    if text.contains(['e', 'E']) {
        return false;
    }
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    let fraction = fraction.trim_end_matches('0');
    if fraction.len() > scale as usize {
        return false;
    }
    let digits = format!("{whole}{fraction:0<width$}", width = scale as usize);
    digits
        .parse::<i128>()
        .ok()
        .is_some_and(|n| i64::try_from(sign * n).is_ok())
}
