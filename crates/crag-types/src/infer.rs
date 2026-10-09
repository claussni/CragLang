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
//! written. Narrowing (§11.5.1) follows control flow: the inference keeps
//! the narrowed type of each binding where control is, splits it at a
//! test and joins it where paths meet. A function's errors are inferred
//! apart from its written success type (§11.5.2). A call of a generic
//! function infers its type arguments and is instantiated where it is
//! written; in a generic body the type parameters are opaque and the
//! slots of its bounds are candidates of calls (§11.5.3). Viable
//! candidates are ranked by specificity (§11.5.4). Union lifting and the
//! rest of M2 come later (§11.5); what needs them is reported as not
//! supported yet rather than guessed.

use crag_db::Db;
use crag_hir::{
    Arm, BindingId, BindingKind, Body, Expr, ExprId, FieldArg, ItemId, ItemKind, Literal, LocalFn,
    ModuleId, Name, Owner, PRELUDE, Pat, PatId, PatLiteral, Program, Resolution, Stmt, TypeArg,
    TypeRef, TypeRefId, TypeTarget, hir_body, module_scope, type_identity,
};

use crate::case::{Checker, PatternMatrix};
use crate::def::SigParam;
use crate::def::{
    HeaderKind, TypeLowerer, alias_target, prelude_item, signature, type_header, value_type,
};
use crate::generic::{CallSite, Slot, bind, instantiate, mentions, slots, type_param_names};
use crate::group::{error_type, result_type};
use crate::overload::{Ranked, most_specific};
use crate::relate::{declared_fields, fields_of, is_subtype, join, normalize};
use crate::result::{Callee, ErrorKind, InferenceResult, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// The types of one body. Runs apart from `body_types` for the queries
/// that ask for a success type or a value's type.
pub fn infer<'db>(db: &'db dyn Db, program: Program, owner: Owner<'db>) -> InferenceResult<'db> {
    infer_in_group(db, program, owner, &[])
}

/// The types of one body while the errors of its group are solved: a call
/// of a member of `group` gives its written success type and the errors
/// found so far (§11.5.2).
pub fn infer_in_group<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    group: &[(ItemId<'db>, Ty<'db>)],
) -> InferenceResult<'db> {
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
        narrowed: vec![None; body.bindings.len()],
        callees: Vec::new(),
        holes: Vec::new(),
        frames: Vec::new(),
        negative: false,
        bool_ty: prelude_type(db, program, "Bool"),
        empty: prelude_item(db, program, "Empty").map(|e| type_identity(db, program, e)),
        range: prelude_item(db, program, "Range").map(|e| type_identity(db, program, e)),
        range_from: prelude_item(db, program, "RangeFrom").map(|e| type_identity(db, program, e)),
        module: owner.module(db),
        group,
        error: error_type(db, program),
        generic: generic_owner.filter(|&item| *item.kind(db) == ItemKind::Function),
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
    /// Where control is: the type each binding is narrowed to there, if a
    /// test narrowed it (§3.13.4).
    narrowed: Flow<'db>,
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
    /// While a group's errors are solved, the errors of its members so
    /// far.
    group: &'a [(ItemId<'db>, Ty<'db>)],
    /// The prelude's `Error` (§8.1).
    error: Option<Ty<'db>>,
    /// The function being checked, whose type parameters are opaque here
    /// and whose slots its body calls (§11.5.3).
    generic: Option<ItemId<'db>>,
}

/// The narrowed type of each binding at a point of the body, by binding.
type Flow<'db> = Vec<Option<Ty<'db>>>;

struct Frame<'db> {
    /// The written result type; the `return`s are checked against it.
    expected: Option<Ty<'db>>,
    /// Without one, the types the `return`s give.
    returned: Vec<Ty<'db>>,
    /// Whether the errors are left to inference: a function's own frame
    /// whose written type names no error (§8.1).
    open: bool,
    /// In an open frame, the errors the body gives.
    errors: Vec<Ty<'db>>,
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

/// A function a call may resolve to, with its parameters as the call
/// sees them.
struct Candidate<'db> {
    function: ItemId<'db>,
    params: Vec<SigParam<'db>>,
    kind: CandidateKind,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CandidateKind {
    Plain,
    /// Its parameters name its type parameters.
    Generic,
    /// A slot of the generic function being checked, by index.
    Slot(u32),
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
        let open = expected.is_some_and(|e| self.errors_of(e).is_never(self.db));
        Some(self.frame(expected, root, open))
    }

    /// Checks a function or closure body against its written result type,
    /// or infers it from the body and its `return`s. An open frame adds
    /// the errors the body gives to its written type.
    fn frame(&mut self, expected: Option<Ty<'db>>, root: ExprId, open: bool) -> Ty<'db> {
        self.frames.push(Frame {
            expected,
            returned: Vec::new(),
            open,
            errors: Vec::new(),
        });
        let ty = self.infer(root, expected);
        self.result_value(Site::Expr(root), ty);
        let frame = self.frames.pop().expect("pushed above");
        match expected {
            Some(expected) => {
                let mut types = frame.errors;
                types.push(expected);
                self.join_all(types)
            }
            None => self.join_all(frame.returned),
        }
    }

    /// A value the innermost frame gives, by its last expression, a
    /// `return` or a `pass`: checked against the written type, where an
    /// open frame takes the errors apart.
    fn result_value(&mut self, site: Site, ty: Ty<'db>) {
        let Some(frame) = self.frames.last() else {
            return;
        };
        let Some(expected) = frame.expected else {
            self.frames.last_mut().expect("checked").returned.push(ty);
            return;
        };
        if !frame.open || self.fits(ty, expected) {
            self.expect(site, ty, expected);
            return;
        }
        let errors = self.errors_of(ty);
        let rest = self.successes_of(ty);
        if self.fits(rest, expected) {
            self.frames.last_mut().expect("checked").errors.push(errors);
        } else {
            self.error(
                site,
                ErrorKind::Mismatch {
                    expected,
                    found: ty,
                },
            );
        }
    }

    /// The members of `ty` that are errors.
    fn errors_of(&self, ty: Ty<'db>) -> Ty<'db> {
        let Some(error) = self.error else {
            return Ty::never(self.db);
        };
        let members = ty
            .members(self.db)
            .into_iter()
            .filter(|&m| !m.is_error(self.db) && self.fits(m, error))
            .collect();
        self.join_all(members)
    }

    /// The members of `ty` that are not errors.
    fn successes_of(&self, ty: Ty<'db>) -> Ty<'db> {
        let Some(error) = self.error else {
            return ty;
        };
        let members = ty
            .members(self.db)
            .into_iter()
            .filter(|&m| m.is_error(self.db) || !self.fits(m, error))
            .collect();
        self.join_all(members)
    }

    /// What a call of `function` gives, or none for a recursive function
    /// without a written success type.
    fn result_of(&self, function: ItemId<'db>) -> Option<Ty<'db>> {
        if let Some(&(_, errors)) = self.group.iter().find(|(m, _)| *m == function) {
            let success = signature(self.db, self.program, function).result?;
            return Some(self.join(success, errors));
        }
        result_type(self.db, self.program, function)
    }

    /// The success type of `function`, which a type-qualified call and
    /// the return-type filter compare (§5.6.1).
    fn success_of(&self, function: ItemId<'db>) -> Option<Ty<'db>> {
        match signature(self.db, self.program, function).result {
            Some(success) => Some(success),
            None => self.result_of(function).map(|r| self.successes_of(r)),
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
                    None,
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
                    None,
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
                Expr::Name {
                    name,
                    local: None,
                    item:
                        Some(Resolution::Value {
                            value: None,
                            functions,
                        }),
                } => {
                    let args = self.type_args(args);
                    let ty = self.function_value(id, *name, functions, Some(args), expected);
                    self.exprs[base.index()] = Some(ty);
                    ty
                }
                _ => {
                    let kind = ErrorKind::Unsupported("type arguments of values");
                    self.error(Site::Expr(id), kind);
                    self.err_ty()
                }
            },
            Expr::And(..) | Expr::Or(..) | Expr::Not(_) | Expr::Is { .. } => {
                let (holds, fails) = self.test(id);
                self.narrowed = self.merge(vec![holds, fails]);
                self.bool_ty
            }
            Expr::Range { start, end } => self.range(id, *start, *end, expected),
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
                let (holds, fails) = self.condition(*condition);
                self.narrowed = holds;
                let a = match otherwise {
                    Some(_) => self.infer(*then, expected),
                    None => self.synth(*then),
                };
                let after_then = std::mem::replace(&mut self.narrowed, fails);
                let b = match otherwise {
                    Some(otherwise) => self.infer(*otherwise, expected),
                    None => Ty::unit(db),
                };
                let after_else = std::mem::take(&mut self.narrowed);
                self.meet(vec![(a, after_then), (b, after_else)]);
                match otherwise {
                    Some(_) => self.join(a, b),
                    None => Ty::unit(db),
                }
            }
            Expr::Case { subject, arms } => self.case(*subject, arms, expected),
            Expr::Pass => {
                self.error(Site::Expr(id), ErrorKind::PassOutsideCase);
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
            if let Some(ty) = self.narrowed[binding.index()] {
                return ty;
            }
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
            }) => self.function_value(id, name, functions, None, expected),
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
        match self.result_of(function) {
            Some(ty) => ty,
            None => {
                self.error(Site::Expr(id), ErrorKind::RecursiveSuccess { function });
                self.err_ty()
            }
        }
    }

    /// An overloaded name used as a value: the function whose type fits
    /// the expected one, or the only one (§5.6.1). A generic function
    /// takes its type arguments from `targs` or from the expected type.
    fn function_value(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        targs: Option<Vec<Ty<'db>>>,
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let program = self.program;
        let mut candidates = self.candidates(functions);
        if let Some(targs) = &targs {
            self.with_type_args(id, &mut candidates, targs.len());
        }
        // Each candidate's type, if its type arguments are known.
        let typed: Vec<(usize, Ty<'db>, Vec<Ty<'db>>)> = candidates
            .iter()
            .enumerate()
            .filter_map(|(i, c)| {
                let params: Vec<Ty<'db>> = c.params.iter().map(|p| p.ty).collect();
                let result = match c.kind {
                    CandidateKind::Slot(k) => self.slots()[k as usize].result,
                    _ => self.result_of(c.function).unwrap_or_else(|| self.err_ty()),
                };
                let ty = Ty::new(db, TyKind::Fn { params, result });
                if c.kind != CandidateKind::Generic {
                    return Some((i, ty, Vec::new()));
                }
                let args = match &targs {
                    Some(targs) => targs.clone(),
                    None => {
                        let count = signature(db, program, c.function).type_params;
                        let mut args = vec![None; count];
                        for member in expected.into_iter().flat_map(|e| e.members(db)) {
                            if matches!(member.kind(db), TyKind::Fn { .. }) {
                                bind(db, program, c.function, ty, member, &mut args);
                            }
                        }
                        args.into_iter().collect::<Option<Vec<_>>>()?
                    }
                };
                let ty = crate::relate::subst(db, program, ty, c.function, &args);
                Some((i, ty, args))
            })
            .collect();
        let fitting: Vec<&(usize, Ty<'db>, Vec<Ty<'db>>)> = match expected {
            Some(expected) if typed.len() > 1 => typed
                .iter()
                .filter(|(_, ty, _)| self.fits(*ty, expected))
                .collect(),
            _ => typed.iter().collect(),
        };
        match fitting.as_slice() {
            [(i, ty, args)] => {
                let candidate = &candidates[*i];
                match candidate.kind {
                    CandidateKind::Plain => {
                        let function = candidate.function;
                        self.callees.push((id, Callee::Function(function)));
                        self.fn_ty(id, function)
                    }
                    CandidateKind::Slot(k) => {
                        self.callees.push((id, Callee::Slot(k)));
                        *ty
                    }
                    CandidateKind::Generic => {
                        let function = candidate.function;
                        if self.result_of(function).is_none() {
                            self.error(Site::Expr(id), ErrorKind::RecursiveSuccess { function });
                            return self.err_ty();
                        }
                        match instantiate(db, program, function, args, self.call_site()) {
                            Ok(instance) => self.callees.push((id, Callee::Instance(instance))),
                            Err(fit) => self.error(Site::Expr(id), ErrorKind::Unfit(fit)),
                        }
                        *ty
                    }
                }
            }
            [] => {
                let generic = candidates.iter().find(|c| c.kind == CandidateKind::Generic);
                let kind = match generic {
                    Some(c) if typed.is_empty() => ErrorKind::UninferredTypeArg {
                        function: c.function,
                        name: type_param_names(db, program, c.function)[0],
                    },
                    _ => ErrorKind::NoMatch {
                        name,
                        args: Vec::new(),
                    },
                };
                self.error(Site::Expr(id), kind);
                self.err_ty()
            }
            several => {
                let kind = ErrorKind::Ambiguous {
                    name,
                    candidates: several
                        .iter()
                        .map(|(i, ..)| candidates[*i].function)
                        .collect(),
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
                Expr::Name {
                    name,
                    local: None,
                    item:
                        Some(Resolution::Value {
                            value: None,
                            functions,
                        }),
                } => {
                    let targs = self.type_args(targs);
                    let ty = self.resolve(
                        id,
                        Some(*base),
                        *name,
                        functions,
                        Some(targs),
                        None,
                        args,
                        fields,
                        expected,
                        None,
                    );
                    self.exprs[callee.index()] = self.exprs[base.index()];
                    ty
                }
                _ => {
                    let kind = ErrorKind::Unsupported("type arguments of values");
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
            Expr::Str(_) | Expr::Literal(Literal::Str(_)) => builtin(&[Builtin::Str]),
            Expr::Literal(Literal::Bytes(_)) => builtin(&[Builtin::Bytes]),
            Expr::Literal(Literal::CodePoint(_)) => builtin(&[Builtin::CodePoint]),
            // A list literal fits when its items could fit the element
            // type.
            Expr::List(items) => any(&|k| match k {
                TyKind::Builtin(Builtin::List | Builtin::Set, args) => {
                    items.iter().all(|&item| self.could_fit(item, args[0]))
                }
                _ => false,
            }),
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
                .any(|element| match self.written_scale(*start) {
                    Some(scale) => fixed_scale(db, element) == Some(scale),
                    None => self.default_fits(*start, element),
                }),
            _ => true,
        }
    }

    /// Resolves a call of one of `functions` (§5.6.1) and checks its
    /// arguments: the candidates that fit, filtered by the success and the
    /// expected type, the most specific of one module (§11.5.4), and of
    /// those the ones the literals' default types fit. A generic function takes its
    /// type arguments from `targs` or infers them (§11.5.3); a slot of the
    /// generic function being checked is a candidate like a function.
    #[allow(clippy::too_many_arguments)]
    fn resolve(
        &mut self,
        id: ExprId,
        callee: Option<ExprId>,
        name: Name<'db>,
        functions: &[ItemId<'db>],
        targs: Option<Vec<Ty<'db>>>,
        receiver: Option<Arg<'db>>,
        args: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        expected: Option<Ty<'db>>,
        success: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
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
        let mut candidates = self.candidates(functions);
        if let Some(targs) = &targs {
            self.with_type_args(id, &mut candidates, targs.len());
        }
        // What each candidate's parameters are with the type arguments
        // the typed arguments give; those still unknown fit anything.
        let provisional: Vec<Vec<SigParam<'db>>> = candidates
            .iter()
            .map(|c| {
                let plan = self.plan(&c.params, &positional, &named, builds_record);
                let args = self.provisional_args(c, plan.as_ref(), targs.as_deref(), &positional);
                self.at_args(c, &args)
            })
            .collect();
        let chosen = if candidates.len() == 1 {
            Some(0)
        } else {
            let mut viable: Vec<usize> = (0..candidates.len())
                .filter(|&i| {
                    let params = &provisional[i];
                    self.plan(params, &positional, &named, builds_record)
                        .is_some_and(|p| self.plan_fits(params, &p, &positional, &named))
                        && self.bounds_hold(
                            &candidates[i],
                            &positional,
                            &named,
                            builds_record,
                            targs.as_deref(),
                        )
                })
                .collect();
            let gives = |this: &Self, i: usize| {
                let c = &candidates[i];
                let args = this.provisional_args(c, None, targs.as_deref(), &positional);
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
            // The most specific of one module's candidates (§5.6.1); of
            // those left, the ones the literals fit with their default types.
            let mut modules = Vec::new();
            if viable.len() > 1 {
                let ranked: Vec<Ranked<'db>> = viable
                    .iter()
                    .map(|&i| self.ranked(&candidates[i], &positional, &named, builds_record))
                    .collect();
                match most_specific(db, self.program, &ranked) {
                    Ok(best) => viable = best.into_iter().map(|k| viable[k]).collect(),
                    Err(several) => modules = several,
                }
            }
            if viable.len() > 1 && modules.is_empty() {
                let defaults: Vec<_> = viable
                    .iter()
                    .copied()
                    .filter(|&i| self.defaults_fit(&provisional[i], &positional))
                    .collect();
                if !defaults.is_empty() {
                    viable = defaults;
                }
            }
            match viable.as_slice() {
                _ if !modules.is_empty() => {
                    let modules = modules.iter().map(|m| m.path(db).clone()).collect();
                    self.error(Site::Expr(id), ErrorKind::SeveralModules { name, modules });
                    None
                }
                [one] => Some(*one),
                [] => {
                    let args = positional
                        .iter()
                        .map(|&a| match a {
                            Arg::Typed(_, t) | Arg::Receiver(_, t) => t,
                            Arg::Pending(e) => self.synth(e),
                        })
                        .collect();
                    if !self.any_error(&positional) && !candidates.is_empty() {
                        self.error(Site::Expr(id), ErrorKind::NoMatch { name, args });
                    }
                    None
                }
                several => {
                    let kind = ErrorKind::Ambiguous {
                        name,
                        candidates: several.iter().map(|&i| candidates[i].function).collect(),
                    };
                    self.error(Site::Expr(id), kind);
                    None
                }
            }
        };
        let Some(chosen) = chosen else {
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
        let candidate = candidates.swap_remove(chosen);
        let fields = fields.unwrap_or_default();
        let (params, result) = match candidate.kind {
            CandidateKind::Plain => {
                let function = candidate.function;
                self.apply(
                    id,
                    name,
                    &candidate.params,
                    &positional,
                    fields,
                    &named,
                    builds_record,
                );
                self.callees.push((id, Callee::Function(function)));
                (candidate.params, self.success(id, function))
            }
            CandidateKind::Slot(k) => {
                self.apply(
                    id,
                    name,
                    &candidate.params,
                    &positional,
                    fields,
                    &named,
                    builds_record,
                );
                self.callees.push((id, Callee::Slot(k)));
                let result = self.slots()[k as usize].result;
                (candidate.params, result)
            }
            CandidateKind::Generic => self.generic_call(
                id,
                name,
                &candidate,
                targs,
                positional,
                fields,
                named,
                builds_record,
                expected,
            ),
        };
        if let Some(callee) = callee {
            let params = params.iter().map(|p| p.ty).collect();
            self.exprs[callee.index()] = Some(Ty::new(db, TyKind::Fn { params, result }));
        }
        result
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
    fn candidates(&self, functions: &[ItemId<'db>]) -> Vec<Candidate<'db>> {
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
    fn mapping_rules(&mut self, id: ExprId, function: ItemId<'db>, args: &[Ty<'db>]) {
        let db = self.db;
        let mapping = function.module(db).path(db) == PRELUDE
            && matches!(function.name(db).text(db).as_str(), "check" | "expect");
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
    fn with_type_args(&mut self, id: ExprId, candidates: &mut Vec<Candidate<'db>>, count: usize) {
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
    fn slots(&self) -> &'db [Slot<'db>] {
        match self.generic {
            Some(item) => slots(self.db, self.program, item),
            None => &[],
        }
    }

    /// Where the body is written, for the slot fillings of its calls.
    fn call_site(&self) -> CallSite<'db> {
        CallSite {
            module: self.module,
            caller: self.generic,
        }
    }

    /// The type arguments of a candidate that the given ones and the typed
    /// arguments fix.
    fn provisional_args(
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
    fn at_args(&self, candidate: &Candidate<'db>, args: &[Option<Ty<'db>>]) -> Vec<SigParam<'db>> {
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

    fn known(&self, args: &[Option<Ty<'db>>]) -> Vec<Ty<'db>> {
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

    /// A call of a generic function: infers its type arguments from the
    /// typed arguments, the context, and then the arguments that take
    /// their type from the context, checks the arguments, and instantiates
    /// the function where the call is written. Returns the parameters and
    /// the result with the type arguments.
    #[allow(clippy::too_many_arguments)]
    fn generic_call(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        candidate: &Candidate<'db>,
        targs: Option<Vec<Ty<'db>>>,
        mut positional: Vec<Arg<'db>>,
        fields: &[FieldArg<'db>],
        mut named: Vec<(Name<'db>, Arg<'db>)>,
        builds_record: bool,
        expected: Option<Ty<'db>>,
    ) -> (Vec<SigParam<'db>>, Ty<'db>) {
        let db = self.db;
        let program = self.program;
        let function = candidate.function;
        let plan = self.plan(&candidate.params, &positional, &named, builds_record);
        let mut args =
            self.provisional_args(candidate, plan.as_ref(), targs.as_deref(), &positional);
        let result = self.result_of(function);
        if args.iter().any(Option::is_none)
            && let (Some(expected), Some(result)) = (expected, result)
        {
            let mut from_context = args.clone();
            bind(db, program, function, result, expected, &mut from_context);
            for (arg, context) in args.iter_mut().zip(from_context) {
                if arg.is_none() {
                    *arg = context;
                }
            }
        }
        // The arguments that take their type from the context, in order:
        // a closure gets the parameter types known so far and gives its
        // result.
        if let Some(Plan::Params(given)) = &plan {
            for (i, g) in given.iter().enumerate() {
                let Some(g) = *g else { continue };
                let param = candidate.params[i].ty;
                let unknown = |j: u32| args.get(j as usize).is_some_and(Option::is_none);
                if !mentions(db, param, function, &unknown) {
                    continue;
                }
                let arg = if g < positional.len() {
                    &mut positional[g]
                } else {
                    &mut named[g - positional.len()].1
                };
                let Arg::Pending(e) = *arg else { continue };
                let partial = self.at_args(candidate, &args)[i].ty;
                let ty = match self.body.expr(e) {
                    Expr::Closure { .. } => self.infer(e, Some(partial)),
                    _ => self.synth(e),
                };
                bind(db, program, function, param, ty, &mut args);
                *arg = Arg::Typed(e, ty);
            }
        }
        let names = type_param_names(db, program, function);
        let mut uninferred = false;
        for (i, arg) in args.iter_mut().enumerate() {
            if arg.is_none() {
                let name = names.get(i).copied().unwrap_or(name);
                self.error(
                    Site::Expr(id),
                    ErrorKind::UninferredTypeArg { function, name },
                );
                uninferred = true;
                *arg = Some(self.err_ty());
            }
        }
        let args = self.known(&args);
        let params = self.at_args(
            candidate,
            &args.iter().copied().map(Some).collect::<Vec<_>>(),
        );
        self.apply(
            id,
            name,
            &params,
            &positional,
            fields,
            &named,
            builds_record,
        );
        self.mapping_rules(id, function, &args);
        if !uninferred && !args.iter().any(|a| a.is_error(db)) {
            match instantiate(db, program, function, &args, self.call_site()) {
                Ok(instance) => self.callees.push((id, Callee::Instance(instance))),
                Err(fit) => self.error(Site::Expr(id), ErrorKind::Unfit(fit)),
            }
        }
        let result = match result {
            Some(result) => crate::relate::subst(db, program, result, function, &args),
            None => {
                self.error(Site::Expr(id), ErrorKind::RecursiveSuccess { function });
                self.err_ty()
            }
        };
        (params, result)
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
        params: &[SigParam<'db>],
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
    ) -> Option<Plan> {
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
        params: &[SigParam<'db>],
        plan: &Plan,
        positional: &[Arg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
    ) -> bool {
        let arg_fits = |arg: Arg<'db>, param: Ty<'db>| match arg {
            Arg::Typed(_, t) | Arg::Receiver(_, t) => self.fits(t, param),
            Arg::Pending(e) => self.could_fit(e, param),
        };
        match plan {
            Plan::Params(given) => given.iter().zip(params).all(|(g, p)| match g {
                Some(i) if *i < positional.len() => arg_fits(positional[*i], p.ty),
                Some(i) => arg_fits(named[*i - positional.len()].1, p.ty),
                None => true,
            }),
            Plan::Record => {
                let record = params[positional.len()].ty;
                let fields = fields_of(self.db, self.program, record).unwrap_or_default();
                positional
                    .iter()
                    .zip(params)
                    .all(|(&a, p)| arg_fits(a, p.ty))
                    && named
                        .iter()
                        .all(|(n, a)| fields.iter().any(|(f, t)| f == n && arg_fits(*a, *t)))
            }
        }
    }

    fn defaults_fit(&self, params: &[SigParam<'db>], positional: &[Arg<'db>]) -> bool {
        positional.iter().zip(params).all(|(a, p)| match a {
            Arg::Pending(e) => self.default_fits(*e, p.ty),
            _ => true,
        })
    }

    /// Checks the arguments of a call against the chosen function's
    /// parameters.
    #[allow(clippy::too_many_arguments)]
    fn apply(
        &mut self,
        id: ExprId,
        name: Name<'db>,
        params: &[SigParam<'db>],
        positional: &[Arg<'db>],
        fields: &[FieldArg<'db>],
        named: &[(Name<'db>, Arg<'db>)],
        builds_record: bool,
    ) {
        let db = self.db;
        let negative = self.negative;
        self.negative = name.text(db) == "negate";
        let plan = self.plan(params, positional, named, builds_record);
        match plan {
            Some(Plan::Params(given)) => {
                for (i, g) in given.iter().enumerate() {
                    let Some(g) = *g else { continue };
                    let arg = if g < positional.len() {
                        positional[g]
                    } else {
                        named[g - positional.len()].1
                    };
                    self.check_arg(arg, params[i].ty);
                }
            }
            Some(Plan::Record) => {
                for (&arg, param) in positional.iter().zip(params) {
                    self.check_arg(arg, param.ty);
                }
                let record = params[positional.len()].ty;
                self.build_record(id, record, fields);
            }
            None => {
                // Only a lone candidate gets here; say what is wrong.
                let mut seen = vec![false; params.len()];
                for (i, &arg) in positional.iter().enumerate() {
                    match params.get(i) {
                        Some(param) => {
                            seen[i] = true;
                            self.check_arg(arg, param.ty);
                        }
                        None => self.check_arg(arg, Ty::error(db)),
                    }
                }
                if positional.len() > params.len() {
                    let kind = ErrorKind::ArgCount {
                        expected: params.len(),
                        found: positional.len(),
                    };
                    self.error(Site::Expr(id), kind);
                }
                for field in fields {
                    let value = field_value(field);
                    let param = match field {
                        FieldArg::Field { path, .. } if path.len() == 1 => {
                            params.iter().position(|p| p.name == Some(path[0]))
                        }
                        _ => None,
                    };
                    match param {
                        Some(i) if !seen[i] => {
                            seen[i] = true;
                            self.check(value, params[i].ty);
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
                for (i, param) in params.iter().enumerate() {
                    if !seen[i] && !param.default {
                        let kind = match param.name {
                            Some(name) => ErrorKind::MissingArg { name },
                            None => ErrorKind::ArgCount {
                                expected: params.len(),
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
        let inside = self.without_vars();
        let outside = std::mem::replace(&mut self.narrowed, inside);
        let result = self.frame(result, root, false);
        self.narrowed = outside;
        Ty::new(
            db,
            TyKind::Fn {
                params: param_tys,
                result,
            },
        )
    }

    // Narrowing.

    /// Checks a condition and returns the narrowings where it holds and
    /// where it does not.
    fn condition(&mut self, id: ExprId) -> (Flow<'db>, Flow<'db>) {
        match self.body.expr(id) {
            Expr::And(..) | Expr::Or(..) | Expr::Not(_) | Expr::Is { .. } => {
                let outcomes = self.test(id);
                self.exprs[id.index()] = Some(self.bool_ty);
                outcomes
            }
            _ => {
                let bool_ty = self.bool_ty;
                self.check(id, bool_ty);
                (self.narrowed.clone(), self.narrowed.clone())
            }
        }
    }

    /// `and`, `or`, `not` and `is`, which narrow (§3.13.4): the right
    /// operand of `and` sees what the left one established, and that of
    /// `or` what the left one ruled out.
    fn test(&mut self, id: ExprId) -> (Flow<'db>, Flow<'db>) {
        match self.body.expr(id) {
            Expr::And(a, b) => {
                let (a_holds, a_fails) = self.condition(*a);
                self.narrowed = a_holds;
                let (b_holds, b_fails) = self.condition(*b);
                (b_holds, self.merge(vec![a_fails, b_fails]))
            }
            Expr::Or(a, b) => {
                let (a_holds, a_fails) = self.condition(*a);
                self.narrowed = a_fails;
                let (b_holds, b_fails) = self.condition(*b);
                (self.merge(vec![a_holds, b_holds]), b_fails)
            }
            Expr::Not(a) => {
                let (holds, fails) = self.condition(*a);
                (fails, holds)
            }
            Expr::Is { expr, ty } => {
                let subject = self.synth(*expr);
                let target = self.pattern_type(*ty, subject);
                let start = self.narrowed.clone();
                if subject.is_error(self.db) || target.is_error(self.db) {
                    return (start.clone(), start);
                }
                let Some(matched) = self.refine(subject, target) else {
                    let kind = ErrorKind::NeverMatches {
                        pattern: target,
                        subject,
                    };
                    self.error(Site::Expr(id), kind);
                    return (start.clone(), start);
                };
                let Some(binding) = self.narrowable(*expr) else {
                    return (start.clone(), start);
                };
                let (mut holds, mut fails) = (start.clone(), start);
                holds[binding.index()] = Some(matched);
                fails[binding.index()] = Some(self.rest(subject, target));
                (holds, fails)
            }
            _ => unreachable!("only tests are tested"),
        }
    }

    /// The binding a test of `expr` narrows: a `let`, a `var` or a
    /// parameter read by its name. Refs and fields are never narrowed.
    fn narrowable(&self, expr: ExprId) -> Option<BindingId> {
        let Expr::Name {
            local: Some(binding),
            ..
        } = self.body.expr(expr)
        else {
            return None;
        };
        let kind = self.body.binding(*binding).kind;
        matches!(
            kind,
            BindingKind::Let | BindingKind::Var | BindingKind::Param
        )
        .then_some(*binding)
    }

    /// The type a value of `subject` has when it is also one of `target`:
    /// `target` itself when it is one type that fits the subject, else
    /// the members of the subject that `target` overlaps; none when no
    /// value is of both.
    ///
    /// A union of finer types than the subject's members is never made,
    /// because a union value is tagged with the member it was made as.
    fn refine(&self, subject: Ty<'db>, target: Ty<'db>) -> Option<Ty<'db>> {
        let db = self.db;
        let targets = target.members(db);
        if targets.len() == 1 && self.fits(target, subject) {
            return Some(target);
        }
        let members: Vec<Ty<'db>> = subject
            .members(db)
            .into_iter()
            .filter(|&m| self.fits(m, target) || targets.iter().any(|&t| self.fits(t, m)))
            .collect();
        (!members.is_empty()).then(|| self.join_all(members))
    }

    /// The members of `subject` whose values are never of `target`.
    fn rest(&self, subject: Ty<'db>, target: Ty<'db>) -> Ty<'db> {
        let members = subject
            .members(self.db)
            .into_iter()
            .filter(|&m| !self.fits(m, target))
            .collect();
        self.join_all(members)
    }

    /// The members of `subject` some value of which no pattern of the
    /// matrix matches.
    fn unmatched(&self, matrix: &PatternMatrix<'db>, subject: Ty<'db>) -> Ty<'db> {
        let checker = Checker::new(self.db, self.program);
        let members = subject
            .members(self.db)
            .into_iter()
            .filter(|&m| checker.missing_example(matrix, m).is_some())
            .collect();
        self.join_all(members)
    }

    /// The pattern `id` as the case checker sees it, its alternatives
    /// apart; none if it did not type.
    fn lowered(&self, id: PatId) -> Option<Vec<crate::case::Pattern<'db>>> {
        let checker = Checker::new(self.db, self.program);
        let alternatives = match self.body.pat(id) {
            Pat::Or(alternatives) => alternatives.clone(),
            _ => vec![id],
        };
        alternatives
            .into_iter()
            .map(|alt| checker.lower(self.body, &self.pats, alt))
            .collect()
    }

    /// Where control paths meet: a binding stays narrowed if every path
    /// that gets here narrowed it, to the union of what they narrowed it
    /// to.
    fn merge(&self, flows: Vec<Flow<'db>>) -> Flow<'db> {
        let mut flows = flows.into_iter();
        let Some(mut merged) = flows.next() else {
            return self.narrowed.clone();
        };
        for flow in flows {
            for (m, f) in merged.iter_mut().zip(flow) {
                *m = match (*m, f) {
                    (Some(a), Some(b)) => Some(self.join(a, b)),
                    _ => None,
                };
            }
        }
        merged
    }

    /// Continues after branches, each with its type and the narrowings at
    /// its end; a branch of type `Never` does not get here.
    fn meet(&mut self, ends: Vec<(Ty<'db>, Flow<'db>)>) {
        let db = self.db;
        let (reached, left): (Vec<_>, Vec<_>) =
            ends.into_iter().partition(|(ty, _)| !ty.is_never(db));
        self.narrowed = match reached.is_empty() {
            true => left.into_iter().next().map(|(_, f)| f).unwrap_or_default(),
            false => self.merge(reached.into_iter().map(|(_, f)| f).collect()),
        };
    }

    /// Narrowings that do not hold in code that may run later, such as a
    /// closure: those of `var`s.
    fn without_vars(&self) -> Flow<'db> {
        let body = self.body;
        self.narrowed
            .iter()
            .enumerate()
            .map(|(i, &ty)| match body.bindings[i].kind {
                BindingKind::Var => None,
                _ => ty,
            })
            .collect()
    }

    /// `case` (§7.2): a subject that is a binding is narrowed in each arm
    /// to what its pattern matches of the values no earlier arm took. A
    /// `pass` arm gives those values to the caller (§8.2).
    fn case(&mut self, subject: ExprId, arms: &[Arm], expected: Option<Ty<'db>>) -> Ty<'db> {
        let db = self.db;
        let subject_ty = self.synth(subject);
        let binding = self.narrowable(subject);
        let start = self.narrowed.clone();
        let mut remaining = Some(subject_ty);
        let mut matrix = PatternMatrix::default();
        let mut types = Vec::new();
        let mut ends = Vec::new();
        let mut typed = true;
        for arm in arms {
            self.narrowed = start.clone();
            typed &= self.pattern_checks(arm.pat, subject_ty);
            // What the arm matches of what is left; an arm that never
            // matches, which is reported, narrows nothing.
            let matched = self.pats[arm.pat.index()]
                .filter(|m| !m.is_error(db))
                .and_then(|m| self.refine(remaining.unwrap_or(subject_ty), m));
            if let (Some(binding), Some(matched)) = (binding, matched) {
                self.narrowed[binding.index()] = Some(matched);
            }
            if let Some(guard) = arm.guard {
                let (holds, _) = self.condition(guard);
                self.narrowed = holds;
            }
            let ty = match self.body.expr(arm.body) {
                Expr::Pass => {
                    let passed = matched.unwrap_or(subject_ty);
                    self.result_value(Site::Expr(arm.body), passed);
                    let never = Ty::never(db);
                    self.exprs[arm.body.index()] = Some(passed);
                    never
                }
                _ => self.infer(arm.body, expected),
            };
            types.push(ty);
            ends.push((ty, std::mem::take(&mut self.narrowed)));
            if arm.guard.is_none() {
                remaining = match (remaining, self.lowered(arm.pat)) {
                    (Some(r), Some(patterns)) => {
                        for pattern in patterns {
                            matrix.push(pattern);
                        }
                        Some(self.unmatched(&matrix, r))
                    }
                    // Past an arm that did not type, nothing is known.
                    _ => None,
                };
            }
        }
        if typed {
            self.coverage(subject, subject_ty, arms);
        }
        match ends.is_empty() {
            true => self.narrowed = start,
            false => self.meet(ends),
        }
        self.join_all(types)
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
                if self.pattern_checks(*pat, ty) {
                    self.irrefutable(*pat, ty);
                }
                if ty.is_never(db) { ty } else { unit }
            }
            Stmt::LetElse {
                pat,
                ty,
                value,
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
                if let Some(binding) = binding {
                    // The `else` part sees the values the pattern misses.
                    let mut matrix = PatternMatrix::default();
                    let rest = match self.lowered(*pat) {
                        Some(patterns) => {
                            for pattern in patterns {
                                matrix.push(pattern);
                            }
                            let tested = self.rest(value_ty, target);
                            let missed = self.unmatched(&matrix, target);
                            self.join(tested, missed)
                        }
                        None => value_ty,
                    };
                    self.narrowed[binding.index()] = Some(rest);
                }
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
                self.narrowed = start;
                if let Some(binding) = binding
                    && let Some(matched) = self.pats[pat.index()]
                    && let Some(matched) = self.refine(value_ty, matched)
                {
                    self.narrowed[binding.index()] = Some(matched);
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
            Stmt::Emit { value, .. } => {
                self.error(Site::Expr(*value), ErrorKind::Unsupported("signals"));
                self.synth(*value);
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
    fn written_scale(&self, id: ExprId) -> Option<u32> {
        match self.body.expr(id) {
            Expr::Literal(Literal::Float(text)) => decimals(text),
            Expr::Call { callee, args, .. } if args.len() == 1 && self.is_negation(*callee) => {
                self.written_scale(args[0])
            }
            _ => None,
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
    /// `CodePoint`, `Fixed`, and types with a `compare` and a `next` in
    /// scope.
    /// Type parameters pass; their bounds are checked with M2.
    fn is_discrete(&self, ty: Ty<'db>) -> bool {
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
            Expr::Literal(literal) => constant(literal, scale),
            Expr::Call { callee, args, .. } if args.len() == 1 && self.is_negation(*callee) => {
                self.constant_expr(args[0], scale).map(|n| -n)
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
        if function.generic {
            let kind = ErrorKind::Unsupported("generic local functions");
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
                let ty = self.literal_ty(&literal.literal, Some(subject));
                if !self.pattern_literal_fits(literal, ty) {
                    self.error(Site::Pat(id), ErrorKind::Literal { ty });
                }
                if let Pat::Range { start, end } = body.pat(id) {
                    let scale = fixed_scale(self.db, ty);
                    if !self.pattern_literal_fits(end, ty) {
                        self.error(Site::Pat(id), ErrorKind::Literal { ty });
                    } else if !self.is_discrete(ty) {
                        self.error(Site::Pat(id), ErrorKind::NotDiscrete { ty });
                    } else if let Some(scale) = scale
                        && let Some(written) =
                            [start, end].into_iter().find_map(|l| match &l.literal {
                                Literal::Float(text) => decimals(text).filter(|&d| d != scale),
                                _ => None,
                            })
                    {
                        let found = self.builtin(Builtin::Fixed(written));
                        let kind = ErrorKind::Mismatch {
                            expected: ty,
                            found,
                        };
                        self.error(Site::Pat(id), kind);
                    } else if let (Some(lo), Some(hi)) = (signed(start, scale), signed(end, scale))
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

    /// Checks a pattern as `pattern` does and says whether it typed
    /// without errors, so that coverage is only checked for patterns that
    /// did.
    fn pattern_checks(&mut self, id: PatId, subject: Ty<'db>) -> bool {
        let before = self.lower.errors.len();
        self.pattern(id, subject);
        self.lower.errors.len() == before && !subject.is_error(self.db)
    }

    /// Reports the arms of a `case` that earlier arms cover, and a value
    /// no arm covers (§7.2).
    fn coverage(&mut self, subject: ExprId, ty: Ty<'db>, arms: &[Arm]) {
        let checker = Checker::new(self.db, self.program);
        let body = self.body;
        let mut lowered = Vec::new();
        for arm in arms {
            let alternatives = match body.pat(arm.pat) {
                Pat::Or(alternatives) => alternatives.clone(),
                _ => vec![arm.pat],
            };
            let mut patterns = Vec::new();
            for id in alternatives {
                let Some(pattern) = checker.lower(body, &self.pats, id) else {
                    return;
                };
                patterns.push((id, pattern));
            }
            lowered.push(patterns);
        }
        let mut matrix = PatternMatrix::default();
        for (arm, alternatives) in arms.iter().zip(lowered) {
            let mut covered = matrix.clone();
            let mut unreachable = Vec::new();
            let count = alternatives.len();
            for (id, pattern) in alternatives {
                if !checker.is_useful(&covered, &pattern, ty) {
                    unreachable.push(id);
                }
                covered.push(pattern);
            }
            if unreachable.len() == count {
                self.error(Site::Pat(arm.pat), ErrorKind::Unreachable);
            } else {
                for id in unreachable {
                    self.error(Site::Pat(id), ErrorKind::Unreachable);
                }
            }
            if arm.guard.is_none() {
                matrix = covered;
            }
        }
        if let Some(missing) = checker.missing_example(&matrix, ty) {
            let missing = missing.display(self.db);
            self.error(Site::Expr(subject), ErrorKind::NotExhaustive { missing });
        }
    }

    /// Reports a value of `ty` the pattern of a `let` or a `for` does not
    /// match.
    fn irrefutable(&mut self, id: PatId, ty: Ty<'db>) {
        let checker = Checker::new(self.db, self.program);
        let Some(pattern) = checker.lower(self.body, &self.pats, id) else {
            return;
        };
        let mut matrix = PatternMatrix::default();
        matrix.push(pattern);
        if let Some(missing) = checker.missing_example(&matrix, ty) {
            let missing = missing.display(self.db);
            self.error(Site::Pat(id), ErrorKind::Refutable { missing });
        }
    }

    /// Whether a literal of a pattern, with its sign, fits `ty`.
    fn pattern_literal_fits(&mut self, literal: &PatLiteral, ty: Ty<'db>) -> bool {
        let outer = std::mem::replace(&mut self.negative, literal.negative);
        let fits = self.literal_fits(&literal.literal, ty);
        self.negative = outer;
        fits
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

/// The value of an integer, decimal or code point literal, in units of
/// `scale` for a `Fixed`.
pub fn constant(literal: &Literal, scale: Option<u32>) -> Option<i128> {
    match (literal, scale) {
        (Literal::Int(n), scale) => i128::try_from(*n)
            .ok()?
            .checked_mul(10i128.checked_pow(scale.unwrap_or(0))?),
        (Literal::Float(text), Some(scale)) => fixed_value(text, scale),
        (Literal::CodePoint(c), None) => Some(i128::from(u32::from(*c))),
        _ => None,
    }
}

/// The value of a literal of a pattern, with its sign.
pub(crate) fn signed(literal: &PatLiteral, scale: Option<u32>) -> Option<i128> {
    let value = constant(&literal.literal, scale)?;
    Some(if literal.negative { -value } else { value })
}

/// The scale `S` of a `Fixed[S]`.
pub(crate) fn fixed_scale(db: &dyn Db, ty: Ty<'_>) -> Option<u32> {
    match ty.as_builtin(db) {
        Some((Builtin::Fixed(scale), _)) => Some(scale),
        _ => None,
    }
}

/// The number of decimals a decimal literal is written with, trailing
/// zeros included.
fn decimals(text: &str) -> Option<u32> {
    if text.contains(['e', 'E']) {
        return None;
    }
    let (_, fraction) = text.split_once('.')?;
    u32::try_from(fraction.len()).ok()
}

fn field_value(field: &FieldArg) -> ExprId {
    match field {
        FieldArg::Field { value, .. } | FieldArg::Spread(value) => *value,
    }
}

/// Whether a decimal literal is exact at `scale` digits and fits the
/// representation of `Fixed` (Compiler Architecture §11).
fn fixed_fits(text: &str, scale: u32, sign: i128) -> bool {
    fixed_value(text, scale).is_some_and(|n| i64::try_from(sign * n).is_ok())
}

/// A decimal literal in units of 10^-`scale`, if it is exact at `scale`
/// digits.
fn fixed_value(text: &str, scale: u32) -> Option<i128> {
    if text.contains(['e', 'E']) {
        return None;
    }
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    let fraction = fraction.trim_end_matches('0');
    if fraction.len() > scale as usize {
        return None;
    }
    let digits = format!("{whole}{fraction:0<width$}", width = scale as usize);
    digits.parse::<i128>().ok()
}
