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
//! candidates are ranked by specificity (§11.5.4). A call whose union
//! arguments no candidate takes whole is lifted: split by their members
//! and recorded as a dispatch (§11.5.5). Once a body is inferred, its
//! effects are found by a walk over it (§11.5.7), and where its values go
//! by another (§11.5.8). The rest of M2 comes
//! later (§11.5); what needs it is reported as not supported yet rather
//! than guessed.

use std::collections::HashMap;

use crag_db::Db;
use crag_hir::{
    Arm, BindingId, BindingKind, Body, Expr, ExprId, FieldArg, ItemId, ItemKind, Literal, LocalFn,
    ModuleId, Name, Owner, PRELUDE, Pat, PatId, PatLiteral, Program, Resolution, Stmt, TypeArg,
    TypeRef, TypeRefId, TypeTarget, hir_body, module_scope, type_identity,
};

use crate::case::{Checker, PatternMatrix};
use crate::def::SigParam;
use crate::def::{
    HeaderKind, TypeLowerer, alias_target, place_positional, prelude_item, signature, type_header,
    value_type,
};
use crate::effect::{EffectSet, Walker};
use crate::escape::{EscapeLevel, EscapeWalker, Escapes};
use crate::generic::{
    CallSite, Filling, Slot, bind, function_at, instantiate, mentions, slots, type_param_names,
};
use crate::group::{
    GroupMember, error_type, function_effects, group_of, param_escapes, result_type,
};
use crate::overload::{Ranked, most_specific};
use crate::relate::{declared_fields, fields_of, is_subtype, join, normalize};
use crate::result::{
    Callee, Dispatch, DispatchArm, ErrorKind, InferenceResult, Iteration, Optional, Site, TypeError,
};
use crate::ty::{Builtin, Ty, TyKind};

mod call;
mod closure;
mod construct;
mod narrow;
mod pattern;
mod select;
mod stmt;
mod value;

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
    group: &[GroupMember<'db>],
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
        optional: Vec::new(),
        iterations: Vec::new(),
        shows: Vec::new(),
        sent: Vec::new(),
        trap_handlers: Vec::new(),
        typed: HashMap::new(),
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
        embed: generic_owner.filter(|&item| *item.kind(db) == ItemKind::Embed),
        in_type: generic_owner.is_some_and(|item| *item.kind(db) == ItemKind::Type),
    };
    let result = match owner {
        Owner::Item(item) => match *item.kind(db) {
            ItemKind::Function => cx.function(),
            ItemKind::Value | ItemKind::Embed => {
                let ty = cx.module_value();
                // Module-level bindings hold only Solid values (§5.5); a
                // REPL session's may hold any.
                if let (Some(ty), Some(root)) = (ty, body.root)
                    && item.module(db).path(db) != crag_hir::SESSION
                    && let Err(why) = crate::marker::solid(db, program, ty)
                {
                    let why = why.clone();
                    cx.lower
                        .error(Site::Expr(root), ErrorKind::ValueNotSolid { ty, why });
                }
                ty
            }
            ItemKind::Type => {
                cx.type_defaults(item);
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
    // Effects matter for what runs: functions, tests, module-level values,
    // which compile-time evaluation runs only without them (§3.14, §18.4),
    // and the defaults of fields, which must have none.
    let effects = match owner {
        Owner::Item(item)
            if !matches!(*item.kind(db), ItemKind::Function | ItemKind::Type)
                && !item.kind(db).is_value() =>
        {
            EffectSet::NONE
        }
        _ => {
            let effects_of = |f: ItemId<'db>| cx.effects_of(f);
            let walker = Walker::new(
                db,
                program,
                body,
                &cx.exprs,
                &cx.bindings,
                &cx.callees,
                &effects_of,
            );
            let walked = walker.walk_body(body.pure);
            cx.lower.errors.extend(walked.errors);
            walked.effects
        }
    };
    // Module-level values hold closures too, whose captures conversion
    // needs (§11.5.9).
    let escapes = match owner {
        Owner::Item(item)
            if !matches!(*item.kind(db), ItemKind::Function | ItemKind::Type)
                && !item.kind(db).is_value() =>
        {
            Escapes::default()
        }
        _ => {
            let summary_of = |f: ItemId<'db>| cx.escapes_of(f);
            let names_of = |f: ItemId<'db>| -> Vec<(Option<Name<'db>>, bool)> {
                signature(db, program, f)
                    .params
                    .iter()
                    .map(|p| (p.name, p.default))
                    .collect()
            };
            let walker =
                EscapeWalker::new(db, body, &cx.bindings, &cx.callees, &summary_of, &names_of);
            let walked = walker.walk_body();
            cx.lower.errors.extend(walked.errors);
            let captures = crate::marker::capture_errors(db, program, body, &cx.bindings);
            cx.lower.errors.extend(captures);
            walked.escapes
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
        optional: cx.optional,
        iterations: cx.iterations,
        shows: cx.shows,
        trap_handlers: cx.trap_handlers,
        sent: cx.sent,
        effects,
        escapes,
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
    optional: Vec<(ExprId, Optional<'db>)>,
    iterations: Vec<(ExprId, Iteration<'db>)>,
    shows: Vec<(ExprId, Filling<'db>)>,
    trap_handlers: Vec<(ExprId, Ty<'db>)>,
    sent: Vec<ExprId>,
    /// Expressions already typed, which their next check takes as they
    /// are: the field values a construction infers its type arguments
    /// from.
    typed: HashMap<ExprId, Ty<'db>>,
    /// The function and closures being checked, innermost last, for
    /// `return`.
    frames: Vec<Frame<'db>>,
    /// Whether the body is a type's, whose conditions and handlers are
    /// typed together: its constructions are checked when they run.
    in_type: bool,
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
    group: &'a [GroupMember<'db>],
    /// The prelude's `Error` (§8.1).
    error: Option<Ty<'db>>,
    /// The function being checked, whose type parameters are opaque here
    /// and whose slots its body calls (§11.5.3).
    generic: Option<ItemId<'db>>,
    /// The `embed` being checked, whose resource its body is.
    embed: Option<ItemId<'db>>,
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

/// Which candidate a call resolves to.
enum Selection {
    One(usize),
    NoneViable,
    Several(Vec<usize>),
}

/// A lifted call's split arguments, their members, and per combination
/// the candidate chosen with the arguments it sees.
type Lifted<'db> = (Vec<usize>, Vec<Vec<Ty<'db>>>, Vec<(usize, Vec<Arg<'db>>)>);

/// The first combination of a lifted call that does not resolve.
enum Failure<'db> {
    None(Vec<Ty<'db>>),
    Several(Vec<ItemId<'db>>),
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

    /// Whether an expression names a `dur` binding anywhere inside it:
    /// one declared `dur`, or a parameter of type `Dur[T]` (§21.2). The
    /// bindings inside `root` are typed when this runs, after the body.
    fn touches_dur(&self, root: ExprId) -> bool {
        let mut pending = vec![root];
        while let Some(e) = pending.pop() {
            if let Expr::Name {
                local: Some(binding),
                ..
            } = self.body.expr(e)
            {
                if self.body.binding(*binding).kind == BindingKind::Dur {
                    return true;
                }
                let ty = self.bindings.get(binding.index()).copied().flatten();
                if let Some(ty) = ty
                    && matches!(ty.as_builtin(self.db), Some((Builtin::Dur, _)))
                {
                    return true;
                }
            }
            pending.extend(self.body.children(e));
        }
        false
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
        if let Some(member) = self.group.iter().find(|m| m.function == function) {
            let success = signature(self.db, self.program, function).result?;
            return Some(self.join(success, member.errors));
        }
        result_type(self.db, self.program, function)
    }

    /// The levels of `function`'s parameters: of its group's solution so
    /// far while that is solved.
    fn escapes_of(&self, function: ItemId<'db>) -> Vec<EscapeLevel> {
        match self.group.iter().find(|m| m.function == function) {
            Some(member) => member.escapes.clone(),
            None => param_escapes(self.db, self.program, function).clone(),
        }
    }

    /// The effects of `function`: of its group's solution so far while
    /// that is solved.
    fn effects_of(&self, function: ItemId<'db>) -> EffectSet {
        match self.group.iter().find(|m| m.function == function) {
            Some(member) => member.effects,
            None => function_effects(self.db, self.program, function),
        }
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

    /// The defaults of a type's fields, against the fields' types, and the
    /// handlers of its `on` clauses that are closures, against the member
    /// of their kind's form they fit (§11.4). The types themselves are the
    /// declaration's, which reports their errors.
    fn type_defaults(&mut self, item: ItemId<'db>) {
        let Some(decl) = &self.body.type_decl else {
            return;
        };
        let fields: Vec<_> = decl
            .fields
            .iter()
            .map(|f| (f.name, self.lower_type(f.ty), f.default))
            .collect();
        let alias = decl.alias.map(|a| self.lower_type(a));
        self.lower.errors.clear();
        for &(_, ty, default) in &fields {
            if let Some(default) = default {
                self.check(default, ty);
            }
        }
        // The conditions see the value as `this` and the fields by name
        // (§3.10).
        if let Some(this) = decl.this {
            let db = self.db;
            let own = match alias {
                Some(target) => target,
                None => {
                    let identity = type_identity(db, self.program, item);
                    let names = type_header(db, self.program, item).params.clone();
                    let params = (0..names.len())
                        .map(|i| Ty::new(db, TyKind::Param(Some(identity), i as u32, names[i])))
                        .collect();
                    Ty::new(db, TyKind::Named(identity, params))
                }
            };
            self.bindings[this.index()] = Some(own);
            for &(name, binding) in &decl.field_bindings {
                let ty = fields.iter().find(|(n, ..)| *n == name).map(|(_, t, _)| *t);
                self.bindings[binding.index()] = ty;
            }
            let bool_ty = self.bool_ty;
            for condition in &decl.conditions {
                self.check(condition.value, bool_ty);
            }
        }
        for clause in &decl.handlers {
            let Expr::Closure { params, .. } = self.body.expr(clause.handler) else {
                continue;
            };
            let written: Vec<Option<Ty<'db>>> = params.iter().map(|p| self.written(p.ty)).collect();
            let expectation =
                crate::handler::closure_expectation(self.db, self.program, item, clause, &written);
            match expectation {
                Some(Some(expected)) => {
                    self.check(clause.handler, expected);
                }
                // `type_handlers` reports a closure that fits no member,
                // and inference one whose parameters' types it cannot
                // infer.
                Some(None) => {
                    self.synth(clause.handler);
                }
                // `type_handlers` reports a clause without a form.
                None => {}
            }
        }
    }

    // Expressions.

    fn synth(&mut self, id: ExprId) -> Ty<'db> {
        self.infer(id, None)
    }

    /// Checks an expression against an expected type and returns its own.
    fn check(&mut self, id: ExprId, expected: Ty<'db>) -> Ty<'db> {
        let mut ty = self.infer(id, Some(expected));
        if self.sendable(id, ty, expected) {
            ty = self.reference(id, ty);
            self.exprs[id.index()] = Some(ty);
        }
        self.expect(Site::Expr(id), ty, expected);
        ty
    }

    fn infer(&mut self, id: ExprId, expected: Option<Ty<'db>>) -> Ty<'db> {
        if let Some(ty) = self.typed.remove(&id) {
            return ty;
        }
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
            Expr::Literal(literal) => {
                // A literal with its sign, or one `negate` takes (§6.2.1).
                let signed = self.body.is_negative(id);
                let outer = self.negative;
                self.negative = outer != signed;
                let ty = self.literal(id, literal, expected);
                self.negative = outer;
                ty
            }
            Expr::Embed => self.embed(id, expected),
            Expr::Str(parts) => {
                // A string without interpolation is a literal (§3.10.1).
                if let [crag_hir::StrPart::Text(text)] = parts.as_slice() {
                    let literal = Literal::Str(text.clone());
                    if let Some(refined) = self.refined_literal(id, &literal, expected) {
                        return refined;
                    }
                }
                for part in parts {
                    if let crag_hir::StrPart::Expr(e) = part {
                        let ty = self.synth(*e);
                        self.interpolated(*e, ty);
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
                let receiver_ty = self.synth(*receiver);
                if *optional {
                    return self.optional(id, receiver_ty, |this, present| {
                        this.method_call(
                            id,
                            *receiver,
                            present,
                            *name,
                            functions,
                            args,
                            fields.as_deref(),
                            None,
                        )
                    });
                }
                self.method_call(
                    id,
                    *receiver,
                    receiver_ty,
                    *name,
                    functions,
                    args,
                    fields.as_deref(),
                    expected,
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
                let receiver_ty = self.synth(*receiver);
                if *optional {
                    return self.optional(id, receiver_ty, |this, present| {
                        this.field(id, *receiver, present, *name, functions, None)
                    });
                }
                self.field(id, *receiver, receiver_ty, *name, functions, expected)
            }
            Expr::Index { base, args } => self.index(id, *base, args),
            Expr::TypeArgs { base, args } => match body.expr(*base) {
                Expr::Name {
                    name,
                    local: None,
                    item: Some(Resolution::Type(item)),
                } => {
                    let args = self.type_args(id, Some(*item), args);
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
                    let args = self.type_args(id, None, args);
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
            Expr::Grid(rows) => self.grid(id, rows, expected),
            Expr::Block { stmts, tail } => {
                let mut leaves = false;
                let mut handled = Vec::new();
                for stmt in stmts {
                    // A trap handler gives the block its value (§8.3.1).
                    if let Stmt::On { ty, handler } = stmt
                        && let Some(trap) = self.trap_type(*ty)
                    {
                        handled.push((*handler, self.trap_handler(*handler, trap)));
                        continue;
                    }
                    leaves |= self.stmt(stmt).is_never(db);
                }
                let ty = match tail {
                    Some(tail) => self.infer(*tail, expected),
                    None => Ty::unit(db),
                };
                let ty = if leaves { Ty::never(db) } else { ty };
                let mut whole = ty;
                for (handler, given) in handled {
                    match expected.or(Some(ty).filter(|t| !t.is_never(db))) {
                        Some(wanted) => self.expect(Site::Expr(handler), given, wanted),
                        None => whole = self.join(whole, given),
                    }
                }
                whole
            }
            // A closure literal becomes an `Expr` where its context asks
            // for one, checked against the function type (§18.6).
            Expr::Closure { params, body: root } => {
                let sent = self.sent_as(expected, Some(params.len()));
                let context = sent.or(expected);
                let ty = self.closure(params, *root, context);
                let ty = self.pure_if_effectless(id, ty, context);
                match sent {
                    // Reported as for a plain closure: the function type
                    // must fit.
                    Some(f) if !self.fits(ty, f) => {
                        self.expect(Site::Expr(id), ty, f);
                        self.builtin_of(Builtin::Expr, vec![f])
                    }
                    Some(_) => {
                        let errors = crate::transport::literal_errors(
                            db,
                            self.program,
                            self.body,
                            &self.bindings,
                            id,
                        );
                        self.lower.errors.extend(errors);
                        self.sent.push(id);
                        self.builtin_of(Builtin::Expr, vec![ty])
                    }
                    None => ty,
                }
            }
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
            // A transaction: its value, an error aborting it, and a
            // `return` ends it with its value (§9.5.1). One that touches
            // a `dur` commits to the store, which can fail, so its result
            // includes `StoreError` (§21.7).
            Expr::Atomic(inner) => {
                let ty = self.frame(expected, *inner, false);
                if self.touches_dur(*inner)
                    && prelude_item(db, self.program, "StoreError").is_some()
                {
                    let error = prelude_type(db, self.program, "StoreError");
                    self.join(ty, error)
                } else {
                    ty
                }
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

/// Whether a type is one of the sources of `std.stream`, which `for`
/// iterates until the stream ends (§10.5).
pub fn is_source(db: &dyn Db, item: ItemId<'_>) -> bool {
    item.module(db).path(db) == "std.stream"
        && matches!(
            item.name(db).text(db).as_str(),
            "Source" | "Finite" | "Infinite"
        )
}

/// Whether interpolation writes values of a type as they are: a `Str` or
/// a `CodePoint`, or a conditioned alias of one (§19.11).
pub fn is_text<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    matches!(
        crate::relate::unrefined(db, program, ty).as_builtin(db),
        Some((Builtin::Str | Builtin::CodePoint, _))
    )
}
