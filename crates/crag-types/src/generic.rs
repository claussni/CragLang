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

//! Generic functions and forms (Implementation Plan §11.5.3).
//!
//! A generic function is checked once, its type parameters opaque: a
//! parameter bounded by a named type fits that type and has its fields,
//! and one bounded by a form can be passed to the form's functions, its
//! slots. The forms of a function's bounds, those a form requires in its
//! `where` clause or stands for included, give the function its slots in
//! a fixed order.
//!
//! A call infers the type arguments from the arguments and the expected
//! type, and instantiates the function: each type argument must fit its
//! bound, and for every slot a function visible where the call is written
//! must accept the slot's parameters and give its result. The functions
//! found are the call's slot fillings; in a generic caller a slot may be
//! filled by one of the caller's own.

use crag_db::Db;
use crag_hir::{
    ItemId, ItemKind, ModuleId, Name, Owner, Program, Requirement, Resolution, TypeArg, TypeRef,
    TypeRefId, TypeTarget, hir_body, module_scope,
};

use crate::def::{SigParam, TypeLowerer, own_type_params, signature, type_header};
use crate::group::result_type;
use crate::relate::{is_subtype, join, normalize, parent, subst};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Ty, TyKind};

/// A form applied to types: what a requirement asks of them.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct FormBound<'db> {
    pub form: ItemId<'db>,
    pub args: Vec<Ty<'db>>,
}

impl<'db> FormBound<'db> {
    pub fn display(&self, db: &'db dyn Db) -> String {
        let args: Vec<String> = self.args.iter().map(|t| t.display(db)).collect();
        format!("{}[{}]", self.form.name(db).text(db), args.join(", "))
    }

    fn subst(
        &self,
        db: &'db dyn Db,
        program: Program,
        owner: ItemId<'db>,
        args: &[Ty<'db>],
    ) -> Self {
        FormBound {
            form: self.form,
            args: self
                .args
                .iter()
                .map(|&t| subst(db, program, t, owner, args))
                .collect(),
        }
    }
}

/// What the type parameters of a generic function must fit (§4.2–4.4).
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Bounds<'db> {
    /// The named type a type parameter must fit, by its index.
    pub types: Vec<(u32, Ty<'db>)>,
    /// The forms, with those they require or stand for, each once.
    pub forms: Vec<FormBound<'db>>,
    /// Unions of forms, of which at least one must fit (§4.7). They give
    /// no slots.
    pub any_of: Vec<Vec<FormBound<'db>>>,
    pub errors: Vec<TypeError<'db>>,
}

/// A form's requirements, in its own type parameters.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct FormDef<'db> {
    /// The forms it requires in its `where` clause and bounds, or the one
    /// it stands for.
    pub requires: Vec<FormBound<'db>>,
    /// The union of forms it stands for, or required unions.
    pub any_of: Vec<Vec<FormBound<'db>>>,
    /// Its functions.
    pub slots: Vec<ItemId<'db>>,
    pub errors: Vec<TypeError<'db>>,
}

/// One function a generic function's bounds require: the form's function
/// with the bound's type arguments.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Slot<'db> {
    /// The index of its form in `Bounds::forms`.
    pub bound: u32,
    /// The form's function.
    pub function: ItemId<'db>,
    pub params: Vec<SigParam<'db>>,
    pub result: Ty<'db>,
}

/// A generic function with its type arguments and slot fillings, as a
/// call uses it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct Instance<'db> {
    pub function: ItemId<'db>,
    pub args: Vec<Ty<'db>>,
    /// One per slot of the function, in the order of `slots`.
    pub fillings: Vec<Filling<'db>>,
}

/// The function that fills a slot.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Filling<'db> {
    /// A declared function, generic or not.
    Function(Instance<'db>),
    /// A slot of the generic function the call is written in, by index.
    Slot(u32),
}

/// Why type arguments do not fit a generic function's bounds.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum FitError<'db> {
    /// A type argument does not fit its named bound.
    Bound {
        param: Name<'db>,
        arg: Ty<'db>,
        bound: Ty<'db>,
    },
    /// No visible function meets a form's function.
    Missing {
        bound: FormBound<'db>,
        slot: Name<'db>,
        wanted: Ty<'db>,
    },
    /// Several do equally well.
    Ambiguous {
        bound: FormBound<'db>,
        slot: Name<'db>,
        wanted: Ty<'db>,
        candidates: Vec<ItemId<'db>>,
    },
    /// No form of a union fits.
    NoneOf { forms: Vec<FormBound<'db>> },
}

impl<'db> FitError<'db> {
    pub fn message(&self, db: &'db dyn Db) -> String {
        match self {
            FitError::Bound { param, arg, bound } => format!(
                "{} does not fit the bound {} of `{}`",
                arg.display(db),
                bound.display(db),
                param.text(db)
            ),
            FitError::Missing {
                bound,
                slot,
                wanted,
            } => format!(
                "{} does not hold: no visible function `{}` has the type {}",
                bound.display(db),
                slot.text(db),
                wanted.display(db)
            ),
            FitError::Ambiguous {
                bound,
                slot,
                wanted,
                ..
            } => format!(
                "{} is ambiguous: several functions `{}` have the type {}",
                bound.display(db),
                slot.text(db),
                wanted.display(db)
            ),
            FitError::NoneOf { forms } => {
                let forms: Vec<String> = forms.iter().map(|f| f.display(db)).collect();
                format!("none of {} holds", forms.join(" | "))
            }
        }
    }
}

/// A requirement as lowered: a named bound, a form, or a union of forms.
enum Req<'db> {
    Type(u32, Ty<'db>),
    Form(FormBound<'db>),
    AnyOf(Vec<FormBound<'db>>),
}

/// The form a written type names, with its written arguments.
fn form_ref<'db>(
    db: &'db dyn Db,
    lower: &TypeLowerer<'_, 'db>,
    ty: TypeRefId,
) -> Option<(ItemId<'db>, Vec<TypeArg>)> {
    match lower.body.type_ref(ty) {
        TypeRef::Named {
            target: TypeTarget::Item(item),
            args,
            ..
        } if *item.kind(db) == ItemKind::Form => Some((*item, args.clone())),
        _ => None,
    }
}

/// A written form applied to its arguments; a bound in brackets gives the
/// form its type parameter as the first argument.
fn form_bound<'db>(
    lower: &mut TypeLowerer<'_, 'db>,
    ty: TypeRefId,
    param: Option<Ty<'db>>,
) -> Option<FormBound<'db>> {
    let db = lower.db;
    let (form, written) = form_ref(db, lower, ty)?;
    let arity = type_header(db, lower.program, form).params.len();
    let mut args: Vec<Ty<'db>> = param.into_iter().collect();
    let given = args.len();
    for arg in &written {
        match arg {
            TypeArg::Type(t) => args.push(lower.lower(*t)),
            _ => {
                lower.error(Site::Type(ty), ErrorKind::TypeArgKind);
                return None;
            }
        }
    }
    if args.len() != arity {
        let kind = ErrorKind::TypeArgCount {
            expected: arity.saturating_sub(given),
            found: written.len(),
        };
        lower.error(Site::Type(ty), kind);
        return None;
    }
    Some(FormBound { form, args })
}

/// Lowers a requirement, reporting what is wrong with it.
fn requirement<'db>(lower: &mut TypeLowerer<'_, 'db>, req: &Requirement) -> Option<Req<'db>> {
    let db = lower.db;
    let param = req.param.map(|i| {
        let name = lower.body.type_params[i as usize];
        Ty::new(db, TyKind::Param(lower.owner, i, name))
    });
    if let TypeRef::Union(members) = lower.body.type_ref(req.ty) {
        let members = members.clone();
        let forms = members
            .iter()
            .filter(|&&m| form_ref(db, lower, m).is_some())
            .count();
        if forms > 0 {
            if forms < members.len() {
                lower.error(Site::Type(req.ty), ErrorKind::MixedBound);
                return None;
            }
            let bounds: Option<Vec<_>> = members
                .iter()
                .map(|&m| form_bound(lower, m, param))
                .collect();
            return bounds.map(Req::AnyOf);
        }
    }
    if form_ref(db, lower, req.ty).is_some() {
        return form_bound(lower, req.ty, param).map(Req::Form);
    }
    let ty = lower.lower(req.ty);
    match req.param {
        Some(i) => Some(Req::Type(i, ty)),
        None => {
            if !ty.is_error(db) {
                lower.error(Site::Type(req.ty), ErrorKind::NotAForm { ty });
            }
            None
        }
    }
}

/// A form's requirements and functions.
#[crag_db::tracked(returns(ref))]
pub fn form_def<'db>(db: &'db dyn Db, program: Program, form: ItemId<'db>) -> FormDef<'db> {
    let body = hir_body(db, program, Owner::Item(form));
    let mut lower = TypeLowerer::new(db, program, body, Some(form));
    let mut def = FormDef {
        slots: crag_hir::form_slots(db, form),
        ..FormDef::default()
    };
    let alias = body
        .form
        .as_ref()
        .and_then(|f| f.alias)
        .map(|ty| Requirement { param: None, ty });
    for req in body.requirements.iter().chain(&alias) {
        match requirement(&mut lower, req) {
            Some(Req::Form(bound)) => def.requires.push(bound),
            Some(Req::AnyOf(bounds)) => def.any_of.push(bounds),
            Some(Req::Type(..)) => {
                let kind = ErrorKind::Unsupported("named types as bounds of forms");
                lower.error(Site::Type(req.ty), kind);
            }
            None => {}
        }
    }
    for slot in body.form.iter().flat_map(|f| &f.slots) {
        for &(_, ty) in &slot.params {
            lower.lower(ty);
        }
        lower.lower(slot.result);
        if slot.generic {
            let kind = ErrorKind::Unsupported("generic functions in forms");
            lower.error(Site::Type(slot.result), kind);
        }
    }
    def.errors = lower.errors;
    def
}

/// Adds a form bound and what its form requires, each once.
fn expand<'db>(
    db: &'db dyn Db,
    program: Program,
    bound: FormBound<'db>,
    forms: &mut Vec<FormBound<'db>>,
    any_of: &mut Vec<Vec<FormBound<'db>>>,
) {
    if forms.contains(&bound) {
        return;
    }
    let def = form_def(db, program, bound.form);
    forms.push(bound.clone());
    for required in &def.requires {
        let required = required.subst(db, program, bound.form, &bound.args);
        expand(db, program, required, forms, any_of);
    }
    for union in &def.any_of {
        let union = union
            .iter()
            .map(|b| b.subst(db, program, bound.form, &bound.args))
            .collect();
        if !any_of.contains(&union) {
            any_of.push(union);
        }
    }
}

/// The bounds of a generic function's type parameters, those of its form
/// typed parameters included (§4.3).
#[crag_db::tracked(returns(ref))]
pub fn bounds<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Bounds<'db> {
    let body = hir_body(db, program, Owner::Item(item));
    let mut lower = TypeLowerer::new(db, program, body, Some(item));
    let mut bounds = Bounds::default();
    if *item.kind(db) == ItemKind::Type {
        if let Some(req) = body.requirements.first() {
            let kind = ErrorKind::Unsupported("bounds on type parameters of types");
            lower.error(Site::Type(req.ty), kind);
        }
        bounds.errors = lower.errors;
        return bounds;
    }
    let own = own_type_params(db, item) as u32;
    let mut forms = Vec::new();
    for req in &body.requirements {
        // Those of local functions, which cannot be generic yet.
        if req.param.is_some_and(|p| p >= own) {
            continue;
        }
        match requirement(&mut lower, req) {
            Some(Req::Type(i, ty)) => bounds.types.push((i, ty)),
            Some(Req::Form(bound)) => forms.push(bound),
            Some(Req::AnyOf(union)) => bounds.any_of.push(union),
            None => {}
        }
    }
    for ty in lower.implicit.clone() {
        let param = lower.lower(ty);
        if let Some(bound) = form_bound(&mut lower, ty, Some(param)) {
            forms.push(bound);
        }
    }
    for bound in forms {
        expand(db, program, bound, &mut bounds.forms, &mut bounds.any_of);
    }
    bounds.errors = lower.errors;
    bounds
}

/// The named type a type parameter is bounded by (§4.2). Subtyping asks
/// for it, so it lowers nothing else.
#[crag_db::tracked(returns(copy), cycle_result = param_bound_cycle)]
pub fn param_bound<'db>(
    db: &'db dyn Db,
    program: Program,
    item: ItemId<'db>,
    index: u32,
) -> Option<Ty<'db>> {
    let body = hir_body(db, program, Owner::Item(item));
    let mut lower = TypeLowerer::new(db, program, body, Some(item));
    let req = body.requirements.iter().find(|r| {
        r.param == Some(index)
            && form_ref(db, &lower, r.ty).is_none()
            && !matches!(body.type_ref(r.ty), TypeRef::Union(m)
                if m.iter().any(|&m| form_ref(db, &lower, m).is_some()))
    })?;
    Some(lower.lower(req.ty))
}

fn param_bound_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _item: ItemId<'db>,
    _index: u32,
) -> Option<Ty<'db>> {
    None
}

/// The slots of a generic function: for each form of its bounds, each of
/// the form's functions with the bound's type arguments.
#[crag_db::tracked(returns(ref))]
pub fn slots<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Vec<Slot<'db>> {
    let mut slots = Vec::new();
    for (i, bound) in bounds(db, program, item).forms.iter().enumerate() {
        for &function in &form_def(db, program, bound.form).slots {
            let sig = signature(db, program, function);
            let at = |t: Ty<'db>| subst(db, program, t, bound.form, &bound.args);
            slots.push(Slot {
                bound: i as u32,
                function,
                params: sig
                    .params
                    .iter()
                    .map(|p| SigParam {
                        name: p.name,
                        ty: at(p.ty),
                        default: false,
                    })
                    .collect(),
                result: sig.result.map_or_else(|| Ty::error(db), at),
            });
        }
    }
    slots
}

/// Where a call is written: the module whose functions fill slots, and the
/// generic function, if any, whose own slots may.
#[derive(Clone, Copy, Debug)]
pub struct CallSite<'db> {
    pub module: ModuleId,
    pub caller: Option<ItemId<'db>>,
}

/// How deep generic functions may fill each other's slots.
const MAX_DEPTH: u32 = 8;

/// The instance of a generic function with these type arguments, if they
/// fit its bounds where the call is written.
pub fn instantiate<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
    args: &[Ty<'db>],
    at: CallSite<'db>,
) -> Result<Instance<'db>, FitError<'db>> {
    instantiate_at(db, program, function, args, at, 0)
}

fn instantiate_at<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
    args: &[Ty<'db>],
    at: CallSite<'db>,
    depth: u32,
) -> Result<Instance<'db>, FitError<'db>> {
    let b = bounds(db, program, function);
    for &(i, bound) in &b.types {
        let bound = subst(db, program, bound, function, args);
        let arg = args
            .get(i as usize)
            .copied()
            .unwrap_or_else(|| Ty::error(db));
        if !is_subtype(db, program, arg, bound) {
            let param = type_param_names(db, program, function)[i as usize];
            return Err(FitError::Bound { param, arg, bound });
        }
    }
    let mut fillings = Vec::new();
    for bound in &b.forms {
        let bound = bound.subst(db, program, function, args);
        fillings.extend(fit_slots(db, program, &bound, at, depth)?);
    }
    for union in &b.any_of {
        let union: Vec<FormBound<'db>> = union
            .iter()
            .map(|f| f.subst(db, program, function, args))
            .collect();
        if !union
            .iter()
            .any(|f| fits(db, program, f, at, depth).is_ok())
        {
            return Err(FitError::NoneOf { forms: union });
        }
    }
    Ok(Instance {
        function,
        args: args.to_vec(),
        fillings,
    })
}

/// Whether a form bound holds where the call is written, with what it
/// requires.
fn fits<'db>(
    db: &'db dyn Db,
    program: Program,
    bound: &FormBound<'db>,
    at: CallSite<'db>,
    depth: u32,
) -> Result<(), FitError<'db>> {
    let mut forms = Vec::new();
    let mut any_of = Vec::new();
    expand(db, program, bound.clone(), &mut forms, &mut any_of);
    for form in &forms {
        fit_slots(db, program, form, at, depth)?;
    }
    for union in &any_of {
        if !union
            .iter()
            .any(|f| fits(db, program, f, at, depth).is_ok())
        {
            return Err(FitError::NoneOf {
                forms: union.clone(),
            });
        }
    }
    Ok(())
}

/// The fillings of a form bound's own functions.
fn fit_slots<'db>(
    db: &'db dyn Db,
    program: Program,
    bound: &FormBound<'db>,
    at: CallSite<'db>,
    depth: u32,
) -> Result<Vec<Filling<'db>>, FitError<'db>> {
    let mut fillings = Vec::new();
    for &slot in &form_def(db, program, bound.form).slots {
        let sig = signature(db, program, slot);
        let at_bound = |t: Ty<'db>| subst(db, program, t, bound.form, &bound.args);
        let params: Vec<Ty<'db>> = sig.params.iter().map(|p| at_bound(p.ty)).collect();
        let result = sig.result.map_or_else(|| Ty::error(db), at_bound);
        let name = *slot.name(db);
        let wanted = Ty::new(
            db,
            TyKind::Fn {
                params: params.clone(),
                result,
            },
        );
        match fill(db, program, name, &params, result, at, depth) {
            Ok(filling) => fillings.push(filling),
            Err(candidates) if candidates.is_empty() => {
                return Err(FitError::Missing {
                    bound: bound.clone(),
                    slot: name,
                    wanted,
                });
            }
            Err(candidates) => {
                return Err(FitError::Ambiguous {
                    bound: bound.clone(),
                    slot: name,
                    wanted,
                    candidates,
                });
            }
        }
    }
    Ok(fillings)
}

/// The function that fills a slot with these parameter and result types:
/// a visible function that accepts the parameters and gives the result,
/// or a slot of the caller. A function that is not generic, and a slot,
/// beat a generic function. Without one, the functions that tie.
fn fill<'db>(
    db: &'db dyn Db,
    program: Program,
    name: Name<'db>,
    params: &[Ty<'db>],
    result: Ty<'db>,
    at: CallSite<'db>,
    depth: u32,
) -> Result<Filling<'db>, Vec<ItemId<'db>>> {
    let fits = |s: Ty<'db>, t: Ty<'db>| is_subtype(db, program, s, t);
    let mut plain: Vec<(Filling<'db>, ItemId<'db>)> = Vec::new();
    let mut generic: Vec<(Filling<'db>, ItemId<'db>)> = Vec::new();
    let functions = match module_scope(db, program, at.module).resolve(name) {
        Some(Resolution::Value { functions, .. }) => functions.clone(),
        _ => Vec::new(),
    };
    for f in functions {
        if *f.kind(db) != ItemKind::Function {
            continue;
        }
        let sig = signature(db, program, f);
        if sig.params.len() != params.len() {
            continue;
        }
        let Some(given) = result_type(db, program, f) else {
            continue;
        };
        if sig.type_params == 0 {
            if params.iter().zip(&sig.params).all(|(&p, q)| fits(p, q.ty)) && fits(given, result) {
                let instance = Instance {
                    function: f,
                    args: Vec::new(),
                    fillings: Vec::new(),
                };
                plain.push((Filling::Function(instance), f));
            }
            continue;
        }
        if depth >= MAX_DEPTH {
            continue;
        }
        let mut args = vec![None; sig.type_params];
        for (&p, q) in params.iter().zip(&sig.params) {
            bind(db, program, f, q.ty, p, &mut args);
        }
        let Some(args) = args.into_iter().collect::<Option<Vec<_>>>() else {
            continue;
        };
        let at_args = |t: Ty<'db>| subst(db, program, t, f, &args);
        let accepts = params
            .iter()
            .zip(&sig.params)
            .all(|(&p, q)| fits(p, at_args(q.ty)));
        if accepts
            && fits(at_args(given), result)
            && let Ok(instance) = instantiate_at(db, program, f, &args, at, depth + 1)
        {
            generic.push((Filling::Function(instance), f));
        }
    }
    if let Some(caller) = at.caller {
        for (k, slot) in slots(db, program, caller).iter().enumerate() {
            if *slot.function.name(db) == name
                && slot.params.len() == params.len()
                && params.iter().zip(&slot.params).all(|(&p, q)| fits(p, q.ty))
                && fits(slot.result, result)
            {
                plain.push((Filling::Slot(k as u32), slot.function));
            }
        }
    }
    let best = if plain.is_empty() { generic } else { plain };
    match best.len() {
        1 => Ok(best.into_iter().next().expect("one").0),
        _ => Err(best.into_iter().map(|(_, f)| f).collect()),
    }
}

/// Whether `ty` names a type parameter of `owner` that `which` picks by
/// index.
pub(crate) fn mentions<'db>(
    db: &'db dyn Db,
    ty: Ty<'db>,
    owner: ItemId<'db>,
    which: &dyn Fn(u32) -> bool,
) -> bool {
    let go = |t: &Ty<'db>| mentions(db, *t, owner, which);
    match ty.kind(db) {
        TyKind::Param(Some(o), index, _) => *o == owner && which(*index),
        TyKind::Error | TyKind::Param(None, ..) => false,
        TyKind::Builtin(_, args) | TyKind::Named(_, args) => args.iter().any(go),
        TyKind::Record { fields, .. } => fields.iter().any(|(_, t)| go(t)),
        TyKind::Fn { params, result } => params.iter().any(go) || go(result),
        TyKind::Union(members) => members.iter().any(go),
    }
}

/// Whether `ty` names any type parameter.
pub(crate) fn mentions_any<'db>(db: &'db dyn Db, ty: Ty<'db>) -> bool {
    match ty.kind(db) {
        TyKind::Param(..) => true,
        TyKind::Error => false,
        TyKind::Builtin(_, args) | TyKind::Named(_, args) => {
            args.iter().any(|&t| mentions_any(db, t))
        }
        TyKind::Record { fields, .. } => fields.iter().any(|&(_, t)| mentions_any(db, t)),
        TyKind::Fn { params, result } => {
            params.iter().any(|&t| mentions_any(db, t)) || mentions_any(db, *result)
        }
        TyKind::Union(members) => members.iter().any(|&t| mentions_any(db, t)),
    }
}

/// Infers type arguments of `owner` by matching a type written with its
/// type parameters against a type found: each parameter takes what it
/// meets, or the union of what it meets.
pub(crate) fn bind<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: ItemId<'db>,
    pattern: Ty<'db>,
    found: Ty<'db>,
    args: &mut [Option<Ty<'db>>],
) {
    if found.is_error(db) || !mentions(db, pattern, owner, &|_| true) {
        return;
    }
    let go =
        |p: Ty<'db>, f: Ty<'db>, args: &mut [Option<Ty<'db>>]| bind(db, program, owner, p, f, args);
    match (pattern.kind(db), found.kind(db)) {
        (TyKind::Param(Some(o), i, _), _) if *o == owner => {
            let Some(slot) = args.get_mut(*i as usize) else {
                return;
            };
            *slot = Some(match *slot {
                None => found,
                Some(prev) if is_subtype(db, program, found, prev) => prev,
                Some(prev) if is_subtype(db, program, prev, found) => found,
                Some(prev) => join(db, program, prev, found),
            });
        }
        (TyKind::Builtin(a, ps), TyKind::Builtin(b, fs)) if a == b && ps.len() == fs.len() => {
            for (&p, &f) in ps.iter().zip(fs) {
                go(p, f, args);
            }
        }
        (TyKind::Named(a, ps), TyKind::Named(b, fs)) => {
            if a == b && ps.len() == fs.len() {
                for (&p, &f) in ps.iter().zip(fs) {
                    go(p, f, args);
                }
            } else if let Some(p) = parent(db, program, found) {
                go(pattern, p, args);
            }
        }
        (TyKind::Record { fields: ps, .. }, TyKind::Record { fields: fs, .. }) => {
            for (name, p) in ps {
                if let Some((_, f)) = fs.iter().find(|(n, _)| n == name) {
                    go(*p, *f, args);
                }
            }
        }
        (
            TyKind::Fn {
                params: pp,
                result: pr,
            },
            TyKind::Fn {
                params: fp,
                result: fr,
            },
        ) if pp.len() == fp.len() => {
            for (&p, &f) in pp.iter().zip(fp) {
                go(p, f, args);
            }
            go(*pr, *fr, args);
        }
        // `T | Empty` against `Int | Empty`: the parameter takes what the
        // other members do not cover.
        (TyKind::Union(members), _) => {
            let (open, closed): (Vec<Ty<'db>>, Vec<Ty<'db>>) = members
                .iter()
                .partition(|&&m| mentions(db, m, owner, &|_| true));
            if let [open] = open.as_slice() {
                let rest: Vec<Ty<'db>> = found
                    .members(db)
                    .into_iter()
                    .filter(|&m| !closed.iter().any(|&c| is_subtype(db, program, m, c)))
                    .collect();
                if !rest.is_empty() {
                    go(*open, normalize(db, program, rest).0, args);
                }
            }
        }
        _ => {}
    }
}

/// A generic function's type parameters by name: the written ones, then
/// one per form typed parameter, named by its form.
pub fn type_param_names<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
) -> Vec<Name<'db>> {
    let body = hir_body(db, program, Owner::Item(function));
    let own = own_type_params(db, function);
    let mut names: Vec<Name<'db>> = body.type_params.iter().take(own).copied().collect();
    for ty in crate::def::implicit_params(db, body) {
        if let TypeRef::Named { name, .. } = body.type_ref(ty) {
            names.push(*name);
        }
    }
    names
}
