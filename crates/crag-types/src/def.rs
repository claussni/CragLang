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

//! Declarations as types: type declarations, function signatures, success
//! types and the types of module-level values, and the lowering of written
//! types.

use crag_db::Db;
use crag_hir::{
    Body, ItemId, ItemKind, Name, Owner, PRELUDE, Program, TypeArg, TypeField, TypeRef, TypeRefId,
    TypeTarget, hir_body, item_tree, type_identity,
};

use crate::infer::infer;
use crate::relate::{self, subst};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// What a reference to a type needs to know of its declaration.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct TypeHeader<'db> {
    pub params: Vec<Name<'db>>,
    pub kind: HeaderKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum HeaderKind {
    /// A prelude declaration standing for a compiler- or runtime-owned
    /// type (§19.1).
    Builtin(Builtin),
    Alias,
    /// A record or a tag.
    Nominal,
    Form,
}

/// A type declaration of the prelude stands for a builtin when it has the
/// builtin's name and number of type parameters, and neither fields nor an
/// alias target.
#[crag_db::tracked(returns(ref))]
pub fn type_header<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> TypeHeader<'db> {
    let body = hir_body(db, program, Owner::Item(item));
    let params = body.type_params.clone();
    if *item.kind(db) == ItemKind::Form {
        return TypeHeader {
            params,
            kind: HeaderKind::Form,
        };
    }
    let decl = body.type_decl.clone().unwrap_or_default();
    let builtin = Builtin::from_name(item.name(db).text(db))
        .filter(|&(_, arity)| arity == params.len())
        .filter(|_| item.module(db).path(db) == PRELUDE && !decl.record && decl.alias.is_none());
    let kind = match (builtin, decl.alias) {
        (Some((builtin, _)), _) => HeaderKind::Builtin(builtin),
        (None, Some(_)) => HeaderKind::Alias,
        (None, None) => HeaderKind::Nominal,
    };
    TypeHeader { params, kind }
}

/// An alias's target, with the alias's parameters as `Param`s; none when
/// the alias refers to itself.
#[crag_db::tracked(returns(copy), cycle_result = alias_cycle)]
pub fn alias_target<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Option<Ty<'db>> {
    let body = hir_body(db, program, Owner::Item(item));
    let alias = body.type_decl.as_ref()?.alias?;
    let mut lower = TypeLowerer::new(db, program, body, Some(item));
    Some(lower.lower(alias))
}

fn alias_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _item: ItemId<'db>,
) -> Option<Ty<'db>> {
    None
}

/// The parent a type spreads (§3.8). Subtyping asks for it while the
/// declarations of recursive types are lowered, so it lowers nothing else.
/// None also for a parent that refers back to the type.
#[crag_db::tracked(returns(copy), cycle_result = parent_cycle)]
pub fn type_parent<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Option<Ty<'db>> {
    let body = hir_body(db, program, Owner::Item(item));
    let parent = body.type_decl.as_ref()?.parent?;
    let mut lower = TypeLowerer::new(db, program, body, Some(item));
    Some(lower.lower(parent))
}

fn parent_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _item: ItemId<'db>,
) -> Option<Ty<'db>> {
    None
}

/// A type declaration with its written types lowered.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct TypeDef<'db> {
    pub kind: TypeDefKind<'db>,
    pub distinct: bool,
    pub opaque: bool,
    pub errors: Vec<TypeError<'db>>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum TypeDefKind<'db> {
    Builtin(Builtin),
    Alias(Ty<'db>),
    Tag,
    Record {
        parent: Option<Ty<'db>>,
        fields: Vec<FieldDef<'db>>,
    },
    Form,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct FieldDef<'db> {
    pub name: Name<'db>,
    pub ty: Ty<'db>,
    pub default: bool,
}

/// A declaration that only a cycle through its own fields can reach, such
/// as `type T(f: T | (x: Int, ..))`, is a tag while that cycle is resolved.
#[crag_db::tracked(returns(ref), cycle_result = type_def_cycle)]
pub fn type_def<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> TypeDef<'db> {
    let body = hir_body(db, program, Owner::Item(item));
    let decl = body.type_decl.clone().unwrap_or_default();
    let mut lower = TypeLowerer::new(db, program, body, Some(item));
    let kind = match type_header(db, program, item).kind {
        HeaderKind::Builtin(builtin) => TypeDefKind::Builtin(builtin),
        HeaderKind::Form => TypeDefKind::Form,
        HeaderKind::Alias => match alias_target(db, program, item) {
            Some(target) => {
                // Lowered again for the errors; the target is the same.
                lower.lower(decl.alias.expect("an alias has a target"));
                TypeDefKind::Alias(target)
            }
            None => {
                let site = Site::Type(decl.alias.expect("an alias has a target"));
                lower.error(site, ErrorKind::AliasCycle);
                TypeDefKind::Alias(Ty::error(db))
            }
        },
        HeaderKind::Nominal if !decl.record => TypeDefKind::Tag,
        HeaderKind::Nominal => {
            let parent = decl.parent.map(|p| {
                let ty = lower.lower(p);
                if relate::fields_of(db, program, ty).is_none() && !ty.is_error(db) {
                    lower.error(
                        Site::Type(p),
                        ErrorKind::Unsupported("parents that are not records"),
                    );
                }
                ty
            });
            let mut fields: Vec<FieldDef<'db>> = Vec::new();
            for field in &decl.fields {
                let ty = lower.lower(field.ty);
                if fields.iter().any(|f| f.name == field.name) {
                    let kind = ErrorKind::DuplicateField { name: field.name };
                    lower.error(Site::Type(field.ty), kind);
                    continue;
                }
                fields.push(FieldDef {
                    name: field.name,
                    ty,
                    default: field.default.is_some(),
                });
            }
            TypeDefKind::Record { parent, fields }
        }
    };
    TypeDef {
        kind,
        distinct: decl.distinct,
        opaque: decl.opaque,
        errors: lower.errors,
    }
}

fn type_def_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _item: ItemId<'db>,
) -> TypeDef<'db> {
    TypeDef {
        kind: TypeDefKind::Tag,
        distinct: false,
        opaque: false,
        errors: Vec::new(),
    }
}

/// A function's written signature.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Signature<'db> {
    /// The number of its own type parameters; a generic function has some.
    pub type_params: usize,
    pub params: Vec<SigParam<'db>>,
    /// None when the success type is left to inference (§3.13.1).
    pub result: Option<Ty<'db>>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct SigParam<'db> {
    pub name: Option<Name<'db>>,
    pub ty: Ty<'db>,
    pub default: bool,
}

/// A function's written signature. A form's function has the form's type
/// parameters (§4.1).
#[crag_db::tracked(returns(ref))]
pub fn signature<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Signature<'db> {
    if *item.kind(db) == ItemKind::Slot {
        return slot_signature(db, program, item);
    }
    let body = hir_body(db, program, Owner::Item(item));
    let mut lower = TypeLowerer::new(db, program, body, Some(item));
    let params = body
        .params
        .iter()
        .map(|p| SigParam {
            name: body.binding(p.binding).name,
            ty: lower.lower(p.ty),
            default: p.default.is_some(),
        })
        .collect();
    let result = body
        .result
        .filter(|&r| *body.type_ref(r) != TypeRef::Infer)
        .map(|r| lower.lower(r));
    Signature {
        type_params: own_type_params(db, item) + lower.implicit.len(),
        params,
        result,
    }
}

fn slot_signature<'db>(db: &'db dyn Db, program: Program, slot: ItemId<'db>) -> Signature<'db> {
    let decl = crag_hir::slot_item(db, slot).and_then(|(form, index)| {
        let body = hir_body(db, program, Owner::Item(form));
        Some((form, body, body.form.as_ref()?.slots.get(index as usize)?))
    });
    let Some((form, body, decl)) = decl else {
        return Signature {
            type_params: 0,
            params: Vec::new(),
            result: None,
        };
    };
    let mut lower = TypeLowerer::new(db, program, body, Some(form));
    let params = decl
        .params
        .iter()
        .map(|&(name, ty)| SigParam {
            name,
            ty: lower.lower(ty),
            default: false,
        })
        .collect();
    Signature {
        type_params: 0,
        params,
        result: Some(lower.lower(decl.result)),
    }
}

/// The parameter types of a function body that name a form without type
/// arguments: each stands for a type parameter of its own (§4.3).
pub(crate) fn implicit_params<'db>(db: &'db dyn Db, body: &Body<'db>) -> Vec<TypeRefId> {
    body.params
        .iter()
        .map(|p| p.ty)
        .filter(|&ty| {
            matches!(body.type_ref(ty), TypeRef::Named {
                target: TypeTarget::Item(item),
                args,
                ..
            } if *item.kind(db) == ItemKind::Form && args.is_empty())
        })
        .collect()
}

/// A function's own type parameters, not those of its local functions.
pub(crate) fn own_type_params(db: &dyn Db, item: ItemId) -> usize {
    let tree = item_tree(db, *item.module(db));
    let Some(item) = tree.items.iter().find(|i| i.id == item) else {
        return 0;
    };
    crag_hir::type_param_count(&item.signature)
}

/// A function's success type: written, or inferred from its body. None
/// when it is inferred and depends on itself (§3.13.1).
#[crag_db::tracked(returns(copy), cycle_result = success_cycle)]
pub fn success_type<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Option<Ty<'db>> {
    if let Some(result) = signature(db, program, item).result {
        return Some(result);
    }
    // Inference runs here apart from `body_types`, so that `body_types` of
    // the function that started a cycle is never part of it.
    infer(db, program, Owner::Item(item)).result
}

fn success_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _item: ItemId<'db>,
) -> Option<Ty<'db>> {
    None
}

/// The type of a value a module-level `let` binds. None when it depends
/// on itself.
#[crag_db::tracked(returns(copy), cycle_result = value_cycle)]
pub fn value_type<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Option<Ty<'db>> {
    let tree = item_tree(db, *item.module(db));
    let decl = tree.items.iter().find(|i| i.id == item)?.decl;
    // The `let` is the owner through the first value it binds.
    let owner = tree
        .items
        .iter()
        .find(|i| i.decl == decl && *i.id.kind(db) == ItemKind::Value)?
        .id;
    let body = hir_body(db, program, Owner::Item(owner));
    let result = infer(db, program, Owner::Item(owner));
    let binding = body
        .bindings
        .iter()
        .position(|b| b.name == Some(*item.name(db)) && b.kind == crag_hir::BindingKind::Module)?;
    Some(result.bindings[binding].unwrap_or_else(|| Ty::error(db)))
}

fn value_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _item: ItemId<'db>,
) -> Option<Ty<'db>> {
    None
}

/// A type the compiler refers to by name, declared in the prelude (§19.1).
pub fn prelude_item<'db>(db: &'db dyn Db, program: Program, name: &str) -> Option<ItemId<'db>> {
    let index = crag_hir::module_index(db, program);
    let module = index.modules.get(PRELUDE)?;
    item_tree(db, *module)
        .items
        .iter()
        .find(|i| *i.id.kind(db) == ItemKind::Type && i.id.name(db).text(db) == name)
        .map(|i| i.id)
}

/// Lowers the written types of one body.
pub(crate) struct TypeLowerer<'a, 'db> {
    pub db: &'db dyn Db,
    pub program: Program,
    pub body: &'a Body<'db>,
    /// The function or type whose type parameters the body's are.
    pub owner: Option<ItemId<'db>>,
    pub types: Vec<Option<Ty<'db>>>,
    pub errors: Vec<TypeError<'db>>,
    /// The parameter types of a function that are forms, each standing
    /// for a type parameter after the written ones (§4.3).
    pub implicit: Vec<TypeRefId>,
    /// The number of written type parameters of the function.
    explicit: u32,
}

impl<'a, 'db> TypeLowerer<'a, 'db> {
    pub fn new(
        db: &'db dyn Db,
        program: Program,
        body: &'a Body<'db>,
        owner: Option<ItemId<'db>>,
    ) -> Self {
        let (implicit, explicit) = match owner {
            Some(item) if *item.kind(db) == ItemKind::Function => {
                (implicit_params(db, body), own_type_params(db, item) as u32)
            }
            _ => (Vec::new(), 0),
        };
        TypeLowerer {
            db,
            program,
            body,
            owner,
            types: vec![None; body.types.len()],
            errors: Vec::new(),
            implicit,
            explicit,
        }
    }

    pub fn error(&mut self, site: Site, kind: ErrorKind<'db>) {
        self.errors.push(TypeError { site, kind });
    }

    pub fn lower(&mut self, id: TypeRefId) -> Ty<'db> {
        let db = self.db;
        if let Some(k) = self.implicit.iter().position(|&t| t == id) {
            let TypeRef::Named { name, .. } = self.body.type_ref(id) else {
                unreachable!("an implicit parameter is named by its form");
            };
            let index = self.explicit + k as u32;
            let ty = Ty::new(db, TyKind::Param(self.owner, index, *name));
            self.types[id.index()] = Some(ty);
            return ty;
        }
        let ty = match self.body.type_ref(id) {
            TypeRef::Missing => Ty::error(db),
            TypeRef::Infer => {
                self.error(Site::Type(id), ErrorKind::CannotInfer);
                Ty::error(db)
            }
            TypeRef::Unit => Ty::unit(db),
            TypeRef::Named { name, target, args } => {
                let (name, target, args) = (*name, target.clone(), args.clone());
                self.named(id, name, target, &args)
            }
            TypeRef::Record { fields, open } => {
                let (fields, open) = (fields.clone(), *open);
                let mut lowered: Vec<(Name<'db>, Ty<'db>)> = Vec::new();
                let mut add = |this: &mut Self, name: Name<'db>, ty: Ty<'db>| {
                    if lowered.iter().any(|(n, _)| *n == name) {
                        this.error(Site::Type(id), ErrorKind::DuplicateField { name });
                    } else {
                        lowered.push((name, ty));
                    }
                };
                for field in fields {
                    match field {
                        TypeField::Field { name, ty } => {
                            let ty = self.lower(ty);
                            add(self, name, ty);
                        }
                        TypeField::Spread(spread) => {
                            let ty = self.lower(spread);
                            match relate::fields_of(db, self.program, ty) {
                                Some(fields) => {
                                    for (name, ty) in fields {
                                        add(self, name, ty);
                                    }
                                }
                                None if ty.is_error(db) => {}
                                None => {
                                    let kind = ErrorKind::Unsupported("spreads of non-records");
                                    self.error(Site::Type(spread), kind);
                                }
                            }
                        }
                    }
                }
                Ty::record(db, lowered, open)
            }
            TypeRef::Fn {
                params,
                result,
                pure,
            } => {
                let (params, result, pure) = (params.clone(), *result, *pure);
                let params = params.into_iter().map(|p| self.lower(p)).collect();
                let result = self.lower(result);
                Ty::new(
                    db,
                    TyKind::Fn {
                        params,
                        result,
                        pure,
                    },
                )
            }
            TypeRef::Union(members) => {
                let members: Vec<_> = members.clone().into_iter().map(|m| self.lower(m)).collect();
                let (ty, overlaps) = relate::normalize(db, self.program, members);
                for (member, container) in overlaps {
                    self.error(Site::Type(id), ErrorKind::Overlap { member, container });
                }
                ty
            }
        };
        self.types[id.index()] = Some(ty);
        ty
    }

    fn named(
        &mut self,
        id: TypeRefId,
        name: Name<'db>,
        target: TypeTarget<'db>,
        args: &[TypeArg],
    ) -> Ty<'db> {
        let db = self.db;
        let item = match target {
            TypeTarget::Unresolved => return Ty::error(db),
            TypeTarget::Param(index) => {
                if !args.is_empty() {
                    let kind = ErrorKind::TypeArgCount {
                        expected: 0,
                        found: args.len(),
                    };
                    self.error(Site::Type(id), kind);
                }
                return Ty::new(db, TyKind::Param(self.owner, index, name));
            }
            TypeTarget::Item(item) => item,
        };
        let header = type_header(db, self.program, item);
        let (kind, arity) = (header.kind, header.params.len());
        if kind == HeaderKind::Form {
            self.error(Site::Type(id), ErrorKind::Unsupported("forms as types"));
            return Ty::error(db);
        }
        if args.len() != arity {
            let kind = ErrorKind::TypeArgCount {
                expected: arity,
                found: args.len(),
            };
            self.error(Site::Type(id), kind);
            return Ty::error(db);
        }
        if let HeaderKind::Builtin(Builtin::Fixed(_)) = kind {
            return match args {
                [TypeArg::Int(scale)] if *scale <= 18 => {
                    Ty::builtin(db, Builtin::Fixed(*scale as u32))
                }
                _ => {
                    self.error(Site::Type(id), ErrorKind::TypeArgKind);
                    Ty::error(db)
                }
            };
        }
        let mut lowered = Vec::new();
        for arg in args {
            match arg {
                TypeArg::Type(t) => lowered.push(self.lower(*t)),
                TypeArg::Int(_) => {
                    self.error(Site::Type(id), ErrorKind::TypeArgKind);
                    lowered.push(Ty::error(db));
                }
                TypeArg::Is(_) => {
                    self.error(Site::Type(id), ErrorKind::Unsupported("`is` arguments"));
                    lowered.push(Ty::error(db));
                }
            }
        }
        match kind {
            HeaderKind::Builtin(f @ (Builtin::Oks | Builtin::Errs)) => {
                relate::type_function(db, self.program, f, lowered[0])
            }
            HeaderKind::Builtin(builtin) => Ty::new(db, TyKind::Builtin(builtin, lowered)),
            HeaderKind::Alias => match alias_target(db, self.program, item) {
                Some(target) => subst(db, self.program, target, item, &lowered),
                None => Ty::error(db),
            },
            _ => Ty::new(
                db,
                TyKind::Named(type_identity(db, self.program, item), lowered),
            ),
        }
    }
}
