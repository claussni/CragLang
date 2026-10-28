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

//! The checks of C imports (Specification §16): the types of C functions,
//! the thread safety of their libraries, and the libraries the manifest
//! declares.

use crag_db::Db;
use crag_hir::{Import, ItemId, ModuleId, Owner, PRELUDE, Program, Threading, hir_body, item_tree};

use crate::def::{c_out, c_signature, is_cstr};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// What a parameter or result of a C function is at the seam
/// (Specification §16.1, §3.1.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CForm {
    /// A sized integer, `Float`, `CF32` or `CPtr[T]`, passed as it is.
    Value,
    /// `()`, a result without a value.
    Void,
    CStr,
    /// `Option[CStr]`: a null pointer is `Empty`.
    OptionCStr,
    /// A `char*` result copied to text at once.
    Str,
    OptionStr,
    /// `Float` united with the tags of a NaN and the infinities, in this
    /// order, that it has.
    Float([bool; 3]),
    /// No C type.
    Invalid,
}

/// The names of the tags a `CForm::Float` may hold.
pub const NON_FINITE: [&str; 3] = ["NaN", "PosInfinity", "NegInfinity"];

impl CForm {
    pub fn of<'db>(db: &'db dyn Db, ty: Ty<'db>) -> CForm {
        if is_cstr(db, ty) {
            return CForm::CStr;
        }
        let named = |t: Ty<'db>, name: &str| match t.kind(db) {
            TyKind::Named(item, _) => {
                item.name(db).text(db) == name && item.module(db).path(db) == PRELUDE
            }
            _ => false,
        };
        match ty.kind(db) {
            TyKind::Record {
                fields,
                open: false,
            } if fields.is_empty() => CForm::Void,
            TyKind::Builtin(Builtin::Str, _) => CForm::Str,
            TyKind::Builtin(
                Builtin::Int
                | Builtin::Int8
                | Builtin::Int16
                | Builtin::Int32
                | Builtin::UInt8
                | Builtin::UInt16
                | Builtin::UInt32
                | Builtin::UInt64
                | Builtin::Float
                | Builtin::CF32
                | Builtin::CPtr,
                _,
            ) => CForm::Value,
            TyKind::Union(members) => {
                let empty = members.iter().any(|&m| named(m, "Empty"));
                let present: Vec<Ty<'db>> = members
                    .iter()
                    .copied()
                    .filter(|&m| !named(m, "Empty"))
                    .collect();
                match (empty, &present[..]) {
                    (true, [one]) if is_cstr(db, *one) => return CForm::OptionCStr,
                    (true, [one]) if matches!(one.as_builtin(db), Some((Builtin::Str, _))) => {
                        return CForm::OptionStr;
                    }
                    _ => {}
                }
                let float = members
                    .iter()
                    .any(|m| matches!(m.as_builtin(db), Some((Builtin::Float, _))));
                let tags = NON_FINITE.map(|name| members.iter().any(|&m| named(m, name)));
                let known = members.iter().all(|&m| {
                    matches!(m.as_builtin(db), Some((Builtin::Float, _)))
                        || NON_FINITE.iter().any(|name| named(m, name))
                });
                match float && known {
                    true => CForm::Float(tags),
                    false => CForm::Invalid,
                }
            }
            TyKind::Error => CForm::Value,
            _ => CForm::Invalid,
        }
    }

    /// Whether a parameter may have this form; an out parameter takes only
    /// plain values.
    pub fn takes(self, out: bool) -> bool {
        match self {
            CForm::Value => true,
            CForm::CStr | CForm::OptionCStr | CForm::Float(_) => !out,
            _ => false,
        }
    }

    /// Whether a result may have this form.
    pub fn gives(self) -> bool {
        self != CForm::Invalid
    }
}

/// The errors of the C imports of a module.
pub fn c_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(ItemId<'db>, TypeError<'db>)> {
    let mut errors = Vec::new();
    for import in &item_tree(db, module).imports {
        let Import::C {
            library,
            functions,
            threading,
            ..
        } = import
        else {
            continue;
        };
        for function in functions {
            types(db, program, function.id, &mut errors);
        }
        let Some(first) = functions.first() else {
            continue;
        };
        if let Some((there, other)) = other_threading(db, program, library, *threading) {
            let kind = ErrorKind::ThreadingMismatch {
                library: library.clone(),
                here: threading.name(),
                there: there.name(),
                module: other.path(db).clone(),
            };
            errors.push((
                first.id,
                TypeError {
                    site: Site::Name,
                    kind,
                },
            ));
        }
        let packages = program.packages(db);
        let path = module.path(db);
        if let Some(package) = packages.of(path).or(packages.packages.first())
            && !package.natives.iter().any(|(name, _)| name == library)
        {
            let kind = ErrorKind::UndeclaredLibrary {
                library: library.clone(),
                package: package.name.clone(),
            };
            errors.push((
                first.id,
                TypeError {
                    site: Site::Name,
                    kind,
                },
            ));
        }
    }
    errors
}

/// The parameters and result of a C function that are no C types.
fn types<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
    errors: &mut Vec<(ItemId<'db>, TypeError<'db>)>,
) {
    let body = hir_body(db, program, Owner::Item(function));
    let (params, result) = c_signature(db, program, function);
    let mut check = |ty: Ty<'db>, site: Option<Site>, is_result: bool| {
        let (ty, out) = match c_out(db, ty) {
            Some(inner) if !is_result => (inner, true),
            _ => (ty, false),
        };
        let form = CForm::of(db, ty);
        let fits = if is_result {
            form.gives()
        } else {
            form.takes(out)
        };
        if !fits {
            let kind = ErrorKind::NotCType { ty, out };
            errors.push((
                function,
                TypeError {
                    site: site.unwrap_or(Site::Name),
                    kind,
                },
            ));
        }
    };
    for (param, &ty) in body.params.iter().zip(&params) {
        check(ty, Some(Site::Type(param.ty)), false);
    }
    check(result, body.result.map(Site::Type), true);
}

/// Another import of the library in the program with another marker, and
/// its module.
fn other_threading(
    db: &dyn Db,
    program: Program,
    library: &str,
    threading: Threading,
) -> Option<(Threading, ModuleId)> {
    program.modules(db).iter().find_map(|&other| {
        item_tree(db, other)
            .imports
            .iter()
            .find_map(|import| match import {
                Import::C {
                    library: l,
                    threading: t,
                    ..
                } if l == library && *t != threading => Some((*t, other)),
                _ => None,
            })
    })
}
