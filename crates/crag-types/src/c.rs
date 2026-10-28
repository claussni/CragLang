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
use crag_hir::{Import, ItemId, ModuleId, Owner, Program, Threading, hir_body, item_tree};

use crate::def::{c_out, c_signature, is_cstr};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

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
        let unit =
            matches!(ty.kind(db), TyKind::Record { fields, open: false } if fields.is_empty());
        let fits = match ty.kind(db) {
            TyKind::Error => true,
            _ if is_cstr(db, ty) => !out,
            _ if unit => is_result,
            TyKind::Builtin(b, _) => matches!(
                b,
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
                    | Builtin::CPtr
            ),
            _ => false,
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
