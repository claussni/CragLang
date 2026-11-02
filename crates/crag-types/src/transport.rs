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

//! What a closure literal sent as an `Expr` may hold (Specification §18.6,
//! Implementation Plan §11.10.13). Its body is `Pure` and its captures
//! `Solid`, which inference checks against `F`; here are the rest: no
//! `ref` or `ext`, as bindings or captures, no `atomic`, `embed` or `on`
//! handler, no `???`, and no capture that holds a `Secret`. A module value
//! the body reads is a capture too, and checked as one.

use crag_db::Db;
use crag_hir::{BindingKind, Body, Expr, ExprId, ItemId, Program, Resolution, Stmt};

use crate::def::value_type;
use crate::marker::{holds_secret, solid};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::Ty;

/// A form that code sent as an `Expr` may not hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Untransported {
    Ref,
    Ext,
    Atomic,
    Embed,
    On,
    Hole,
}

impl Untransported {
    pub fn text(self) -> &'static str {
        match self {
            Untransported::Ref => "a `ref` binding",
            Untransported::Ext => "an `ext` binding",
            Untransported::Atomic => "an `atomic` block",
            Untransported::Embed => "an `embed`",
            Untransported::On => "an `on` handler",
            Untransported::Hole => "`???`, which can only trap",
        }
    }
}

/// The errors of a closure literal sent as an `Expr`, its nested closures
/// and local functions included. `bindings` are the types inferred so far.
pub(crate) fn literal_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    body: &Body<'db>,
    bindings: &[Option<Ty<'db>>],
    closure: ExprId,
) -> Vec<TypeError<'db>> {
    let mut errors = Vec::new();
    let mut error = |site, kind| errors.push(TypeError { site, kind });
    let mut pending = vec![closure];
    while let Some(e) = pending.pop() {
        let form = match body.expr(e) {
            Expr::Atomic(_) => Some(Untransported::Atomic),
            Expr::Embed => Some(Untransported::Embed),
            Expr::Hole => Some(Untransported::Hole),
            Expr::Block { stmts, .. } => {
                for stmt in stmts {
                    let (site, form) = match stmt {
                        Stmt::Bind { binding, .. } => match body.binding(*binding).kind {
                            BindingKind::Ref => (Site::Binding(*binding), Untransported::Ref),
                            BindingKind::Ext => (Site::Binding(*binding), Untransported::Ext),
                            _ => continue,
                        },
                        Stmt::On { handler, .. } => (Site::Expr(*handler), Untransported::On),
                        _ => continue,
                    };
                    error(site, ErrorKind::NotTransportable { form });
                }
                None
            }
            _ => None,
        };
        if let Some(form) = form {
            error(Site::Expr(e), ErrorKind::NotTransportable { form });
        }
        pending.extend(body.children(e).into_iter().rev());
    }
    for binding in body.free_bindings(closure) {
        let declared = body.binding(binding);
        let Some(name) = declared.name else {
            continue;
        };
        match declared.kind {
            BindingKind::Ref | BindingKind::Ext => {
                let ext = declared.kind == BindingKind::Ext;
                error(Site::Expr(closure), ErrorKind::CellCapture { name, ext });
            }
            // A local function is code, which the tree does not bundle.
            BindingKind::Fn => {
                error(Site::Expr(closure), ErrorKind::OuterFunction { name });
            }
            _ => {
                let ty = bindings.get(binding.index()).copied().flatten();
                if let Some(ty) = ty
                    && let Some(path) = holds_secret(db, program, ty)
                {
                    error(
                        Site::Expr(closure),
                        ErrorKind::SecretCapture {
                            name,
                            ty,
                            path: path.clone(),
                        },
                    );
                }
            }
        }
    }
    // A module value the body reads is a capture too, read when the
    // `Expr` is made (§18.6), so it is checked as one: a session's values
    // need not be Solid.
    for (value, at) in module_values(body, closure) {
        let Expr::Name { name, .. } = body.expr(at) else {
            continue;
        };
        let Some(ty) = value_type(db, program, value) else {
            continue;
        };
        if let Err(why) = solid(db, program, ty) {
            let kind = ErrorKind::PureCapture {
                name: *name,
                ty,
                why: why.clone(),
            };
            error(Site::Expr(at), kind);
        } else if let Some(path) = holds_secret(db, program, ty) {
            let kind = ErrorKind::SecretCapture {
                name: *name,
                ty,
                path: path.clone(),
            };
            error(Site::Expr(at), kind);
        }
    }
    errors
}

/// The module values the body of a closure sent as an `Expr` reads, each
/// with where it is first read, in that order: its captures after those
/// of its bindings, in its environment and its tree alike (§18.6).
pub fn module_values<'db>(body: &Body<'db>, closure: ExprId) -> Vec<(ItemId<'db>, ExprId)> {
    let mut out: Vec<(ItemId<'db>, ExprId)> = Vec::new();
    let mut pending = vec![closure];
    while let Some(e) = pending.pop() {
        if let Expr::Name {
            local: None,
            item: Some(Resolution::Value {
                value: Some(value), ..
            }),
            ..
        } = body.expr(e)
            && !out.iter().any(|(v, _)| v == value)
        {
            out.push((*value, e));
        }
        pending.extend(body.children(e).into_iter().rev());
    }
    out
}
