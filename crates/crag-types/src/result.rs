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

//! What inference reports: a type for every node of a body, the target of
//! every call, and the errors, each at the node it is about.

use crag_db::Db;
use crag_hir::{BindingId, BodySourceMap, ExprId, ItemId, Name, PatId, TypeRefId};

use crate::ty::Ty;

#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct InferenceResult<'db> {
    /// By `ExprId`, `PatId`, `BindingId` and `TypeRefId`. What failed to
    /// type has the error type.
    pub exprs: Vec<Option<Ty<'db>>>,
    pub pats: Vec<Option<Ty<'db>>>,
    pub bindings: Vec<Option<Ty<'db>>>,
    pub types: Vec<Option<Ty<'db>>>,
    /// What each call, method call, field access and operator calls, by
    /// the `ExprId` of the call.
    pub callees: Vec<(ExprId, Callee<'db>)>,
    /// The type of a function's result, or of a module-level `let`'s
    /// value.
    pub result: Option<Ty<'db>>,
    /// Every `???` with the type it must have (§6.11).
    pub holes: Vec<(ExprId, Ty<'db>)>,
    pub errors: Vec<TypeError<'db>>,
}

impl<'db> InferenceResult<'db> {
    pub fn expr(&self, id: ExprId) -> Option<Ty<'db>> {
        self.exprs.get(id.index()).copied().flatten()
    }

    pub fn pat(&self, id: PatId) -> Option<Ty<'db>> {
        self.pats.get(id.index()).copied().flatten()
    }

    pub fn binding(&self, id: BindingId) -> Option<Ty<'db>> {
        self.bindings.get(id.index()).copied().flatten()
    }

    pub fn callee(&self, id: ExprId) -> Option<&Callee<'db>> {
        self.callees.iter().find(|(e, _)| *e == id).map(|(_, c)| c)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Callee<'db> {
    /// A declared function.
    Function(ItemId<'db>),
    /// A function value: a local function, a closure or a field.
    Value,
    /// The construction of a record or collection type (§6.7).
    Construct(Ty<'db>),
}

/// A node of a body, where an error is reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Site {
    Expr(ExprId),
    Pat(PatId),
    Type(TypeRefId),
    Binding(BindingId),
}

impl Site {
    pub fn range(self, map: &BodySourceMap) -> Option<std::ops::Range<u32>> {
        match self {
            Site::Expr(id) => map.exprs.get(id.index()),
            Site::Pat(id) => map.pats.get(id.index()),
            Site::Type(id) => map.types.get(id.index()),
            Site::Binding(id) => map.bindings.get(id.index()),
        }
        .cloned()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct TypeError<'db> {
    pub site: Site,
    pub kind: ErrorKind<'db>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum ErrorKind<'db> {
    Mismatch {
        expected: Ty<'db>,
        found: Ty<'db>,
    },
    /// A literal that does not fit its type, or no type of the context.
    Literal {
        ty: Ty<'db>,
    },
    /// No function of this name accepts the arguments.
    NoMatch {
        name: Name<'db>,
        args: Vec<Ty<'db>>,
    },
    /// Several do (§5.6.1).
    Ambiguous {
        name: Name<'db>,
        candidates: Vec<ItemId<'db>>,
    },
    ArgCount {
        expected: usize,
        found: usize,
    },
    /// A named argument that names no parameter.
    UnknownParam {
        name: Name<'db>,
    },
    /// A parameter without a default that no argument gives.
    MissingArg {
        name: Name<'db>,
    },
    NotCallable {
        ty: Ty<'db>,
    },
    NoField {
        ty: Ty<'db>,
        name: Name<'db>,
    },
    MissingField {
        name: Name<'db>,
    },
    UnknownField {
        name: Name<'db>,
    },
    DuplicateField {
        name: Name<'db>,
    },
    NotIndexable {
        ty: Ty<'db>,
    },
    NotIterable {
        ty: Ty<'db>,
    },
    /// Nothing in the context fixes the type: an empty list, or a closure
    /// parameter without a type.
    CannotInfer,
    /// A pattern that no value of the subject's type can match.
    NeverMatches {
        pattern: Ty<'db>,
        subject: Ty<'db>,
    },
    TypeArgCount {
        expected: usize,
        found: usize,
    },
    /// `Fixed` without a scale, or a scale where a type is expected.
    TypeArgKind,
    /// A union written with a member another member contains (§3.6.1).
    Overlap {
        member: Ty<'db>,
        container: Ty<'db>,
    },
    /// An alias that refers to itself (§3.5).
    AliasCycle,
    /// A function whose success type depends on itself and is not written
    /// (§3.13.1).
    RecursiveSuccess {
        function: ItemId<'db>,
    },
    /// A module-level value whose type depends on itself.
    ValueCycle {
        value: ItemId<'db>,
    },
    /// The `else` of a `let … else` that can finish normally (§7.1.1).
    MustLeave,
    /// A record type or a form where a value is expected.
    NotAValue {
        name: Name<'db>,
    },
    /// A range over a type that does not fit `Discrete` (§7.4).
    NotDiscrete {
        ty: Ty<'db>,
    },
    /// A range whose constant ends decrease (§7.4).
    Decreasing,
    /// An arm, or an alternative of one, that earlier arms cover (§7.2).
    Unreachable,
    /// A `case` that misses a value, shown as a pattern.
    NotExhaustive {
        missing: String,
    },
    /// The pattern of a `let` or a `for` that misses a value.
    Refutable {
        missing: String,
    },
    /// Something core inference does not handle yet; later milestones of
    /// the Implementation Plan add it.
    Unsupported(&'static str),
}

impl<'db> ErrorKind<'db> {
    pub fn message(&self, db: &'db dyn Db) -> String {
        let name = |n: &Name<'db>| n.text(db).clone();
        let item = |i: &ItemId<'db>| i.name(db).text(db).clone();
        match self {
            ErrorKind::Mismatch { expected, found } => format!(
                "expected {}, found {}",
                expected.display(db),
                found.display(db)
            ),
            ErrorKind::Literal { ty } => format!("the literal does not fit {}", ty.display(db)),
            ErrorKind::NoMatch { name: n, args } => format!(
                "no function `{}` takes ({})",
                name(n),
                args.iter()
                    .map(|t| t.display(db))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ErrorKind::Ambiguous {
                name: n,
                candidates,
            } => format!(
                "the call of `{}` fits {} functions",
                name(n),
                candidates.len()
            ),
            ErrorKind::ArgCount { expected, found } => {
                format!("expected {expected} arguments, found {found}")
            }
            ErrorKind::UnknownParam { name: n } => format!("there is no parameter `{}`", name(n)),
            ErrorKind::MissingArg { name: n } => format!("the argument `{}` is missing", name(n)),
            ErrorKind::NotCallable { ty } => format!("{} cannot be called", ty.display(db)),
            ErrorKind::NoField { ty, name: n } => {
                format!("{} has no field `{}`", ty.display(db), name(n))
            }
            ErrorKind::MissingField { name: n } => format!("the field `{}` is missing", name(n)),
            ErrorKind::UnknownField { name: n } => format!("there is no field `{}`", name(n)),
            ErrorKind::DuplicateField { name: n } => {
                format!("the field `{}` is given twice", name(n))
            }
            ErrorKind::NotIndexable { ty } => format!("{} cannot be indexed", ty.display(db)),
            ErrorKind::NotIterable { ty } => format!("{} cannot be iterated", ty.display(db)),
            ErrorKind::CannotInfer => "the type cannot be inferred here; write it".into(),
            ErrorKind::NeverMatches { pattern, subject } => format!(
                "a {} pattern never matches a {}",
                pattern.display(db),
                subject.display(db)
            ),
            ErrorKind::TypeArgCount { expected, found } => {
                format!("expected {expected} type arguments, found {found}")
            }
            ErrorKind::TypeArgKind => "`Fixed` takes a number of digits, other types a type".into(),
            ErrorKind::Overlap { member, container } => format!(
                "{} is already part of {}",
                member.display(db),
                container.display(db)
            ),
            ErrorKind::AliasCycle => "the alias refers to itself".into(),
            ErrorKind::RecursiveSuccess { function } => format!(
                "`{}` is recursive, so it must state its success type",
                item(function)
            ),
            ErrorKind::ValueCycle { value } => {
                format!("the value `{}` depends on itself", item(value))
            }
            ErrorKind::MustLeave => "the `else` of a `let … else` must leave".into(),
            ErrorKind::NotAValue { name: n } => format!("`{}` is not a value", name(n)),
            ErrorKind::NotDiscrete { ty } => {
                format!("{} is not Discrete, so it forms no range", ty.display(db))
            }
            ErrorKind::Decreasing => {
                "the range decreases; its first end must not exceed its last".into()
            }
            ErrorKind::Unreachable => "the pattern is unreachable; earlier arms cover it".into(),
            ErrorKind::NotExhaustive { missing } => {
                format!("the `case` does not cover `{missing}`")
            }
            ErrorKind::Refutable { missing } => {
                format!("the pattern does not cover `{missing}`")
            }
            ErrorKind::Unsupported(what) => format!("{what} are not supported yet"),
        }
    }
}
