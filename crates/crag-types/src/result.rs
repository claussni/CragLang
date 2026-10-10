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

use crate::effect::{EffectSet, Restriction};
use crate::escape::{BindingsOnly, Escapes};
use crate::generic::{FitError, Instance};
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
    /// What the body does beyond computing (§3.14).
    pub effects: EffectSet,
    /// Where its parameters and closures go (§11.5.8).
    pub escapes: Escapes,
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
    /// A generic function with its type arguments and slot fillings
    /// (§11.5.3).
    Instance(Instance<'db>),
    /// A slot of the generic function being checked, by its index.
    Slot(u32),
    /// A function value: a local function, a closure or a field.
    Value,
    /// The construction of a record or collection type (§6.7).
    Construct(Ty<'db>),
    /// A call split by the members of its union arguments, or a function
    /// value that splits its parameters so (§4.6.1).
    Dispatch(Dispatch<'db>),
}

/// A lifted call: the arguments it splits and one call per combination
/// of their members (§11.5.5).
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Dispatch<'db> {
    /// The positional arguments split, the receiver first, or the
    /// parameters of a function value.
    pub args: Vec<usize>,
    /// The members of each, in the order of the union.
    pub members: Vec<Vec<Ty<'db>>>,
    /// One per combination of members, the last argument's member
    /// varying fastest.
    pub arms: Vec<DispatchArm<'db>>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct DispatchArm<'db> {
    /// A declared function, an instance or a slot.
    pub callee: Callee<'db>,
    pub result: Ty<'db>,
}

impl<'db> Dispatch<'db> {
    /// The arm for the members at these indices, one per split argument.
    pub fn arm(&self, indices: &[usize]) -> &DispatchArm<'db> {
        let index = indices
            .iter()
            .zip(&self.members)
            .fold(0, |n, (&i, members)| n * members.len() + i);
        &self.arms[index]
    }
}

/// A node of a body, where an error is reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Site {
    Expr(ExprId),
    Pat(PatId),
    Type(TypeRefId),
    Binding(BindingId),
    /// The name of the declaration.
    Name,
}

impl Site {
    pub fn range(self, map: &BodySourceMap) -> Option<std::ops::Range<u32>> {
        match self {
            Site::Expr(id) => map.exprs.get(id.index()),
            Site::Pat(id) => map.pats.get(id.index()),
            Site::Type(id) => map.types.get(id.index()),
            Site::Binding(id) => map.bindings.get(id.index()),
            Site::Name => Some(&map.name),
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
    /// A lifted call whose members have no function that takes them
    /// (§4.6.1).
    NoLift {
        name: Name<'db>,
        members: Vec<Ty<'db>>,
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
    /// A recursive group with members that state no success type, at the
    /// call that links them (§3.13.1).
    RecursiveGroup {
        members: Vec<ItemId<'db>>,
        missing: Vec<ItemId<'db>>,
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
    /// `pass` anywhere but as the body of a `case` arm (§8.2).
    PassOutsideCase,
    /// A type parameter of a called generic function that neither the
    /// arguments nor the context fix.
    UninferredTypeArg {
        function: ItemId<'db>,
        name: Name<'db>,
    },
    /// Type arguments that do not fit the bounds of a generic function.
    Unfit(FitError<'db>),
    /// A `where` entry that names no form (§4.4).
    NotAForm {
        ty: Ty<'db>,
    },
    /// A bound that unites forms with types (§4.7).
    MixedBound,
    /// `check` or `expect` of a value without errors (§8.4).
    NoErrors {
        function: ItemId<'db>,
    },
    /// Two overloads of one module with the same parameter shape and
    /// incomparable bounds, without their combined overload (§5.6.1).
    MissingCombined {
        other: ItemId<'db>,
        signature: String,
    },
    /// A call with viable candidates from several modules, which are
    /// never ranked (§5.6.1).
    SeveralModules {
        name: Name<'db>,
        modules: Vec<String>,
    },
    /// `check` of a value whose successes contain `Empty`, which its
    /// failure would merge with (§8.4).
    EmptyMerges,
    /// Effects a restricted context does not allow (§3.14): an `ext`
    /// access is told apart from other `io`.
    Effect {
        effects: EffectSet,
        ext: bool,
        restriction: Restriction,
    },
    /// A call of an `is Pure` function that passes it a function with
    /// effects.
    PureCall {
        function: ItemId<'db>,
    },
    /// A bindings-only value that is returned, stored, emitted or passed
    /// to an unknown function (§3.12, §9.2).
    BindingsOnly {
        what: BindingsOnly,
    },
    /// An escaping closure that captures a `var` (§6.4.1).
    EscapingVar {
        name: Name<'db>,
    },
    /// A ref resolved in another ref's `update` closure (§9.5).
    SecondRef,
    /// An `ext` accessed in an `ext` closure (§9.6).
    NestedExt,
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
            ErrorKind::NoLift { name: n, members } => format!(
                "no function `{}` takes ({}), which union lifting needs for each member",
                name(n),
                members
                    .iter()
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
            ErrorKind::RecursiveGroup { members, missing } => {
                let list = |items: &[ItemId<'db>]| {
                    let names: Vec<String> =
                        items.iter().map(|i| format!("`{}`", item(i))).collect();
                    match names.split_last() {
                        Some((last, [])) => last.clone(),
                        Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
                        None => String::new(),
                    }
                };
                let (verb, what) = match missing.len() {
                    1 => ("its", "success type"),
                    _ => ("their", "success types"),
                };
                format!(
                    "this call makes {} recursive, so {} must state {verb} {what}",
                    list(members),
                    list(missing)
                )
            }
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
            ErrorKind::PassOutsideCase => "`pass` stands only as the body of a `case` arm".into(),
            ErrorKind::UninferredTypeArg { function, name: n } => format!(
                "the type parameter `{}` of `{}` cannot be inferred",
                name(n),
                item(function)
            ),
            ErrorKind::Unfit(fit) => fit.message(db),
            ErrorKind::NotAForm { ty } => format!("{} is not a form", ty.display(db)),
            ErrorKind::MixedBound => "a bound unites forms or types, not both".into(),
            ErrorKind::NoErrors { function } => {
                format!("`{}` of a value that has no errors", item(function))
            }
            ErrorKind::MissingCombined { other, signature } => format!(
                "this overload and an earlier `{}` take the same parameters with incomparable bounds; add `{signature}`",
                item(other)
            ),
            ErrorKind::SeveralModules { name: n, modules } => format!(
                "`{}` has viable candidates from several modules ({}); import one of them selectively",
                name(n),
                modules.join(", ")
            ),
            ErrorKind::EmptyMerges => {
                "`check` of a value that can be `Empty` would merge success and failure".into()
            }
            ErrorKind::Effect {
                effects,
                ext,
                restriction,
            } => {
                let context = match restriction {
                    Restriction::Pure => "an `is Pure` function",
                    Restriction::Atomic => "an `atomic` block",
                    Restriction::Update => "an `update` closure",
                };
                if *ext {
                    format!("this accesses an `ext`, which {context} does not allow")
                } else {
                    let names: Vec<String> =
                        effects.names().iter().map(|n| format!("`{n}`")).collect();
                    let s = if names.len() == 1 { "" } else { "s" };
                    format!(
                        "this has the effect{s} {}, which {context} does not allow",
                        names.join(", ")
                    )
                }
            }
            ErrorKind::PureCall { function } => format!(
                "`{}` is Pure, so the functions passed to it must have no effects",
                item(function)
            ),
            ErrorKind::BindingsOnly { what } => {
                let what = match what {
                    BindingsOnly::Ref => "a ref",
                    BindingsOnly::Ext => "an `ext` cell",
                    BindingsOnly::Closure => "a closure that carries a ref",
                    BindingsOnly::Lazy => "a `lazy` value that carries a ref",
                };
                format!(
                    "{what} is bindings-only: it cannot be returned, stored, emitted or passed to an unknown function"
                )
            }
            ErrorKind::EscapingVar { name: n } => format!(
                "this closure escapes, so it cannot capture the `var` `{}`",
                name(n)
            ),
            ErrorKind::SecondRef => {
                "an `update` closure resolves only its own ref; update several in an `atomic` block"
                    .into()
            }
            ErrorKind::NestedExt => {
                "an `ext` closure accesses no other `ext`, so that locks never nest".into()
            }
            ErrorKind::Unsupported(what) => format!("{what} are not supported yet"),
        }
    }
}
