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

//! The HIR (Implementation Plan §11.4.6): bodies as resolved, desugared
//! trees.
//!
//! A body keeps its expressions, patterns, types and bindings in arenas
//! indexed by small integers. Names refer to bindings or to items;
//! operators and prefixes are calls; named arguments form a field list on
//! their call; `_` arguments have become closures. A body holds no
//! positions, so it stays equal when only the text around it moves; the
//! `BodySourceMap` beside it maps every node back to its range.

use crate::items::{ItemId, Name};
use crate::literal::Literal;
use crate::scope::Resolution;

macro_rules! id {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, crag_db::SalsaValue)]
        pub struct $name(pub u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(ExprId);
id!(PatId);
id!(TypeRefId);
id!(BindingId);

/// A function's, a module-level value's or a test's body.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Body<'db> {
    pub exprs: Vec<Expr<'db>>,
    pub pats: Vec<Pat<'db>>,
    pub types: Vec<TypeRef<'db>>,
    pub bindings: Vec<Binding<'db>>,
    /// The type parameters of the function and of its local functions.
    pub type_params: Vec<Name<'db>>,
    /// A function's parameters.
    pub params: Vec<Param>,
    /// A function's written result type.
    pub result: Option<TypeRefId>,
    /// A module-level `let`: its pattern, whose bindings are the module's
    /// values, and its type.
    pub pattern: Option<(PatId, Option<TypeRefId>)>,
    /// The block of a function or test, the value of a `let`; none for a
    /// function without a body (§19.2).
    pub root: Option<ExprId>,
    /// A type declaration's fields, parent and alias target.
    pub type_decl: Option<TypeDecl<'db>>,
}

/// A type declaration (§3.2–3.9). Its clauses are not lowered yet.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct TypeDecl<'db> {
    /// Whether it has a field list; a tag has none (§3.2).
    pub record: bool,
    /// The spread parent (§3.8).
    pub parent: Option<TypeRefId>,
    pub fields: Vec<FieldDecl<'db>>,
    /// `type X = T` (§3.5).
    pub alias: Option<TypeRefId>,
    pub distinct: bool,
    pub opaque: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct FieldDecl<'db> {
    pub name: Name<'db>,
    pub ty: TypeRefId,
    pub default: Option<ExprId>,
}

impl<'db> Body<'db> {
    pub fn expr(&self, id: ExprId) -> &Expr<'db> {
        &self.exprs[id.index()]
    }

    pub fn pat(&self, id: PatId) -> &Pat<'db> {
        &self.pats[id.index()]
    }

    pub fn type_ref(&self, id: TypeRefId) -> &TypeRef<'db> {
        &self.types[id.index()]
    }

    pub fn binding(&self, id: BindingId) -> &Binding<'db> {
        &self.bindings[id.index()]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Binding<'db> {
    /// None for the bindings lowering introduces itself.
    pub name: Option<Name<'db>>,
    pub kind: BindingKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum BindingKind {
    Let,
    Var,
    Ref,
    Ext,
    Param,
    /// A local function's name (§5.6.4).
    Fn,
    /// A name a module-level `let` binds: a value of the module.
    Module,
    /// A missing argument of a partial application (§6.6).
    Hole,
    /// A supplied argument of a partial application, evaluated once where
    /// the closure is made.
    Supplied,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Param {
    pub binding: BindingId,
    pub ty: TypeRefId,
    pub default: Option<ExprId>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Expr<'db> {
    /// Left by a syntax error or an unresolved name, which were reported.
    Missing,
    /// `???` (§6.11).
    Hole,
    Literal(Literal),
    /// A string with interpolations.
    Str(Vec<StrPart>),
    /// A name: a local binding, items, or both, since a binding may share
    /// its name with functions (§5.4).
    Name {
        name: Name<'db>,
        local: Option<BindingId>,
        item: Option<Resolution<'db>>,
    },
    /// A call. A call of a type is a construction or a conversion (§5.6).
    /// Named arguments and spreads form one field list, which inference
    /// turns into the single record parameter or into defaulted parameters
    /// (§5.6.2).
    Call {
        callee: ExprId,
        args: Vec<ExprId>,
        fields: Option<Vec<FieldArg<'db>>>,
    },
    /// `x.f(args)`: a call of the field `f`, if `x` has one, or of one of
    /// `functions` with `x` as the first argument (§6.3).
    MethodCall {
        receiver: ExprId,
        name: Name<'db>,
        functions: Vec<ItemId<'db>>,
        optional: bool,
        args: Vec<ExprId>,
        fields: Option<Vec<FieldArg<'db>>>,
    },
    /// `T.f(args)`: a call of one of `functions` whose success type is `T`.
    TypedCall {
        ty: TypeRefId,
        name: Name<'db>,
        functions: Vec<ItemId<'db>>,
        args: Vec<ExprId>,
        fields: Option<Vec<FieldArg<'db>>>,
    },
    /// `x.f` or `x?.f`: the field, or a call of one of `functions` with `x`
    /// alone.
    Field {
        receiver: ExprId,
        name: Name<'db>,
        functions: Vec<ItemId<'db>>,
        optional: bool,
    },
    /// `e[i]` on a value (§6.5).
    Index {
        base: ExprId,
        args: Vec<ExprId>,
    },
    /// `e[T]` on a type or a function: type arguments.
    TypeArgs {
        base: ExprId,
        args: Vec<TypeArg>,
    },
    /// Short-circuiting `and`, `or` and `not` (§6.2).
    And(ExprId, ExprId),
    Or(ExprId, ExprId),
    Not(ExprId),
    /// `a..b`, or `a..` without an end (§7.4).
    Range {
        start: ExprId,
        end: Option<ExprId>,
    },
    Is {
        expr: ExprId,
        ty: TypeRefId,
    },
    /// A record literal; `()` is the empty one.
    Record(Vec<FieldArg<'db>>),
    List(Vec<ExprId>),
    Map(Vec<(ExprId, ExprId)>),
    Grid(Vec<Vec<ExprId>>),
    Block {
        stmts: Vec<Stmt>,
        /// The last statement, if it is an expression: the block's value.
        tail: Option<ExprId>,
    },
    Closure {
        params: Vec<ClosureParam>,
        body: ExprId,
    },
    If {
        condition: ExprId,
        then: ExprId,
        otherwise: Option<ExprId>,
    },
    /// `case`. A lone `pass` is the arm `_ -> pass`.
    Case {
        subject: ExprId,
        arms: Vec<Arm>,
    },
    /// `pass` in an arm (§8.2).
    Pass,
    Atomic(ExprId),
    Lazy(ExprId),
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum StrPart {
    Text(String),
    Expr(ExprId),
}

/// An entry of a field list: `name: value`, a dotted path into nested
/// records (§6.7), or a spread `..value`.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum FieldArg<'db> {
    Field { path: Vec<Name<'db>>, value: ExprId },
    Spread(ExprId),
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct ClosureParam {
    pub pat: PatId,
    pub ty: Option<TypeRefId>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Arm {
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Stmt {
    Expr(ExprId),
    Let {
        pat: PatId,
        ty: Option<TypeRefId>,
        value: ExprId,
    },
    /// `let pat: T = value else …` (§7.1.1): binds when the value matches,
    /// with `T` as a type test, and otherwise runs `otherwise`, a block or
    /// a closure of the unmatched value, which must leave.
    LetElse {
        pat: PatId,
        ty: Option<TypeRefId>,
        value: ExprId,
        otherwise: ExprId,
    },
    /// `var`, `ref` and `ext`, told apart by the binding's kind.
    Bind {
        binding: BindingId,
        ty: Option<TypeRefId>,
        value: ExprId,
    },
    /// `name = value` on a `var` (§5.2).
    Assign {
        binding: BindingId,
        value: ExprId,
    },
    For {
        pat: PatId,
        iterable: ExprId,
        body: ExprId,
    },
    Emit {
        kind: Option<EmitKind>,
        value: ExprId,
    },
    Return(Option<ExprId>),
    /// `on T handler` (§8.3.1, §11.3).
    On {
        ty: TypeRefId,
        handler: ExprId,
    },
    /// A local function (§5.6.4), visible from its declaration on.
    Fn {
        binding: BindingId,
        function: LocalFn,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum EmitKind {
    Ok,
    Fail,
    Retry,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct LocalFn {
    pub params: Vec<Param>,
    pub result: Option<TypeRefId>,
    pub body: Option<ExprId>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Pat<'db> {
    Missing,
    Wildcard,
    /// A new binding, or `name: pattern`, which binds and matches.
    Bind {
        binding: BindingId,
        sub: Option<PatId>,
    },
    /// A type or a tag, with type arguments if written.
    Type(TypeRefId),
    /// `T(fields)` or an anonymous `(fields)`.
    Record {
        ty: Option<TypeRefId>,
        fields: Vec<PatField<'db>>,
    },
    /// `[a, b, ..rest]`: the patterns before and after the rest, and the
    /// rest's binding.
    List {
        before: Vec<PatId>,
        rest: Option<Option<BindingId>>,
        after: Vec<PatId>,
    },
    Literal(Literal),
    Range {
        start: Literal,
        end: Literal,
    },
    /// Alternatives, which bind the same names to the same bindings.
    Or(Vec<PatId>),
}

/// A field of a record pattern: by name, or by position for a named type.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct PatField<'db> {
    pub name: Option<Name<'db>>,
    pub pat: PatId,
}

/// A written type, with its names resolved.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum TypeRef<'db> {
    Missing,
    /// `_`.
    Infer,
    /// `()`.
    Unit,
    Named {
        name: Name<'db>,
        target: TypeTarget<'db>,
        args: Vec<TypeArg>,
    },
    Record {
        fields: Vec<TypeField<'db>>,
        /// A trailing `..`: extra fields are accepted (§3.8.1).
        open: bool,
    },
    Fn {
        params: Vec<TypeRefId>,
        result: TypeRefId,
    },
    Union(Vec<TypeRefId>),
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum TypeTarget<'db> {
    /// A type or a form.
    Item(ItemId<'db>),
    /// A type parameter, by index into the body's type parameters.
    Param(u32),
    /// Reported.
    Unresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum TypeArg {
    Type(TypeRefId),
    /// `Fixed[2]`.
    Int(u128),
    /// A trailing `is` clause (§11.4): markers, each possibly negated.
    Is(Vec<(bool, TypeRefId)>),
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum TypeField<'db> {
    Field { name: Name<'db>, ty: TypeRefId },
    Spread(TypeRefId),
}
