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

//! The kinds of syntax tree nodes and leaves.

use crate::token::{TokenKind, TriviaKind};

/// The kind of a leaf: a token, or a piece of the trivia in front of one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LeafKind {
    Token(TokenKind),
    Trivia(TriviaKind),
}

/// The kind of a syntax tree node (Specification Appendix D).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SyntaxKind {
    /// The root: one source file.
    Module,
    /// Tokens the parser skipped to recover from an error.
    Error,

    // Declarations (D.2).
    Import,
    ImportItems,
    ImportItem,
    CImport,
    CSig,
    Path,
    TypeDecl,
    TypeParams,
    TypeParam,
    FieldList,
    Field,
    Spread,
    WhereClause,
    IsClause,
    Marker,
    OnClause,
    FormDecl,
    FormFn,
    FnDecl,
    ParamList,
    Param,
    ReturnType,
    PrefixClause,
    LetDecl,
    LetElse,
    VarDecl,
    RefDecl,
    EmbedDecl,
    TestDecl,

    // Statements (D.3).
    Block,
    Assign,
    ForStmt,
    EmitStmt,
    ReturnStmt,
    OnStmt,

    // Expressions (D.4).
    Literal,
    /// A string with interpolations: `StrStart`, then expressions separated
    /// by `StrMid`, then `StrEnd`.
    StrExpr,
    NameRef,
    /// `_` as an expression: a partial-application hole (§6.6).
    Placeholder,
    ParenExpr,
    RecordExpr,
    ListExpr,
    MapExpr,
    MapEntry,
    GridExpr,
    GridRow,
    Closure,
    ClosureParams,
    ClosureParam,
    IfExpr,
    CaseExpr,
    CaseArm,
    ArmGuard,
    AtomicExpr,
    LazyExpr,
    PassExpr,
    BinExpr,
    /// Unary `-`, `not`, or a prefix (§8.5). A prefix is a run of adjacent
    /// `Symbol` tokens; which declared prefixes it consists of is decided
    /// once the imports are known.
    PrefixExpr,
    RangeExpr,
    IsExpr,
    CallExpr,
    /// Arguments in parentheses, or in brackets for bracket application.
    ArgList,
    LabeledArg,
    Label,
    SpreadArg,
    /// Bracket application `e[…]` (§6.5).
    BracketExpr,
    /// `.name` or `?.name`.
    FieldExpr,

    // Patterns (D.5).
    OrPat,
    BindPat,
    WildcardPat,
    NamePat,
    LiteralPat,
    RangePat,
    TypePat,
    RecordPat,
    PatField,
    ListPat,
    RestPat,

    // Types (D.6).
    NamedType,
    TypeArgs,
    InferType,
    UnitType,
    ParenType,
    RecordType,
    TypeField,
    SpreadType,
    /// A trailing `..` in a record type: it accepts extra fields (§3.8.1).
    OpenRow,
    FnType,
    FnTypeParams,
    UnionType,
}
