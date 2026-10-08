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

//! Type terms (Implementation Plan §11.4.7). Types are interned, so two
//! equal types are one id and compare as integers.

use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{ItemId, Name};

#[crag_db::interned(debug)]
pub struct Ty<'db> {
    #[returns(ref)]
    pub kind: TyKind<'db>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum TyKind<'db> {
    /// The type of what failed to type; it fits everything, so one error
    /// is reported once.
    Error,
    /// A compiler- or runtime-owned type (§19.1).
    Builtin(Builtin, Vec<Ty<'db>>),
    /// A declared record or tag type, by the declaration that stands for
    /// its identity (§3.3).
    Named(ItemId<'db>, Vec<Ty<'db>>),
    /// An anonymous record, its fields sorted by name (§3.4); `()` has
    /// none.
    Record {
        fields: Vec<(Name<'db>, Ty<'db>)>,
        /// A trailing `..` (§3.8.1).
        open: bool,
    },
    Fn {
        params: Vec<Ty<'db>>,
        result: Ty<'db>,
    },
    /// At least two members, none containing another, in a fixed order; no
    /// members is `Never` (§3.6.3).
    Union(Vec<Ty<'db>>),
    /// A type parameter of a generic function or type, by its owner and
    /// index, opaque inside it. Tests and the local functions in them have
    /// no owner.
    Param(Option<ItemId<'db>>, u32, Name<'db>),
}

/// The types only the compiler and the runtime can define (§19.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Builtin {
    Int,
    Int8,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Float,
    /// `Fixed[S]`, with `S` fractional digits.
    Fixed(u32),
    Str,
    CodePoint,
    Bytes,
    List,
    Map,
    Set,
    Grid,
    Ref,
    Lazy,
}

impl Builtin {
    /// The builtin a prelude declaration of this name stands for, and the
    /// number of type arguments it takes. `Fixed` takes its scale.
    pub fn from_name(name: &str) -> Option<(Builtin, usize)> {
        Some(match name {
            "Int" => (Builtin::Int, 0),
            "Int8" => (Builtin::Int8, 0),
            "Int16" => (Builtin::Int16, 0),
            "Int32" => (Builtin::Int32, 0),
            "UInt8" => (Builtin::UInt8, 0),
            "UInt16" => (Builtin::UInt16, 0),
            "UInt32" => (Builtin::UInt32, 0),
            "UInt64" => (Builtin::UInt64, 0),
            "Float" => (Builtin::Float, 0),
            "Fixed" => (Builtin::Fixed(0), 1),
            "Str" => (Builtin::Str, 0),
            "CodePoint" => (Builtin::CodePoint, 0),
            "Bytes" => (Builtin::Bytes, 0),
            "List" => (Builtin::List, 1),
            "Map" => (Builtin::Map, 2),
            "Set" => (Builtin::Set, 1),
            "Grid" => (Builtin::Grid, 1),
            "Ref" => (Builtin::Ref, 1),
            "Lazy" => (Builtin::Lazy, 1),
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            Builtin::Int => "Int",
            Builtin::Int8 => "Int8",
            Builtin::Int16 => "Int16",
            Builtin::Int32 => "Int32",
            Builtin::UInt8 => "UInt8",
            Builtin::UInt16 => "UInt16",
            Builtin::UInt32 => "UInt32",
            Builtin::UInt64 => "UInt64",
            Builtin::Float => "Float",
            Builtin::Fixed(_) => "Fixed",
            Builtin::Str => "Str",
            Builtin::CodePoint => "CodePoint",
            Builtin::Bytes => "Bytes",
            Builtin::List => "List",
            Builtin::Map => "Map",
            Builtin::Set => "Set",
            Builtin::Grid => "Grid",
            Builtin::Ref => "Ref",
            Builtin::Lazy => "Lazy",
        }
    }

    /// The range of an integer type, as `(least, greatest)`.
    pub fn int_range(self) -> Option<(i128, i128)> {
        Some(match self {
            Builtin::Int => (i64::MIN.into(), i64::MAX.into()),
            Builtin::Int8 => (i8::MIN.into(), i8::MAX.into()),
            Builtin::Int16 => (i16::MIN.into(), i16::MAX.into()),
            Builtin::Int32 => (i32::MIN.into(), i32::MAX.into()),
            Builtin::UInt8 => (0, u8::MAX.into()),
            Builtin::UInt16 => (0, u16::MAX.into()),
            Builtin::UInt32 => (0, u32::MAX.into()),
            Builtin::UInt64 => (0, u64::MAX.into()),
            _ => return None,
        })
    }
}

impl<'db> Ty<'db> {
    pub fn error(db: &'db dyn Db) -> Ty<'db> {
        Ty::new(db, TyKind::Error)
    }

    pub fn builtin(db: &'db dyn Db, builtin: Builtin) -> Ty<'db> {
        Ty::new(db, TyKind::Builtin(builtin, Vec::new()))
    }

    pub fn unit(db: &'db dyn Db) -> Ty<'db> {
        Ty::new(
            db,
            TyKind::Record {
                fields: Vec::new(),
                open: false,
            },
        )
    }

    pub fn never(db: &'db dyn Db) -> Ty<'db> {
        Ty::new(db, TyKind::Union(Vec::new()))
    }

    /// An anonymous record, its fields put in order.
    pub fn record(db: &'db dyn Db, mut fields: Vec<(Name<'db>, Ty<'db>)>, open: bool) -> Ty<'db> {
        fields.sort_by(|(a, _), (b, _)| a.text(db).cmp(b.text(db)));
        Ty::new(db, TyKind::Record { fields, open })
    }

    pub fn is_error(self, db: &'db dyn Db) -> bool {
        matches!(self.kind(db), TyKind::Error)
    }

    pub fn is_never(self, db: &'db dyn Db) -> bool {
        matches!(self.kind(db), TyKind::Union(members) if members.is_empty())
    }

    /// The builtin and its arguments, if this is one.
    pub fn as_builtin(self, db: &'db dyn Db) -> Option<(Builtin, &'db [Ty<'db>])> {
        match self.kind(db) {
            TyKind::Builtin(b, args) => Some((*b, args)),
            _ => None,
        }
    }

    /// The members of a union, or the type itself.
    pub fn members(self, db: &'db dyn Db) -> Vec<Ty<'db>> {
        match self.kind(db) {
            TyKind::Union(members) => members.clone(),
            _ => vec![self],
        }
    }

    /// The order members of a union are kept in.
    pub(crate) fn order(self) -> impl Ord {
        self.as_id()
    }

    /// The type as source writes it.
    pub fn display(self, db: &'db dyn Db) -> String {
        let list = |types: &[Ty<'db>]| {
            types
                .iter()
                .map(|t| t.display(db))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let args = |types: &[Ty<'db>]| {
            if types.is_empty() {
                String::new()
            } else {
                format!("[{}]", list(types))
            }
        };
        match self.kind(db) {
            TyKind::Error => "_".into(),
            TyKind::Builtin(Builtin::Fixed(scale), _) => format!("Fixed[{scale}]"),
            TyKind::Builtin(b, types) => format!("{}{}", b.name(), args(types)),
            TyKind::Named(item, types) => format!("{}{}", item.name(db).text(db), args(types)),
            TyKind::Record { fields, open } => {
                let mut parts: Vec<String> = fields
                    .iter()
                    .map(|(n, t)| format!("{}: {}", n.text(db), t.display(db)))
                    .collect();
                if *open {
                    parts.push("..".into());
                }
                format!("({})", parts.join(", "))
            }
            TyKind::Fn { params, result } => {
                format!("({}) -> {}", list(params), result.display(db))
            }
            TyKind::Union(members) if members.is_empty() => "Never".into(),
            // Members by their text, which does not depend on the order
            // types were interned in.
            TyKind::Union(members) => {
                let mut texts: Vec<String> = members
                    .iter()
                    .map(|m| match m.kind(db) {
                        TyKind::Fn { .. } => format!("({})", m.display(db)),
                        _ => m.display(db),
                    })
                    .collect();
                texts.sort();
                texts.join(" | ")
            }
            TyKind::Param(_, _, name) => name.text(db).clone(),
        }
    }
}
