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

//! The conditions of a type on a value known where it is written
//! (Specification §3.10.1).
//!
//! A literal may stand where a conditioned alias is expected once its
//! conditions hold for it, and a record built of literals that fails a
//! condition of its type is a compile error. The conditions are evaluated
//! here as far as they compare, combine and compute with the prelude's
//! operators on `this`, the fields and literals; a condition beyond that
//! cannot be decided, and the value must be converted or is checked when
//! it is built.

use crag_hir::{Expr, ExprId, ItemId, Literal, Owner, PRELUDE, Program, hir_body};

use crate::result::Callee;

/// A value the evaluation knows.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Known {
    Int(i128),
    Float(f64),
    Text(String),
    Bool(bool),
    /// A record with the fields known, by name.
    Record(Vec<(String, Known)>),
}

/// How a literal's conditions came out: all hold, one fails, by its label,
/// or one cannot be decided here.
pub(crate) enum Verdict {
    Holds,
    Fails(String),
    Undecided(String),
}

/// The value of a literal, as `negative` signs it.
pub(crate) fn known(literal: &Literal, negative: bool) -> Option<Known> {
    let sign = if negative { -1.0 } else { 1.0 };
    Some(match literal {
        Literal::Int(n) => {
            let n = i128::try_from(*n).ok()?;
            Known::Int(if negative { -n } else { n })
        }
        Literal::Float(text) => Known::Float(sign * text.parse::<f64>().ok()?),
        Literal::Str(s) => Known::Text(s.clone()),
        _ => return None,
    })
}

/// Whether the conditions of the type `item` hold for `value`.
pub(crate) fn verdict(
    db: &dyn crag_db::Db,
    program: Program,
    item: ItemId<'_>,
    value: &Known,
) -> Verdict {
    let body = hir_body(db, program, Owner::Item(item));
    let Some(decl) = body.type_decl.as_ref() else {
        return Verdict::Holds;
    };
    let types = crate::body_types(db, program, Owner::Item(item));
    let eval = Eval {
        db,
        body,
        types,
        this: decl.this,
        fields: &decl.field_bindings,
        value,
    };
    for condition in &decl.conditions {
        match eval.expr(condition.value) {
            Some(Known::Bool(true)) => {}
            Some(Known::Bool(false)) => return Verdict::Fails(condition.label(db)),
            _ => return Verdict::Undecided(condition.label(db)),
        }
    }
    Verdict::Holds
}

struct Eval<'a, 'db> {
    db: &'db dyn crag_db::Db,
    body: &'a crag_hir::Body<'db>,
    types: &'a crate::InferenceResult<'db>,
    this: Option<crag_hir::BindingId>,
    fields: &'a [(crag_hir::Name<'db>, crag_hir::BindingId)],
    value: &'a Known,
}

impl Eval<'_, '_> {
    fn expr(&self, id: ExprId) -> Option<Known> {
        let bool_of = |k: Option<Known>| match k {
            Some(Known::Bool(b)) => Some(b),
            _ => None,
        };
        match self.body.expr(id) {
            Expr::Literal(literal) => known(literal, self.body.is_negative(id)),
            Expr::Str(parts) => match parts.as_slice() {
                [crag_hir::StrPart::Text(text)] => Some(Known::Text(text.clone())),
                [] => Some(Known::Text(String::new())),
                _ => None,
            },
            Expr::Name { local: Some(b), .. } if Some(*b) == self.this => Some(self.value.clone()),
            Expr::Name { local: Some(b), .. } => {
                let (name, _) = self.fields.iter().find(|(_, f)| f == b)?;
                self.field(self.value, name.text(self.db))
            }
            Expr::Field {
                receiver,
                name,
                optional: false,
                ..
            } => self.field(&self.expr(*receiver)?, name.text(self.db)),
            Expr::And(a, b) => Some(Known::Bool(
                bool_of(self.expr(*a))? && bool_of(self.expr(*b))?,
            )),
            Expr::Or(a, b) => Some(Known::Bool(
                bool_of(self.expr(*a))? || bool_of(self.expr(*b))?,
            )),
            Expr::Not(a) => Some(Known::Bool(!bool_of(self.expr(*a))?)),
            Expr::Call {
                args, fields: None, ..
            } => {
                let Some(Callee::Function(f)) = self.types.callee(id) else {
                    return None;
                };
                if f.module(self.db).path(self.db) != PRELUDE {
                    return None;
                }
                let values: Vec<Known> =
                    args.iter().map(|&a| self.expr(a)).collect::<Option<_>>()?;
                operator(f.name(self.db).text(self.db), &values)
            }
            _ => None,
        }
    }

    fn field(&self, value: &Known, name: &str) -> Option<Known> {
        match value {
            Known::Record(fields) => fields
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, k)| k.clone()),
            _ => None,
        }
    }
}

/// A prelude operator on known values.
fn operator(name: &str, values: &[Known]) -> Option<Known> {
    use Known::*;
    let ordering = |a: &Known, b: &Known| match (a, b) {
        (Int(a), Int(b)) => a.partial_cmp(b),
        (Float(a), Float(b)) => a.partial_cmp(b),
        (Int(a), Float(b)) => (*a as f64).partial_cmp(b),
        (Float(a), Int(b)) => a.partial_cmp(&(*b as f64)),
        (Text(a), Text(b)) => a.partial_cmp(b),
        _ => None,
    };
    Some(match (name, values) {
        ("negate", [Int(a)]) => Int(-a),
        ("negate", [Float(a)]) => Float(-a),
        ("equals", [a, b]) => Bool(ordering(a, b)? == std::cmp::Ordering::Equal),
        ("lessThan", [a, b]) => Bool(ordering(a, b)?.is_lt()),
        ("lessOrEqual", [a, b]) => Bool(ordering(a, b)?.is_le()),
        ("greaterThan", [a, b]) => Bool(ordering(a, b)?.is_gt()),
        ("greaterOrEqual", [a, b]) => Bool(ordering(a, b)?.is_ge()),
        ("add", [Int(a), Int(b)]) => Int(a.checked_add(*b)?),
        ("subtract", [Int(a), Int(b)]) => Int(a.checked_sub(*b)?),
        ("multiply", [Int(a), Int(b)]) => Int(a.checked_mul(*b)?),
        ("divide", [Int(a), Int(b)]) => Int(a.checked_div(*b)?),
        ("remainder", [Int(a), Int(b)]) => Int(a.checked_rem(*b)?),
        ("add", [Float(a), Float(b)]) => Float(a + b),
        ("subtract", [Float(a), Float(b)]) => Float(a - b),
        ("multiply", [Float(a), Float(b)]) => Float(a * b),
        ("divide", [Float(a), Float(b)]) if *b != 0.0 => Float(a / b),
        _ => return None,
    })
}
