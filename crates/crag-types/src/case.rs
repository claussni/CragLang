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

//! `case` checking (Implementation Plan §11.4.8): whether the arms cover
//! every value of the subject, and whether each arm matches a value no
//! earlier arm does (§7.2). Both are the usefulness test of the pattern
//! matrix from "Warnings for pattern matching" (Maranget, 2007).
//!
//! The test splits the values of a column into constructors. A type
//! pattern splits a union into its members, and a member into the
//! subtypes the column names and the rest of it, since a type may have
//! subtypes no pattern names. Literals and ranges split a discrete type
//! into intervals; literals of other types split it into their values and
//! the rest. List patterns split a list by length.

use crag_db::Db;
use crag_hir::{Body, Literal, Name, Pat, PatId, Program};

use crate::infer::{constant, fixed_scale};
use crate::relate::{declared_fields, fields_of, is_subtype};
use crate::ty::{Builtin, Ty, TyKind};

/// A pattern as the test sees it, with bindings dropped and fields by
/// name.
#[derive(Clone, Debug)]
pub(crate) enum Pattern<'db> {
    Wild,
    /// A type pattern, or with fields a record pattern. An anonymous
    /// record pattern has no type and matches the record it is checked
    /// against.
    Type {
        ty: Option<Ty<'db>>,
        fields: Option<Vec<(Name<'db>, Pattern<'db>)>>,
    },
    /// A literal or a range of a discrete type: the values `lo..=hi`, in
    /// units of the scale for a `Fixed`.
    Range {
        ty: Ty<'db>,
        lo: i128,
        hi: i128,
    },
    /// A literal of a type whose values are not counted.
    Value {
        ty: Ty<'db>,
        value: Value,
    },
    List {
        before: Vec<Pattern<'db>>,
        rest: bool,
        after: Vec<Pattern<'db>>,
    },
    Or(Vec<Pattern<'db>>),
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Value {
    Str(String),
    Bytes(Vec<u8>),
    /// By its bits; Float has no NaN and -0.0 cannot be written.
    Float(u64),
}

impl Pattern<'_> {
    fn is_wild(&self) -> bool {
        matches!(self, Pattern::Wild)
    }
}

/// Rows of patterns, one column per position in the value. A guarded arm
/// is not a row: it can fail (§7.2).
#[derive(Clone, Debug, Default)]
pub(crate) struct PatternMatrix<'db> {
    rows: Vec<Vec<Pattern<'db>>>,
}

impl<'db> PatternMatrix<'db> {
    pub(crate) fn push(&mut self, pattern: Pattern<'db>) {
        self.rows.push(vec![pattern]);
    }
}

/// A set of values of a column that every pattern either covers whole or
/// not at all.
#[derive(Clone, Debug)]
pub(crate) enum Ctor<'db> {
    /// The values of `ty` no finer type of the column names, with the
    /// fields the column's record patterns look into.
    Type {
        ty: Ty<'db>,
        fields: Vec<(Name<'db>, Ty<'db>)>,
    },
    Range {
        ty: Ty<'db>,
        lo: i128,
        hi: i128,
    },
    Value {
        ty: Ty<'db>,
        value: Value,
    },
    /// The values of `ty` that no literal of the column names.
    Other(Ty<'db>),
    /// The lists of `ty` of a length, or of at least `prefix + suffix`
    /// elements, of which the first `prefix` and the last `suffix` are
    /// looked into.
    List {
        ty: Ty<'db>,
        element: Ty<'db>,
        len: ListLen,
    },
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ListLen {
    Fixed(usize),
    AtLeast { prefix: usize, suffix: usize },
}

impl<'db> Ctor<'db> {
    fn ty(&self) -> Ty<'db> {
        match self {
            Ctor::Type { ty, .. }
            | Ctor::Range { ty, .. }
            | Ctor::Value { ty, .. }
            | Ctor::Other(ty)
            | Ctor::List { ty, .. } => *ty,
        }
    }

    /// The types of the positions inside it.
    fn arity(&self) -> Vec<Ty<'db>> {
        match self {
            Ctor::Type { fields, .. } => fields.iter().map(|(_, t)| *t).collect(),
            Ctor::List { element, len, .. } => {
                let n = match len {
                    ListLen::Fixed(n) => *n,
                    ListLen::AtLeast { prefix, suffix } => prefix + suffix,
                };
                vec![*element; n]
            }
            _ => Vec::new(),
        }
    }
}

/// A value no row matches, for the diagnostic.
#[derive(Clone, Debug)]
pub(crate) enum Witness<'db> {
    Wild,
    Ctor(Ctor<'db>, Vec<Witness<'db>>),
}

impl<'db> Witness<'db> {
    /// The value as a pattern that matches it.
    pub(crate) fn display(&self, db: &'db dyn Db) -> String {
        let Witness::Ctor(ctor, args) = self else {
            return "_".into();
        };
        let list = |args: &[Witness<'db>]| args.iter().map(|a| a.display(db)).collect::<Vec<_>>();
        match ctor {
            Ctor::Type { ty, fields } => {
                let anonymous = matches!(ty.kind(db), TyKind::Record { .. });
                if args.iter().all(|a| matches!(a, Witness::Wild)) {
                    return if anonymous {
                        "_".into()
                    } else {
                        ty.display(db)
                    };
                }
                let fields: Vec<String> = fields
                    .iter()
                    .zip(args)
                    .map(|((n, _), a)| format!("{}: {}", n.text(db), a.display(db)))
                    .collect();
                let name = if anonymous {
                    String::new()
                } else {
                    ty.display(db)
                };
                format!("{name}({})", fields.join(", "))
            }
            Ctor::Range { ty, lo, hi } if lo == hi => value_text(db, *ty, *lo),
            Ctor::Range { ty, lo, hi } => {
                format!("{}..{}", value_text(db, *ty, *lo), value_text(db, *ty, *hi))
            }
            Ctor::Value { value, .. } => match value {
                Value::Str(s) => format!(
                    "\"{}\"",
                    s.chars().map(|c| escape(c, '"')).collect::<String>()
                ),
                Value::Bytes(b) => {
                    let text: String = b
                        .iter()
                        .map(|&b| match b {
                            0x20..0x7f => escape(char::from(b), '"'),
                            _ => format!("\\x{b:02x}"),
                        })
                        .collect();
                    format!("b\"{text}\"")
                }
                Value::Float(bits) => format!("{:?}", f64::from_bits(*bits)),
            },
            Ctor::Other(ty) => ty.display(db),
            Ctor::List { len, .. } => {
                let mut items = list(args);
                if let ListLen::AtLeast { prefix, .. } = len {
                    items.insert(*prefix, "..".into());
                }
                format!("[{}]", items.join(", "))
            }
        }
    }
}

/// A value of a discrete type as source writes it.
fn value_text(db: &dyn Db, ty: Ty<'_>, value: i128) -> String {
    match ty.as_builtin(db) {
        Some((Builtin::CodePoint, _)) => match u32::try_from(value).ok().and_then(char::from_u32) {
            Some(c) => format!("'{}'", escape(c, '\'')),
            None => value.to_string(),
        },
        Some((Builtin::Fixed(scale), _)) if scale > 0 => {
            let unit = 10i128.pow(scale);
            let sign = if value < 0 { "-" } else { "" };
            let (whole, fraction) = (value.abs() / unit, value.abs() % unit);
            format!("{sign}{whole}.{fraction:0width$}", width = scale as usize)
        }
        Some((builtin, _)) => match builtin.int_range() {
            Some((least, _)) if value == least => format!("{}.min", builtin.name()),
            Some((_, greatest)) if value == greatest => format!("{}.max", builtin.name()),
            _ => value.to_string(),
        },
        None => value.to_string(),
    }
}

/// A character inside a literal quoted with `quote` (§2.6).
fn escape(c: char, quote: char) -> String {
    match c {
        '\n' => "\\n".into(),
        '\t' => "\\t".into(),
        '\r' => "\\r".into(),
        '\0' => "\\0".into(),
        '\\' => "\\\\".into(),
        '{' if quote == '"' => "{{".into(),
        '}' if quote == '"' => "}}".into(),
        c if c == quote => format!("\\{c}"),
        c if c.is_control() => format!("\\u{{{:x}}}", u32::from(c)),
        c => c.into(),
    }
}

/// The values of a discrete type, as intervals.
fn domain(db: &dyn Db, ty: Ty<'_>) -> Option<Vec<(i128, i128)>> {
    let (builtin, _) = ty.as_builtin(db)?;
    match builtin {
        Builtin::CodePoint => Some(vec![(0, 0xD7FF), (0xE000, 0x10FFFF)]),
        Builtin::Fixed(_) => Some(vec![(i64::MIN.into(), i64::MAX.into())]),
        _ => builtin.int_range().map(|range| vec![range]),
    }
}

pub(crate) struct Checker<'db> {
    db: &'db dyn Db,
    program: Program,
}

impl<'db> Checker<'db> {
    pub(crate) fn new(db: &'db dyn Db, program: Program) -> Self {
        Checker { db, program }
    }

    fn fits(&self, s: Ty<'db>, t: Ty<'db>) -> bool {
        is_subtype(self.db, self.program, s, t)
    }

    /// The pattern of a body for the test, given the types inference gave
    /// the patterns. None when a pattern is missing or did not type, so
    /// that a broken pattern raises no further errors.
    pub(crate) fn lower(
        &self,
        body: &Body<'db>,
        pats: &[Option<Ty<'db>>],
        id: PatId,
    ) -> Option<Pattern<'db>> {
        let db = self.db;
        let ty = pats.get(id.index()).copied().flatten()?;
        if ty.is_error(db) {
            return None;
        }
        Some(match body.pat(id) {
            Pat::Missing => return None,
            Pat::Wildcard | Pat::Bind { sub: None, .. } => Pattern::Wild,
            Pat::Bind { sub: Some(sub), .. } => self.lower(body, pats, *sub)?,
            Pat::Type(_) => Pattern::Type {
                ty: Some(ty),
                fields: None,
            },
            Pat::Record {
                ty: written,
                fields,
            } => {
                let names: Vec<Name<'db>> = match declared_fields(db, self.program, ty) {
                    Some(declared) => declared.into_iter().map(|(n, ..)| n).collect(),
                    None => fields_of(db, self.program, ty)?
                        .into_iter()
                        .map(|(n, _)| n)
                        .collect(),
                };
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let name = field.name.or_else(|| names.get(i).copied())?;
                        Some((name, self.lower(body, pats, field.pat)?))
                    })
                    .collect::<Option<Vec<_>>>()?;
                Pattern::Type {
                    ty: written.is_some().then_some(ty),
                    fields: Some(fields),
                }
            }
            Pat::List {
                before,
                rest,
                after,
            } => {
                let lower = |ids: &[PatId]| {
                    ids.iter()
                        .map(|&p| self.lower(body, pats, p))
                        .collect::<Option<Vec<_>>>()
                };
                Pattern::List {
                    before: lower(before)?,
                    rest: rest.is_some(),
                    after: lower(after)?,
                }
            }
            Pat::Literal(literal) => self.literal(ty, literal, literal)?,
            Pat::Range { start, end } => self.literal(ty, start, end)?,
            Pat::Or(alternatives) => Pattern::Or(
                alternatives
                    .iter()
                    .map(|&p| self.lower(body, pats, p))
                    .collect::<Option<Vec<_>>>()?,
            ),
        })
    }

    fn literal(&self, ty: Ty<'db>, start: &Literal, end: &Literal) -> Option<Pattern<'db>> {
        if domain(self.db, ty).is_some() {
            let scale = fixed_scale(self.db, ty);
            let (lo, hi) = (constant(start, scale)?, constant(end, scale)?);
            return Some(Pattern::Range { ty, lo, hi });
        }
        let value = match start {
            Literal::Str(s) => Value::Str(s.clone()),
            Literal::Bytes(b) => Value::Bytes(b.clone()),
            Literal::Float(text) => Value::Float(text.parse::<f64>().ok()?.to_bits()),
            Literal::Int(n) => Value::Float((*n as f64).to_bits()),
            Literal::CodePoint(_) => return None,
        };
        Some(Pattern::Value { ty, value })
    }

    /// Whether `pattern` matches a value of `ty` that no row of the matrix
    /// does.
    pub(crate) fn is_useful(
        &self,
        matrix: &PatternMatrix<'db>,
        pattern: &Pattern<'db>,
        ty: Ty<'db>,
    ) -> bool {
        self.useful(matrix.rows.clone(), vec![pattern.clone()], &[ty])
            .is_some()
    }

    /// A value of `ty` that no row of the matrix matches.
    pub(crate) fn missing_example(
        &self,
        matrix: &PatternMatrix<'db>,
        ty: Ty<'db>,
    ) -> Option<Witness<'db>> {
        let mut witness = self.useful(matrix.rows.clone(), vec![Pattern::Wild], &[ty])?;
        // With no rows, a member of the subject says more than `_`.
        match (witness.pop()?, matrix.rows.is_empty()) {
            (Witness::Wild, true) => self.split(ty, &[]).into_iter().next().map(|c| {
                let args = vec![Witness::Wild; c.arity().len()];
                Witness::Ctor(c, args)
            }),
            (witness, _) => Some(witness),
        }
    }

    /// The core recursion: a value that `q` matches and no row does, one
    /// witness per column.
    fn useful(
        &self,
        rows: Vec<Vec<Pattern<'db>>>,
        q: Vec<Pattern<'db>>,
        tys: &[Ty<'db>],
    ) -> Option<Vec<Witness<'db>>> {
        let Some(head) = q.first() else {
            return rows.is_empty().then(Vec::new);
        };
        if let Pattern::Or(alternatives) = head {
            return alternatives.iter().find_map(|alt| {
                let mut q = q.clone();
                q[0] = alt.clone();
                self.useful(rows.clone(), q, tys)
            });
        }
        let rows = expand(rows);
        let ty = tys[0];
        if head.is_wild() && rows.iter().all(|r| r[0].is_wild()) && !ty.is_never(self.db) {
            // Every constructor is the same here; the column is dropped.
            let rest = rows.into_iter().map(|r| r[1..].to_vec()).collect();
            let mut witness = self.useful(rest, q[1..].to_vec(), &tys[1..])?;
            witness.insert(0, Witness::Wild);
            return Some(witness);
        }
        let heads: Vec<&Pattern<'db>> = rows.iter().map(|r| &r[0]).chain([head]).collect();
        for ctor in self.split(ty, &heads) {
            let Some(mut inner) = self.specialize(head, &ctor) else {
                continue;
            };
            inner.extend_from_slice(&q[1..]);
            let specialized = rows
                .iter()
                .filter_map(|r| {
                    let mut row = self.specialize(&r[0], &ctor)?;
                    row.extend_from_slice(&r[1..]);
                    Some(row)
                })
                .collect();
            let mut inner_tys = ctor.arity();
            let arity = inner_tys.len();
            inner_tys.extend_from_slice(&tys[1..]);
            if let Some(mut witness) = self.useful(specialized, inner, &inner_tys) {
                let args = witness.drain(..arity).collect();
                witness.insert(0, Witness::Ctor(ctor, args));
                return Some(witness);
            }
        }
        None
    }

    /// The constructors of a column of type `ty` whose rows begin with
    /// `heads`.
    fn split(&self, ty: Ty<'db>, heads: &[&Pattern<'db>]) -> Vec<Ctor<'db>> {
        let db = self.db;
        let members = ty.members(db);
        let mut atoms = members.clone();
        for head in heads {
            let Pattern::Type { ty: Some(p), .. } = head else {
                continue;
            };
            for p in p.members(db) {
                let finer = members.iter().any(|&m| self.fits(p, m) && !self.fits(m, p));
                if finer && !atoms.contains(&p) {
                    atoms.push(p);
                }
            }
        }
        let records = heads.iter().any(|h| {
            matches!(
                h,
                Pattern::Type {
                    fields: Some(_),
                    ..
                }
            )
        });
        let lists = heads.iter().any(|h| matches!(h, Pattern::List { .. }));
        let mut ctors = Vec::new();
        for atom in atoms {
            let intervals: Vec<(i128, i128)> = heads
                .iter()
                .filter_map(|h| match h {
                    Pattern::Range { ty, lo, hi } if *ty == atom => Some((*lo, *hi)),
                    _ => None,
                })
                .collect();
            let mut values: Vec<&Value> = Vec::new();
            for head in heads {
                if let Pattern::Value { ty, value } = head
                    && *ty == atom
                    && !values.contains(&value)
                {
                    values.push(value);
                }
            }
            let list = match atom.as_builtin(db) {
                Some((Builtin::List, [element])) if lists => Some(*element),
                _ => None,
            };
            if let (false, Some(domain)) = (intervals.is_empty(), domain(db, atom)) {
                ctors.extend(
                    pieces(&domain, &intervals)
                        .into_iter()
                        .map(|(lo, hi)| Ctor::Range { ty: atom, lo, hi }),
                );
            } else if !values.is_empty() {
                ctors.extend(values.into_iter().map(|v| Ctor::Value {
                    ty: atom,
                    value: v.clone(),
                }));
                ctors.push(Ctor::Other(atom));
            } else if let Some(element) = list {
                ctors.extend(list_lengths(heads).into_iter().map(|len| Ctor::List {
                    ty: atom,
                    element,
                    len,
                }));
            } else {
                let fields = match records {
                    true => fields_of(db, self.program, atom).unwrap_or_default(),
                    false => Vec::new(),
                };
                ctors.push(Ctor::Type { ty: atom, fields });
            }
        }
        ctors
    }

    /// The patterns inside `pattern` for the values of `ctor`, or none
    /// when it matches none of them.
    fn specialize(&self, pattern: &Pattern<'db>, ctor: &Ctor<'db>) -> Option<Vec<Pattern<'db>>> {
        let wild = || vec![Pattern::Wild; ctor.arity().len()];
        match (pattern, ctor) {
            (Pattern::Wild, _) => Some(wild()),
            (Pattern::Type { ty, fields }, _) => {
                if ty.is_some_and(|p| !self.fits(ctor.ty(), p)) {
                    return None;
                }
                match (fields, ctor) {
                    (Some(fields), Ctor::Type { fields: names, .. }) => Some(
                        names
                            .iter()
                            .map(|(name, _)| {
                                fields
                                    .iter()
                                    .find(|(n, _)| n == name)
                                    .map_or(Pattern::Wild, |(_, p)| p.clone())
                            })
                            .collect(),
                    ),
                    _ => Some(wild()),
                }
            }
            (
                Pattern::Range { ty, lo, hi },
                Ctor::Range {
                    ty: t,
                    lo: l,
                    hi: h,
                },
            ) => (ty == t && lo <= l && h <= hi).then(Vec::new),
            (Pattern::Value { ty, value }, Ctor::Value { ty: t, value: v }) => {
                (ty == t && value == v).then(Vec::new)
            }
            (
                Pattern::List {
                    before,
                    rest,
                    after,
                },
                Ctor::List { len, .. },
            ) => {
                let fixed = before.len() + after.len();
                let gap = match (len, rest) {
                    (ListLen::Fixed(n), false) if *n == fixed => 0,
                    (ListLen::Fixed(n), true) if *n >= fixed => n - fixed,
                    (ListLen::AtLeast { prefix, suffix }, true) => prefix + suffix - fixed,
                    _ => return None,
                };
                let mut inner = before.clone();
                inner.extend(vec![Pattern::Wild; gap]);
                inner.extend(after.iter().cloned());
                Some(inner)
            }
            _ => None,
        }
    }
}

/// Rows with an or-pattern at their head, one row per alternative.
fn expand<'db>(rows: Vec<Vec<Pattern<'db>>>) -> Vec<Vec<Pattern<'db>>> {
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        match &row[0] {
            Pattern::Or(alternatives) => {
                let alternatives: Vec<Vec<Pattern<'db>>> = alternatives
                    .iter()
                    .map(|alt| {
                        let mut r = row.clone();
                        r[0] = alt.clone();
                        r
                    })
                    .collect();
                out.extend(expand(alternatives));
            }
            _ => out.push(row),
        }
    }
    out
}

/// The domain cut where any of the intervals begins or ends, so that each
/// piece lies inside or outside each interval.
fn pieces(domain: &[(i128, i128)], intervals: &[(i128, i128)]) -> Vec<(i128, i128)> {
    let mut cuts: Vec<i128> = intervals
        .iter()
        .flat_map(|&(lo, hi)| [lo, hi + 1])
        .collect();
    cuts.sort_unstable();
    cuts.dedup();
    let mut out = Vec::new();
    for &(lo, hi) in domain {
        let mut start = lo;
        for &cut in &cuts {
            if cut > start && cut <= hi {
                out.push((start, cut - 1));
                start = cut;
            }
        }
        out.push((start, hi));
    }
    out
}

/// The lengths list patterns tell apart: each length up to the longest
/// they name, and every longer list.
fn list_lengths(heads: &[&Pattern<'_>]) -> Vec<ListLen> {
    let (mut longest, mut prefix, mut suffix) = (0, 0, 0);
    for head in heads {
        if let Pattern::List {
            before,
            rest,
            after,
        } = head
        {
            if *rest {
                prefix = prefix.max(before.len());
                suffix = suffix.max(after.len());
            } else {
                longest = longest.max(before.len());
            }
        }
    }
    let least = (longest + 1).max(prefix + suffix);
    let mut lengths: Vec<ListLen> = (0..least).map(ListLen::Fixed).collect();
    lengths.push(ListLen::AtLeast {
        prefix: least - suffix,
        suffix,
    });
    lengths
}
