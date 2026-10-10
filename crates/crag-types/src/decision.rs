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

//! Decision trees for `case` (Implementation Plan §11.4.9), after
//! "Compiling pattern matching to good decision trees" (Maranget, 2008).
//!
//! The tree is built from the pattern matrix of `case` checking: a node
//! tests one position of the value, chosen as the first position the
//! first row still looks into, so every position is tested at most once
//! on a path. The values of a position split into the same constructors
//! the usefulness test uses. A position of several types is first
//! switched on its runtime type; one of a single type is then tested by
//! value, by length, or not at all when it is a record whose fields are
//! looked into.

use crag_db::Db;
use crag_hir::{BindingId, Name, Owner, PatId, Program, hir_body};

use crate::body_types;
use crate::case::{Checker, Ctor, ListLen, Pattern, Value, domain};
use crate::ty::{Builtin, Ty};

/// A position in the value a `case` looks at: the steps from the value to
/// a part of it.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct Position<'db>(pub Vec<Step<'db>>);

impl<'db> Position<'db> {
    fn with(&self, step: Step<'db>) -> Position<'db> {
        let mut steps = self.0.clone();
        steps.push(step);
        Position(steps)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Step<'db> {
    /// The value as a member of its union, or as a subtype of its type,
    /// which a test has established.
    As(Ty<'db>),
    Field(Name<'db>),
    /// An element of a list by its index from the start, or from the end:
    /// `ElemBack(0)` is the last element.
    Elem(u32),
    ElemBack(u32),
    /// The elements of a list without its first `front` and last `back`:
    /// what the rest of a list pattern binds. Always the last step.
    Slice {
        front: u32,
        back: u32,
    },
}

/// The bindings of an arm, each at the position of its value.
pub type Bindings<'db> = Vec<(BindingId, Position<'db>)>;

#[derive(Clone, Debug, PartialEq)]
pub enum DecisionTree<'db> {
    /// No arm matches.
    Fail,
    /// The arm matches.
    Leaf { arm: usize, bindings: Bindings<'db> },
    /// The arm matches if its guard holds; otherwise `otherwise` decides.
    Guard {
        arm: usize,
        bindings: Bindings<'db>,
        otherwise: Box<DecisionTree<'db>>,
    },
    /// The first case whose type the value at the position has. A finer
    /// type comes before the types it is part of. Without a default, the
    /// cases cover every value.
    Switch {
        position: Position<'db>,
        cases: Vec<(Ty<'db>, DecisionTree<'db>)>,
        default: Option<Box<DecisionTree<'db>>>,
    },
    /// The interval of a discrete type the value lies in, from `lo` to
    /// `hi`, in units of the scale for a `Fixed`; an end the type's values
    /// reach is none.
    Ranges {
        position: Position<'db>,
        ty: Ty<'db>,
        cases: Vec<(Option<i128>, Option<i128>, DecisionTree<'db>)>,
        default: Option<Box<DecisionTree<'db>>>,
    },
    /// The literal the value equals.
    Values {
        position: Position<'db>,
        ty: Ty<'db>,
        cases: Vec<(Value, DecisionTree<'db>)>,
        default: Box<DecisionTree<'db>>,
    },
    /// The length of the list.
    Length {
        position: Position<'db>,
        cases: Vec<(ListLen, DecisionTree<'db>)>,
        default: Option<Box<DecisionTree<'db>>>,
    },
}

/// The decision tree of patterns of a body matched against a value of
/// `subject`, one arm per pattern, with whether the arm has a guard. None
/// when a pattern did not type.
pub fn decision_tree<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    subject: Ty<'db>,
    arms: &[(PatId, bool)],
) -> Option<DecisionTree<'db>> {
    let pats = &body_types(db, program, owner).pats;
    decision_tree_with(db, program, owner, pats, subject, arms)
}

/// The decision tree with the patterns of the body typed by `pats`, one
/// type per pattern: those of an instance of a generic function, whose
/// type parameters are replaced (§11.5.10).
pub fn decision_tree_with<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    pats: &[Option<Ty<'db>>],
    subject: Ty<'db>,
    arms: &[(PatId, bool)],
) -> Option<DecisionTree<'db>> {
    let body = hir_body(db, program, owner);
    let checker = Checker::new(db, program);
    let mut rows = Vec::new();
    for (arm, &(pat, _)) in arms.iter().enumerate() {
        rows.push(Row {
            pats: vec![checker.lower(body, pats, pat)?],
            bindings: Vec::new(),
            arm,
        });
    }
    let columns = vec![Column {
        position: Position::default(),
        ty: subject,
    }];
    let guarded: Vec<bool> = arms.iter().map(|&(_, g)| g).collect();
    Some(checker.tree(rows, columns, &guarded))
}

#[derive(Clone, Debug)]
struct Row<'db> {
    pats: Vec<Pattern<'db>>,
    bindings: Bindings<'db>,
    arm: usize,
}

#[derive(Clone, Debug)]
struct Column<'db> {
    position: Position<'db>,
    ty: Ty<'db>,
}

impl<'db> Checker<'db> {
    fn tree(
        &self,
        rows: Vec<Row<'db>>,
        cols: Vec<Column<'db>>,
        guarded: &[bool],
    ) -> DecisionTree<'db> {
        let mut normal = Vec::with_capacity(rows.len());
        for row in rows {
            normalize(row, &cols, &mut normal);
        }
        let rows = normal;
        let Some(first) = rows.first() else {
            return DecisionTree::Fail;
        };
        let Some(i) = first.pats.iter().position(|p| !p.is_wild()) else {
            let (arm, bindings) = (first.arm, first.bindings.clone());
            if !guarded[arm] {
                return DecisionTree::Leaf { arm, bindings };
            }
            let otherwise = Box::new(self.tree(rows[1..].to_vec(), cols, guarded));
            return DecisionTree::Guard {
                arm,
                bindings,
                otherwise,
            };
        };
        let column = cols[i].clone();
        let heads: Vec<&Pattern<'db>> = rows.iter().map(|r| &r.pats[i]).collect();
        let atoms = self.atoms(column.ty, &heads);
        if atoms.len() > 1 {
            return self.switch(rows, cols, i, atoms, guarded);
        }
        let ctors = self.split(column.ty, &heads);
        let named = |ctor: &Ctor<'db>| {
            rows.iter()
                .any(|r| !r.pats[i].is_wild() && self.specialize(&r.pats[i], ctor).is_some())
        };
        let inner = |ctor: &Ctor<'db>| {
            let (rows, cols) = self.specialize_rows(&rows, &cols, i, ctor);
            self.tree(rows, cols, guarded)
        };
        let default = || {
            let mut cols = cols.clone();
            cols.remove(i);
            let rows = rows
                .iter()
                .filter(|r| r.pats[i].is_wild())
                .map(|r| {
                    let mut r = r.clone();
                    r.pats.remove(i);
                    r
                })
                .collect();
            self.tree(rows, cols, guarded)
        };
        let position = column.position.clone();
        match ctors.first() {
            None => DecisionTree::Fail,
            Some(only) if ctors.len() == 1 => inner(only),
            Some(Ctor::Range { .. }) => {
                let domain = domain(self.db, column.ty).unwrap_or_default();
                let least = domain.first().map(|d| d.0);
                let greatest = domain.last().map(|d| d.1);
                let mut cases = Vec::new();
                for ctor in ctors.iter().filter(|c| named(c)) {
                    let Ctor::Range { lo, hi, .. } = ctor else {
                        continue;
                    };
                    let lo = (Some(*lo) != least).then_some(*lo);
                    let hi = (Some(*hi) != greatest).then_some(*hi);
                    cases.push((lo, hi, inner(ctor)));
                }
                let complete = cases.len() == ctors.len();
                DecisionTree::Ranges {
                    position,
                    ty: column.ty,
                    cases,
                    default: (!complete).then(|| Box::new(default())),
                }
            }
            Some(Ctor::Value { .. } | Ctor::Other(_)) => {
                let cases = ctors
                    .iter()
                    .filter_map(|ctor| match ctor {
                        Ctor::Value { value, .. } => Some((value.clone(), inner(ctor))),
                        _ => None,
                    })
                    .collect();
                DecisionTree::Values {
                    position,
                    ty: column.ty,
                    cases,
                    default: Box::new(default()),
                }
            }
            Some(Ctor::List { .. }) => {
                let mut cases = Vec::new();
                for ctor in ctors.iter().filter(|c| named(c)) {
                    if let Ctor::List { len, .. } = ctor {
                        cases.push((*len, inner(ctor)));
                    }
                }
                let complete = cases.len() == ctors.len();
                DecisionTree::Length {
                    position,
                    cases,
                    default: (!complete).then(|| Box::new(default())),
                }
            }
            // A single type has a single constructor.
            Some(Ctor::Type { .. }) => inner(&ctors[0]),
        }
    }

    /// A test of the runtime type of column `i`, one case per atom a row
    /// looks for.
    fn switch(
        &self,
        rows: Vec<Row<'db>>,
        cols: Vec<Column<'db>>,
        i: usize,
        mut atoms: Vec<Ty<'db>>,
        guarded: &[bool],
    ) -> DecisionTree<'db> {
        let column = &cols[i];
        // A finer type fits more of the atoms, and must be tested first.
        let finer: Vec<usize> = atoms
            .iter()
            .map(|&a| atoms.iter().filter(|&&b| self.fits(a, b)).count())
            .collect();
        let mut order: Vec<usize> = (0..atoms.len()).collect();
        order.sort_by_key(|&k| std::cmp::Reverse(finer[k]));
        atoms = order.into_iter().map(|k| atoms[k]).collect();
        let mut cases = Vec::new();
        for atom in atoms {
            let named = rows
                .iter()
                .any(|r| !r.pats[i].is_wild() && self.admits(&r.pats[i], atom));
            if !named {
                continue;
            }
            let narrowed = rows
                .iter()
                .filter_map(|r| self.narrow(r, i, atom))
                .collect();
            let mut cols = cols.clone();
            cols[i] = Column {
                position: column.position.with(Step::As(atom)),
                ty: atom,
            };
            cases.push((atom, self.tree(narrowed, cols, guarded)));
        }
        let members = column.ty.members(self.db);
        let complete = members.iter().all(|m| cases.iter().any(|(t, _)| t == m));
        let default = (!complete).then(|| {
            let mut cols = cols.clone();
            cols.remove(i);
            let rows = rows
                .iter()
                .filter(|r| r.pats[i].is_wild())
                .map(|r| {
                    let mut r = r.clone();
                    r.pats.remove(i);
                    r
                })
                .collect();
            Box::new(self.tree(rows, cols, guarded))
        });
        DecisionTree::Switch {
            position: column.position.clone(),
            cases,
            default,
        }
    }

    /// Whether a pattern can match values of the atom.
    fn admits(&self, pattern: &Pattern<'db>, atom: Ty<'db>) -> bool {
        match pattern {
            Pattern::Type { ty: Some(p), .. } => self.fits(atom, *p),
            Pattern::Range { ty, .. } | Pattern::Value { ty, .. } => *ty == atom,
            Pattern::List { .. } => matches!(atom.as_builtin(self.db), Some((Builtin::List, _))),
            _ => true,
        }
    }

    /// The row for values of the atom at column `i`, whose type is then
    /// known; none when it cannot match them.
    fn narrow(&self, row: &Row<'db>, i: usize, atom: Ty<'db>) -> Option<Row<'db>> {
        if !self.admits(&row.pats[i], atom) {
            return None;
        }
        let mut row = row.clone();
        if let Pattern::Type {
            ty: ty @ Some(_),
            fields,
        } = &mut row.pats[i]
        {
            *ty = None;
            if fields.is_none() {
                row.pats[i] = Pattern::Wild;
            }
        }
        Some(row)
    }

    /// The rows for the values of `ctor` at column `i`, which is replaced
    /// by the positions inside it.
    fn specialize_rows(
        &self,
        rows: &[Row<'db>],
        cols: &[Column<'db>],
        i: usize,
        ctor: &Ctor<'db>,
    ) -> (Vec<Row<'db>>, Vec<Column<'db>>) {
        let position = &cols[i].position;
        let steps: Vec<Step<'db>> = match ctor {
            Ctor::Type { fields, .. } => fields.iter().map(|(n, _)| Step::Field(*n)).collect(),
            Ctor::List { len, .. } => match *len {
                ListLen::Fixed(n) => (0..n as u32).map(Step::Elem).collect(),
                ListLen::AtLeast { prefix, suffix } => (0..prefix as u32)
                    .map(Step::Elem)
                    .chain((0..suffix as u32).rev().map(Step::ElemBack))
                    .collect(),
            },
            _ => Vec::new(),
        };
        let inner: Vec<Column<'db>> = steps
            .into_iter()
            .zip(ctor.arity())
            .map(|(step, ty)| Column {
                position: position.with(step),
                ty,
            })
            .collect();
        let mut new_cols = cols[..i].to_vec();
        new_cols.extend(inner);
        new_cols.extend_from_slice(&cols[i + 1..]);
        let new_rows = rows
            .iter()
            .filter_map(|r| {
                let head = &r.pats[i];
                let inner = self.specialize(head, ctor)?;
                let mut bindings = r.bindings.clone();
                if let Pattern::List {
                    before,
                    rest: Some(Some(rest)),
                    after,
                } = head
                {
                    let slice = Step::Slice {
                        front: before.len() as u32,
                        back: after.len() as u32,
                    };
                    bindings.push((*rest, position.with(slice)));
                }
                let mut pats = r.pats[..i].to_vec();
                pats.extend(inner);
                pats.extend_from_slice(&r.pats[i + 1..]);
                Some(Row {
                    pats,
                    bindings,
                    arm: r.arm,
                })
            })
            .collect();
        (new_rows, new_cols)
    }
}

/// The row with its bindings taken out of the patterns, one row per
/// alternative of an or-pattern.
fn normalize<'db>(mut row: Row<'db>, cols: &[Column<'db>], out: &mut Vec<Row<'db>>) {
    for j in 0..row.pats.len() {
        while let Pattern::Bind(binding, sub) = &row.pats[j] {
            row.bindings.push((*binding, cols[j].position.clone()));
            row.pats[j] = (**sub).clone();
        }
        if let Pattern::Or(alternatives) = &row.pats[j] {
            for alt in alternatives.clone() {
                let mut r = row.clone();
                r.pats[j] = alt;
                normalize(r, cols, out);
            }
            return;
        }
    }
    out.push(row);
}
