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

//! Patterns against the type of their subject, their coverage of it,
//! and what they narrow it to.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    /// Checks a pattern against the type of what it matches and returns the
    /// type it narrows that to.
    pub(super) fn pattern(&mut self, id: PatId, subject: Ty<'db>) -> Ty<'db> {
        let ty = self.pattern_inner(id, subject);
        self.pats[id.index()] = Some(ty);
        ty
    }

    fn pattern_inner(&mut self, id: PatId, subject: Ty<'db>) -> Ty<'db> {
        let db = self.db;
        let body = self.body;
        match body.pat(id) {
            Pat::Missing => self.err_ty(),
            Pat::Wildcard => subject,
            Pat::Bind { binding, sub } => {
                let ty = match sub {
                    Some(sub) => self.pattern(*sub, subject),
                    None => subject,
                };
                // The alternatives of an or-pattern share their bindings.
                let ty = match self.bindings[binding.index()] {
                    Some(previous) => self.join(previous, ty),
                    None => ty,
                };
                self.bindings[binding.index()] = Some(ty);
                ty
            }
            Pat::Type(tref) => {
                let ty = self.pattern_type(*tref, subject);
                self.narrow(id, ty, subject)
            }
            Pat::Record { ty, fields } => {
                let matched = match ty {
                    Some(tref) => {
                        let ty = self.pattern_type(*tref, subject);
                        self.narrow(id, ty, subject)
                    }
                    None => subject,
                };
                let declared: Vec<(Name<'db>, Ty<'db>)> =
                    match declared_fields(db, self.program, matched) {
                        Some(fields) => fields.into_iter().map(|(n, t, _)| (n, t)).collect(),
                        None => match fields_of(db, self.program, matched) {
                            Some(fields) => fields,
                            None => {
                                if !matched.is_error(db) {
                                    let kind = ErrorKind::NeverMatches {
                                        pattern: Ty::unit(db),
                                        subject: matched,
                                    };
                                    self.error(Site::Pat(id), kind);
                                }
                                for field in fields {
                                    self.pattern(field.pat, Ty::error(db));
                                }
                                return self.err_ty();
                            }
                        },
                    };
                for (i, field) in fields.iter().enumerate() {
                    let field_ty = match field.name {
                        Some(name) => declared.iter().find(|(n, _)| *n == name).map(|(_, t)| *t),
                        None => declared.get(i).map(|(_, t)| *t),
                    };
                    let field_ty = match field_ty {
                        Some(t) => t,
                        None => {
                            if !matched.is_error(db) {
                                let kind = match field.name {
                                    Some(name) => ErrorKind::NoField { ty: matched, name },
                                    None => ErrorKind::ArgCount {
                                        expected: declared.len(),
                                        found: fields.len(),
                                    },
                                };
                                self.error(Site::Pat(field.pat), kind);
                            }
                            Ty::error(db)
                        }
                    };
                    self.pattern(field.pat, field_ty);
                }
                matched
            }
            Pat::List {
                before,
                rest,
                after,
            } => {
                let element = match self.member_builtin(subject, &[Builtin::List]) {
                    Some((_, args)) => args[0],
                    None => {
                        if !subject.is_error(db) {
                            let pattern = self.builtin_of(Builtin::List, vec![Ty::error(db)]);
                            let kind = ErrorKind::NeverMatches { pattern, subject };
                            self.error(Site::Pat(id), kind);
                        }
                        Ty::error(db)
                    }
                };
                for &p in before.iter().chain(after) {
                    self.pattern(p, element);
                }
                let list = self.builtin_of(Builtin::List, vec![element]);
                if let Some(Some(binding)) = rest {
                    self.bindings[binding.index()] = Some(list);
                }
                list
            }
            Pat::Literal(literal) | Pat::Range { start: literal, .. } => {
                let ty = self.literal_ty(&literal.literal, Some(subject));
                if !self.pattern_literal_fits(literal, ty) {
                    self.error(Site::Pat(id), ErrorKind::Literal { ty });
                }
                if let Pat::Range { start, end } = body.pat(id) {
                    let scale = fixed_scale(self.db, ty);
                    if !self.pattern_literal_fits(end, ty) {
                        self.error(Site::Pat(id), ErrorKind::Literal { ty });
                    } else if !self.is_discrete(ty) {
                        self.error(Site::Pat(id), ErrorKind::NotDiscrete { ty });
                    } else if let Some(scale) = scale
                        && let Some(written) =
                            [start, end].into_iter().find_map(|l| match &l.literal {
                                Literal::Float(text) => decimals(text).filter(|&d| d != scale),
                                _ => None,
                            })
                    {
                        let found = self.builtin(Builtin::Fixed(written));
                        let kind = ErrorKind::Mismatch {
                            expected: ty,
                            found,
                        };
                        self.error(Site::Pat(id), kind);
                    } else if let (Some(lo), Some(hi)) = (signed(start, scale), signed(end, scale))
                        && lo > hi
                    {
                        self.error(Site::Pat(id), ErrorKind::Decreasing);
                    }
                }
                self.narrow(id, ty, subject)
            }
            Pat::Or(alternatives) => {
                let types = alternatives
                    .iter()
                    .map(|&alt| self.pattern(alt, subject))
                    .collect();
                self.join_all(types)
            }
        }
    }

    /// Checks a pattern as `pattern` does and says whether it typed
    /// without errors, so that coverage is only checked for patterns that
    /// did.
    pub(super) fn pattern_checks(&mut self, id: PatId, subject: Ty<'db>) -> bool {
        let before = self.lower.errors.len();
        self.pattern(id, subject);
        self.lower.errors.len() == before && !subject.is_error(self.db)
    }

    /// Reports the arms of a `case` that earlier arms cover, and a value
    /// no arm covers (§7.2).
    pub(super) fn coverage(&mut self, subject: ExprId, ty: Ty<'db>, arms: &[Arm]) {
        let checker = Checker::new(self.db, self.program);
        let body = self.body;
        let mut lowered = Vec::new();
        for arm in arms {
            let alternatives = match body.pat(arm.pat) {
                Pat::Or(alternatives) => alternatives.clone(),
                _ => vec![arm.pat],
            };
            let mut patterns = Vec::new();
            for id in alternatives {
                let Some(pattern) = checker.lower(body, &self.pats, id) else {
                    return;
                };
                patterns.push((id, pattern));
            }
            lowered.push(patterns);
        }
        let mut matrix = PatternMatrix::default();
        for (arm, alternatives) in arms.iter().zip(lowered) {
            let mut covered = matrix.clone();
            let mut unreachable = Vec::new();
            let count = alternatives.len();
            for (id, pattern) in alternatives {
                if !checker.is_useful(&covered, &pattern, ty) {
                    unreachable.push(id);
                }
                covered.push(pattern);
            }
            if unreachable.len() == count {
                self.error(Site::Pat(arm.pat), ErrorKind::Unreachable);
            } else {
                for id in unreachable {
                    self.error(Site::Pat(id), ErrorKind::Unreachable);
                }
            }
            if arm.guard.is_none() {
                matrix = covered;
            }
        }
        if let Some(missing) = checker.missing_example(&matrix, ty) {
            let missing = missing.display(self.db);
            self.error(Site::Expr(subject), ErrorKind::NotExhaustive { missing });
        }
    }

    /// Reports a value of `ty` the pattern of a `let` or a `for` does not
    /// match.
    pub(super) fn irrefutable(&mut self, id: PatId, ty: Ty<'db>) {
        let checker = Checker::new(self.db, self.program);
        let Some(pattern) = checker.lower(self.body, &self.pats, id) else {
            return;
        };
        let mut matrix = PatternMatrix::default();
        matrix.push(pattern);
        if let Some(missing) = checker.missing_example(&matrix, ty) {
            let missing = missing.display(self.db);
            self.error(Site::Pat(id), ErrorKind::Refutable { missing });
        }
    }

    /// Whether a literal of a pattern, with its sign, fits `ty`.
    fn pattern_literal_fits(&mut self, literal: &PatLiteral, ty: Ty<'db>) -> bool {
        let outer = std::mem::replace(&mut self.negative, literal.negative);
        let fits = self.literal_fits(&literal.literal, ty);
        self.negative = outer;
        fits
    }

    /// The type a type pattern names. A generic tag without arguments takes
    /// them from the one member of the subject it can be (§3.6.1).
    pub(super) fn pattern_type(&mut self, tref: TypeRefId, subject: Ty<'db>) -> Ty<'db> {
        let db = self.db;
        if let TypeRef::Named {
            target: TypeTarget::Item(item),
            args,
            ..
        } = self.body.type_ref(tref)
            && args.is_empty()
            && *item.kind(db) == ItemKind::Type
            && !type_header(db, self.program, *item).params.is_empty()
        {
            let identity = type_identity(db, self.program, *item);
            let levels: Vec<Ty<'db>> = subject
                .members(db)
                .into_iter()
                .filter(|m| matches!(m.kind(db), TyKind::Named(i, _) if *i == identity))
                .collect();
            let ty = match levels.as_slice() {
                [one] => *one,
                _ => {
                    self.error(Site::Type(tref), ErrorKind::CannotInfer);
                    self.err_ty()
                }
            };
            self.lower.types[tref.index()] = Some(ty);
            return ty;
        }
        self.lower_type(tref)
    }

    /// What a pattern of type `ty` narrows the subject to: the members of
    /// the subject that fit it, or `ty` itself when it is part of one.
    fn narrow(&mut self, id: PatId, ty: Ty<'db>, subject: Ty<'db>) -> Ty<'db> {
        let db = self.db;
        if self.fits(ty, subject) {
            return ty;
        }
        let members: Vec<Ty<'db>> = subject
            .members(db)
            .into_iter()
            .filter(|&m| self.fits(m, ty))
            .collect();
        if !members.is_empty() {
            return self.join_all(members);
        }
        let kind = ErrorKind::NeverMatches {
            pattern: ty,
            subject,
        };
        self.error(Site::Pat(id), kind);
        ty
    }
}
