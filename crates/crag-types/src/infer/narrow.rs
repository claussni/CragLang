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

//! Narrowing along control flow: what a condition tells of each path,
//! refining a binding's type by a test, joining paths, and `case`.

use super::*;

impl<'a, 'db> Infer<'a, 'db> {
    /// Checks a condition and returns the narrowings where it holds and
    /// where it does not.
    pub(super) fn condition(&mut self, id: ExprId) -> (Flow<'db>, Flow<'db>) {
        match self.body.expr(id) {
            Expr::And(..) | Expr::Or(..) | Expr::Not(_) | Expr::Is { .. } => {
                let outcomes = self.test(id);
                self.exprs[id.index()] = Some(self.bool_ty);
                outcomes
            }
            _ => {
                let bool_ty = self.bool_ty;
                self.check(id, bool_ty);
                (self.narrowed.clone(), self.narrowed.clone())
            }
        }
    }

    /// `and`, `or`, `not` and `is`, which narrow (§3.13.4): the right
    /// operand of `and` sees what the left one established, and that of
    /// `or` what the left one ruled out.
    pub(super) fn test(&mut self, id: ExprId) -> (Flow<'db>, Flow<'db>) {
        match self.body.expr(id) {
            Expr::And(a, b) => {
                let (a_holds, a_fails) = self.condition(*a);
                self.narrowed = a_holds;
                let (b_holds, b_fails) = self.condition(*b);
                (b_holds, self.merge(vec![a_fails, b_fails]))
            }
            Expr::Or(a, b) => {
                let (a_holds, a_fails) = self.condition(*a);
                self.narrowed = a_fails;
                let (b_holds, b_fails) = self.condition(*b);
                (self.merge(vec![a_holds, b_holds]), b_fails)
            }
            Expr::Not(a) => {
                let (holds, fails) = self.condition(*a);
                (fails, holds)
            }
            Expr::Is { expr, ty } => {
                let subject = self.synth(*expr);
                let target = self.pattern_type(*ty, subject);
                let start = self.narrowed.clone();
                if subject.is_error(self.db) || target.is_error(self.db) {
                    return (start.clone(), start);
                }
                let Some(matched) = self.refine(subject, target) else {
                    let kind = ErrorKind::NeverMatches {
                        pattern: target,
                        subject,
                    };
                    self.error(Site::Expr(id), kind);
                    return (start.clone(), start);
                };
                let Some(binding) = self.narrowable(*expr) else {
                    return (start.clone(), start);
                };
                let (mut holds, mut fails) = (start.clone(), start);
                holds[binding.index()] = Some(matched);
                fails[binding.index()] = Some(self.rest(subject, target));
                (holds, fails)
            }
            _ => unreachable!("only tests are tested"),
        }
    }

    /// The binding a test of `expr` narrows: a `let`, a `var` or a
    /// parameter read by its name. Refs and fields are never narrowed.
    pub(super) fn narrowable(&self, expr: ExprId) -> Option<BindingId> {
        let Expr::Name {
            local: Some(binding),
            ..
        } = self.body.expr(expr)
        else {
            return None;
        };
        let kind = self.body.binding(*binding).kind;
        matches!(
            kind,
            BindingKind::Let | BindingKind::Var | BindingKind::Param
        )
        .then_some(*binding)
    }

    /// The type a value of `subject` has when it is also one of `target`:
    /// `target` itself when it is one type that fits the subject, else
    /// the members of the subject that `target` overlaps; none when no
    /// value is of both.
    ///
    /// A union of finer types than the subject's members is never made,
    /// because a union value is tagged with the member it was made as.
    pub(super) fn refine(&self, subject: Ty<'db>, target: Ty<'db>) -> Option<Ty<'db>> {
        let (db, program) = (self.db, self.program);
        let tested = |s, t| crate::relate::tested(db, program, s, t);
        let targets = target.members(db);
        if targets.len() == 1 && tested(target, subject) {
            return Some(target);
        }
        let members: Vec<Ty<'db>> = subject
            .members(db)
            .into_iter()
            .filter(|&m| tested(m, target) || targets.iter().any(|&t| tested(t, m)))
            .collect();
        (!members.is_empty()).then(|| self.join_all(members))
    }

    /// The members of `subject` whose values are never of `target`.
    pub(super) fn rest(&self, subject: Ty<'db>, target: Ty<'db>) -> Ty<'db> {
        let members = subject
            .members(self.db)
            .into_iter()
            .filter(|&m| !crate::relate::tested(self.db, self.program, m, target))
            .collect();
        self.join_all(members)
    }

    /// The members of `subject` some value of which no pattern of the
    /// matrix matches.
    pub(super) fn unmatched(&self, matrix: &PatternMatrix<'db>, subject: Ty<'db>) -> Ty<'db> {
        let checker = Checker::new(self.db, self.program);
        let members = subject
            .members(self.db)
            .into_iter()
            .filter(|&m| checker.missing_example(matrix, m).is_some())
            .collect();
        self.join_all(members)
    }

    /// The pattern `id` as the case checker sees it, its alternatives
    /// apart; none if it did not type.
    pub(super) fn lowered(&self, id: PatId) -> Option<Vec<crate::case::Pattern<'db>>> {
        let checker = Checker::new(self.db, self.program);
        let alternatives = match self.body.pat(id) {
            Pat::Or(alternatives) => alternatives.clone(),
            _ => vec![id],
        };
        alternatives
            .into_iter()
            .map(|alt| checker.lower(self.body, &self.pats, alt))
            .collect()
    }

    /// Where control paths meet: a binding stays narrowed if every path
    /// that gets here narrowed it, to the union of what they narrowed it
    /// to.
    pub(super) fn merge(&self, flows: Vec<Flow<'db>>) -> Flow<'db> {
        let mut flows = flows.into_iter();
        let Some(mut merged) = flows.next() else {
            return self.narrowed.clone();
        };
        for flow in flows {
            for (m, f) in merged.iter_mut().zip(flow) {
                *m = match (*m, f) {
                    (Some(a), Some(b)) => Some(self.join(a, b)),
                    _ => None,
                };
            }
        }
        merged
    }

    /// Continues after branches, each with its type and the narrowings at
    /// its end; a branch of type `Never` does not get here.
    pub(super) fn meet(&mut self, ends: Vec<(Ty<'db>, Flow<'db>)>) {
        let db = self.db;
        let (reached, left): (Vec<_>, Vec<_>) =
            ends.into_iter().partition(|(ty, _)| !ty.is_never(db));
        self.narrowed = match reached.is_empty() {
            true => left.into_iter().next().map(|(_, f)| f).unwrap_or_default(),
            false => self.merge(reached.into_iter().map(|(_, f)| f).collect()),
        };
    }

    /// Narrowings that do not hold in code that may run later, such as a
    /// closure: those of `var`s.
    pub(super) fn without_vars(&self) -> Flow<'db> {
        let body = self.body;
        self.narrowed
            .iter()
            .enumerate()
            .map(|(i, &ty)| match body.bindings[i].kind {
                BindingKind::Var => None,
                _ => ty,
            })
            .collect()
    }

    /// `case` (§7.2): a subject that is a binding is narrowed in each arm
    /// to what its pattern matches of the values no earlier arm took. A
    /// `pass` arm gives those values to the caller (§8.2).
    pub(super) fn case(
        &mut self,
        subject: ExprId,
        arms: &[Arm],
        expected: Option<Ty<'db>>,
    ) -> Ty<'db> {
        let db = self.db;
        let subject_ty = self.synth(subject);
        let binding = self.narrowable(subject);
        let start = self.narrowed.clone();
        let mut remaining = Some(subject_ty);
        let mut matrix = PatternMatrix::default();
        let mut types = Vec::new();
        let mut ends = Vec::new();
        let mut typed = true;
        for arm in arms {
            self.narrowed = start.clone();
            // `name: _` and a bare name bind what no earlier arm matched
            // (§7.2).
            let rest = match self.body.pat(arm.pat) {
                Pat::Bind { sub: None, .. } => true,
                Pat::Bind { sub: Some(sub), .. } => matches!(self.body.pat(*sub), Pat::Wildcard),
                _ => false,
            };
            let against = match remaining {
                Some(r) if rest && !r.is_never(db) => r,
                _ => subject_ty,
            };
            typed &= self.pattern_checks(arm.pat, against);
            // What the arm matches of what is left; an arm that never
            // matches, which is reported, narrows nothing.
            let matched = self.pats[arm.pat.index()]
                .filter(|m| !m.is_error(db))
                .and_then(|m| self.refine(remaining.unwrap_or(subject_ty), m));
            if let (Some(binding), Some(matched)) = (binding, matched) {
                self.narrowed[binding.index()] = Some(matched);
            }
            if let Some(guard) = arm.guard {
                let (holds, _) = self.condition(guard);
                self.narrowed = holds;
            }
            let ty = match self.body.expr(arm.body) {
                Expr::Pass => {
                    let passed = matched.unwrap_or(subject_ty);
                    self.result_value(Site::Expr(arm.body), passed);
                    let never = Ty::never(db);
                    self.exprs[arm.body.index()] = Some(passed);
                    never
                }
                _ => self.infer(arm.body, expected),
            };
            types.push(ty);
            ends.push((ty, std::mem::take(&mut self.narrowed)));
            if arm.guard.is_none() {
                remaining = match (remaining, self.lowered(arm.pat)) {
                    (Some(r), Some(patterns)) => {
                        for pattern in patterns {
                            matrix.push(pattern);
                        }
                        Some(self.unmatched(&matrix, r))
                    }
                    // Past an arm that did not type, nothing is known.
                    _ => None,
                };
            }
        }
        if typed {
            self.coverage(subject, subject_ty, arms);
        }
        match ends.is_empty() {
            true => self.narrowed = start,
            false => self.meet(ends),
        }
        self.join_all(types)
    }

    // Statements.
}
