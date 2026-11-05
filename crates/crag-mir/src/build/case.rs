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

//! `case`: the decision tree the patterns compile to, lowered to tests
//! and bindings.

use super::*;

impl<'a, 'db> MirBuilder<'a, 'db> {
    pub(super) fn case(&mut self, expr: ExprId, subject: ExprId, arms: &[Arm], dest: Dest) {
        let local = self.place_of(subject);
        let ty = self.ty(subject);
        let spec: Vec<(PatId, bool)> = arms.iter().map(|a| (a.pat, a.guard.is_some())).collect();
        let Some(tree) = decision_tree(self.db, self.program, self.owner, &self.pats, ty, &spec)
        else {
            self.trap(TrapKind::Error, Some(expr));
            return;
        };
        let fail = self.new_block();
        let mut m = Match {
            subject: local,
            arms: vec![None; arms.len()],
            guards: arms.iter().map(|a| a.guard).collect(),
            fail,
        };
        self.lower_decision_tree(&tree, &mut m);
        self.switch_to(fail);
        self.trap(TrapKind::NoMatch, Some(expr));
        let join = self.new_block();
        for (arm, block) in arms.iter().zip(m.arms) {
            let Some(block) = block else {
                continue;
            };
            self.switch_to(block);
            if let Expr::Pass = self.body.expr(arm.body) {
                // The values no earlier arm handled go to the caller
                // (§8.2).
                let passed = self.ty(arm.body);
                let op = match self.converts(ty, passed) {
                    true => self.assign(passed, Rvalue::Convert(Operand::Local(local))),
                    false => Operand::Local(local),
                };
                self.finish_dest(op, passed, Dest::Return);
                continue;
            }
            self.eval(arm.body, dest);
            self.join(dest, join);
        }
        self.switch_to(join);
    }

    /// Lowers a decision tree into tests of the subject, ending the
    /// current block. A leaf binds its arm's names and goes to the arm.
    pub(super) fn lower_decision_tree(&mut self, tree: &DecisionTree<'db>, m: &mut Match) {
        let db = self.db;
        match tree {
            DecisionTree::Fail => self.terminate(Terminator::Jump(m.fail)),
            DecisionTree::Leaf { arm, bindings } => {
                self.bind(m.subject, bindings);
                let target = self.arm_block(m, *arm);
                self.terminate(Terminator::Jump(target));
            }
            DecisionTree::Guard {
                arm,
                bindings,
                otherwise,
            } => {
                self.bind(m.subject, bindings);
                let target = self.arm_block(m, *arm);
                let next = self.new_block();
                let guard = m.guards[*arm].expect("a guarded arm has a guard");
                self.branch_on(guard, target, next);
                self.switch_to(next);
                self.lower_decision_tree(otherwise, m);
            }
            DecisionTree::Switch {
                position,
                cases,
                default,
            } => {
                let place = self.place(m.subject, position);
                let mut targets: Vec<(Ty<'db>, BlockId)> =
                    cases.iter().map(|(t, _)| (*t, self.new_block())).collect();
                let otherwise = match default {
                    Some(_) => self.new_block(),
                    None => targets.pop().map_or(m.fail, |(_, b)| b),
                };
                let blocks: Vec<BlockId> = targets.iter().map(|(_, b)| *b).collect();
                if targets.is_empty() {
                    self.terminate(Terminator::Jump(otherwise));
                } else {
                    self.terminate(Terminator::Switch {
                        place,
                        cases: targets,
                        otherwise,
                    });
                }
                for (block, (_, sub)) in blocks.iter().zip(cases) {
                    self.switch_to(*block);
                    self.lower_decision_tree(sub, m);
                }
                self.switch_to(otherwise);
                match default {
                    Some(default) => self.lower_decision_tree(default, m),
                    None => match cases.last() {
                        Some((_, sub)) => self.lower_decision_tree(sub, m),
                        None => self.terminate(Terminator::Jump(m.fail)),
                    },
                }
            }
            DecisionTree::Ranges {
                position,
                ty,
                cases,
                default,
            } => {
                let builtin = ty.as_builtin(db).map_or(Builtin::Int, |(b, _)| b);
                let value = self.read(m.subject, position, *ty);
                for (k, (lo, hi, sub)) in cases.iter().enumerate() {
                    if k + 1 == cases.len() && default.is_none() {
                        self.lower_decision_tree(sub, m);
                        return;
                    }
                    let (hit, miss) = (self.new_block(), self.new_block());
                    self.interval(value.clone(), builtin, *lo, *hi, hit, miss);
                    self.switch_to(hit);
                    self.lower_decision_tree(sub, m);
                    self.switch_to(miss);
                }
                match default {
                    Some(default) => self.lower_decision_tree(default, m),
                    None => self.terminate(Terminator::Jump(m.fail)),
                }
            }
            DecisionTree::Values {
                position,
                ty,
                cases,
                default,
            } => {
                let builtin = ty.as_builtin(db).map_or(Builtin::Str, |(b, _)| b);
                let value = self.read(m.subject, position, *ty);
                for (literal, sub) in cases {
                    let constant = match literal {
                        Value::Str(s) => Constant::Str(s.clone()),
                        Value::Bytes(b) => Constant::Bytes(b.clone()),
                        Value::Float(bits) => Constant::Float(*bits),
                    };
                    let same =
                        self.compare(CmpOp::Eq, builtin, value.clone(), Operand::Const(constant));
                    let (hit, miss) = (self.new_block(), self.new_block());
                    self.terminate(Terminator::Branch {
                        cond: same,
                        then: hit,
                        otherwise: miss,
                    });
                    self.switch_to(hit);
                    self.lower_decision_tree(sub, m);
                    self.switch_to(miss);
                }
                self.lower_decision_tree(default, m);
            }
            DecisionTree::Length {
                position,
                cases,
                default,
            } => {
                let place = self.place(m.subject, position);
                let len = self.assign(self.int(), Rvalue::Len(place));
                for (k, (length, sub)) in cases.iter().enumerate() {
                    if k + 1 == cases.len() && default.is_none() {
                        self.lower_decision_tree(sub, m);
                        return;
                    }
                    let fits = match length {
                        ListLen::Fixed(n) => {
                            self.compare(CmpOp::Eq, Builtin::Int, len.clone(), int(*n as i128))
                        }
                        ListLen::AtLeast { prefix, suffix } => self.compare(
                            CmpOp::Ge,
                            Builtin::Int,
                            len.clone(),
                            int((prefix + suffix) as i128),
                        ),
                    };
                    let (hit, miss) = (self.new_block(), self.new_block());
                    self.terminate(Terminator::Branch {
                        cond: fits,
                        then: hit,
                        otherwise: miss,
                    });
                    self.switch_to(hit);
                    self.lower_decision_tree(sub, m);
                    self.switch_to(miss);
                }
                match default {
                    Some(default) => self.lower_decision_tree(default, m),
                    None => self.terminate(Terminator::Jump(m.fail)),
                }
            }
        }
    }

    /// Goes to `hit` if the value lies between the ends, and to `miss` if
    /// not.
    fn interval(
        &mut self,
        value: Operand<'db>,
        ty: Builtin,
        lo: Option<i128>,
        hi: Option<i128>,
        hit: BlockId,
        miss: BlockId,
    ) {
        let mut tests = match (lo, hi) {
            (Some(l), Some(h)) if l == h => vec![(CmpOp::Eq, l)],
            _ => {
                let lo = lo.map(|l| (CmpOp::Ge, l));
                let hi = hi.map(|h| (CmpOp::Le, h));
                lo.into_iter().chain(hi).collect()
            }
        };
        let Some(last) = tests.pop() else {
            self.terminate(Terminator::Jump(hit));
            return;
        };
        for (op, bound) in tests {
            let ok = self.compare(op, ty, value.clone(), int(bound));
            let next = self.new_block();
            self.terminate(Terminator::Branch {
                cond: ok,
                then: next,
                otherwise: miss,
            });
            self.switch_to(next);
        }
        let ok = self.compare(last.0, ty, value, int(last.1));
        self.terminate(Terminator::Branch {
            cond: ok,
            then: hit,
            otherwise: miss,
        });
    }

    fn arm_block(&mut self, m: &mut Match, arm: usize) -> BlockId {
        match m.arms[arm] {
            Some(block) => block,
            None => {
                let block = self.new_block();
                m.arms[arm] = Some(block);
                block
            }
        }
    }

    fn place(&self, subject: Local, position: &Position<'db>) -> Place<'db> {
        Place {
            local: subject,
            path: position.0.clone(),
        }
    }

    /// The value at a position, which is not a slice.
    fn read(&mut self, subject: Local, position: &Position<'db>, ty: Ty<'db>) -> Operand<'db> {
        if position.0.is_empty() {
            return Operand::Local(subject);
        }
        let place = self.place(subject, position);
        self.assign(ty, Rvalue::Read(place))
    }

    /// The type of the value at a path into a local.
    pub(super) fn place_ty(&self, local: Local, path: &[Step<'db>]) -> Ty<'db> {
        let db = self.db;
        let mut ty = self.locals[local.index()].ty;
        for step in path {
            ty = match step {
                Step::As(t) => *t,
                Step::Field(name) => fields_of(db, self.program, ty)
                    .and_then(|fs| fs.into_iter().find(|(n, _)| n == name))
                    .map_or_else(|| Ty::error(db), |(_, t)| t),
                Step::Elem(_) | Step::ElemBack(_) => match ty.as_builtin(db) {
                    Some((Builtin::List, [element])) => *element,
                    _ => Ty::error(db),
                },
                Step::Slice { .. } => ty,
            };
        }
        ty
    }

    fn bind(&mut self, subject: Local, bindings: &[(BindingId, Position<'db>)]) {
        for (binding, position) in bindings {
            let local = self.binding(*binding);
            let path = &position.0;
            let (rvalue, ty) = match path.last() {
                None => {
                    let ty = self.locals[subject.index()].ty;
                    self.assign_to(local, Operand::Local(subject), ty);
                    continue;
                }
                Some(Step::Slice { front, back }) => {
                    let list = Place {
                        local: subject,
                        path: path[..path.len() - 1].to_vec(),
                    };
                    let ty = self.place_ty(subject, path);
                    let rvalue = Rvalue::Slice {
                        list,
                        front: *front,
                        back: *back,
                    };
                    (rvalue, ty)
                }
                Some(_) => (
                    Rvalue::Read(self.place(subject, position)),
                    self.place_ty(subject, path),
                ),
            };
            if ty == self.locals[local.index()].ty {
                self.push(Statement::Assign(local, rvalue));
            } else {
                let value = self.assign(ty, rvalue);
                self.assign_to(local, value, ty);
            }
        }
    }
}
