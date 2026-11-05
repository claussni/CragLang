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

//! Boxes: putting a value in its box, union members in theirs, and
//! reading a value back out, lent or taken.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    /// The words of a split value as its layout has them: a record's box,
    /// a union's two words, or the words as they are.
    pub(super) fn boxed(
        &mut self,
        ty: Ty<'db>,
        f: &Form<'db>,
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match f {
            Form::Words(_) => Ok(regs.to_vec()),
            Form::Fields(_) => Ok(vec![self.box_split(ty, f, regs)?]),
            Form::Union(members) => self.box_union(members, regs),
        }
    }

    /// The two words of a union split in registers: its type index, and
    /// its member's word, a record boxed and a member of two words in a
    /// member box, which take over the member's references.
    fn box_union(
        &mut self,
        members: &[(Ty<'db>, Form<'db>)],
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        let payload = self.constant(0);
        // A trap unwinding the frame releases the box made, as a boxed
        // local's, when every member's word is a pointer or nothing.
        let pointers = members
            .iter()
            .all(|(_, f)| !matches!(f, Form::Words(Layout::Imm(_))));
        if pointers {
            self.tracked.push(payload);
        }
        let done = self.new_block();
        for (m, f) in members {
            let n = f.words();
            // A record member is a box, even one of no words.
            if let Form::Words(Layout::Zero | Layout::Tag) = f {
                continue;
            }
            let (hit, next) = (self.new_block(), self.new_block());
            let index = self.constant(self.index(*m));
            let same = self.cmp(Cond::Eq, regs[0], index);
            let term = Term::Branch {
                cond: same,
                then: hit,
                otherwise: next,
            };
            self.end(term, Some(hit));
            let words = &regs[1..1 + n];
            let value = match f {
                Form::Words(Layout::Pair | Layout::Closure) => {
                    let header = match f {
                        Form::Words(Layout::Pair) => TEXT_BOX_HEADER,
                        _ => FUNCTION_BOX_HEADER,
                    };
                    let ptr = self.alloc(MEMBER_BOX_SIZE, header as i64);
                    for (k, &src) in words.iter().enumerate() {
                        self.push(Inst::Store {
                            src,
                            addr: ptr,
                            offset: (HEADER_SIZE + 8 * k as u32) as i32,
                        });
                    }
                    ptr
                }
                _ => word(&self.boxed(*m, f, words)?)?,
            };
            self.push(Inst::Move {
                dst: payload,
                src: value,
            });
            self.end(Term::Jump(done), Some(next));
        }
        self.end(Term::Jump(done), Some(done));
        Ok(vec![regs[0], payload])
    }

    /// The registers of a split value from the words its layout has, which
    /// it borrows: a record's fields loaded from its box, a union's member
    /// from its word.
    pub(super) fn unboxed(
        &mut self,
        ty: Ty<'db>,
        f: &Form<'db>,
        words: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match f {
            Form::Words(_) => Ok(words.to_vec()),
            Form::Fields(_) => self.unbox(ty, f, word(words)?),
            Form::Union(members) => {
                let out: Vec<VReg> = (0..f.words()).map(|_| self.constant(0)).collect();
                self.push(Inst::Move {
                    dst: out[0],
                    src: words[0],
                });
                let done = self.new_block();
                for (m, inner) in members {
                    let n = inner.words();
                    if n == 0 {
                        continue;
                    }
                    let (hit, next) = (self.new_block(), self.new_block());
                    let index = self.constant(self.index(*m));
                    let same = self.cmp(Cond::Eq, words[0], index);
                    let term = Term::Branch {
                        cond: same,
                        then: hit,
                        otherwise: next,
                    };
                    self.end(term, Some(hit));
                    let values = match inner {
                        Form::Words(Layout::Pair | Layout::Closure) => self.member_words(words[1]),
                        _ => self.unboxed(*m, inner, &words[1..2])?,
                    };
                    for (k, src) in values.into_iter().enumerate() {
                        self.push(Inst::Move {
                            dst: out[1 + k],
                            src,
                        });
                    }
                    self.end(Term::Jump(done), Some(next));
                }
                self.end(Term::Jump(done), Some(done));
                Ok(out)
            }
        }
    }

    /// A box holding the registers of a split record, which takes their
    /// references.
    fn box_split(
        &mut self,
        ty: Ty<'db>,
        form: &Form<'db>,
        regs: &[VReg],
    ) -> Result<VReg, Unsupported> {
        let Form::Fields(_) = form else {
            return word(regs);
        };
        let b = box_form(self.db, self.program, ty).ok_or("records of this type")?;
        self.describe(ty)?;
        let regs = self.reform(ty, form, &b.form, regs)?;
        let ptr = self.alloc(b.size, self.index(ty));
        // A trap unwinding the frame releases it, as a boxed local's.
        self.tracked.push(ptr);
        self.store_box(&b, ptr, &regs);
        Ok(ptr)
    }

    /// Writes the registers of a record's fields into its new box.
    pub(super) fn store_box(&mut self, b: &BoxForm<'db>, ptr: VReg, regs: &[VReg]) {
        let words = self.pack(&b.slots, b.size, regs);
        let header = (HEADER_SIZE / 8) as usize;
        for (k, src) in words.into_iter().enumerate().skip(header) {
            self.push(Inst::Store {
                src,
                addr: ptr,
                offset: 8 * k as i32,
            });
        }
    }

    /// The `n` registers of a value stored as `slots` in the box or the
    /// collection's slot at `ptr`, from the words that hold it. A slot of
    /// fewer bytes need not be aligned, and the collection has room for the
    /// last word read past its end.
    pub(super) fn load_stored(&mut self, ptr: VReg, slots: &[Slot], n: usize) -> Vec<VReg> {
        let Some((from, to)) = span(slots) else {
            return (0..n).map(|_| self.constant(0)).collect();
        };
        let first = from / 8 * 8;
        let words: Vec<VReg> = (first..to)
            .step_by(8)
            .map(|at| {
                let dst = self.reg();
                self.push(Inst::LoadUnaligned {
                    dst,
                    addr: ptr,
                    offset: at as i32,
                });
                dst
            })
            .collect();
        let slots: Vec<Slot> = slots.iter().map(|s| rebase(s, first)).collect();
        self.unpack(&slots, &words, n)
    }

    /// The registers of a split record loaded from its box, borrowed from
    /// it.
    fn unbox(
        &mut self,
        ty: Ty<'db>,
        form: &Form<'db>,
        ptr: VReg,
    ) -> Result<Vec<VReg>, Unsupported> {
        let Form::Fields(_) = form else {
            return Ok(vec![ptr]);
        };
        let b = box_form(self.db, self.program, ty).ok_or("records of this type")?;
        let regs = self.load_stored(ptr, &b.slots, b.form.words());
        self.lend(ty, &b.form, form, &regs)
    }

    /// The registers of a value in the form `to`, borrowed from its
    /// registers in the form `from`: a record or union in a box loaded
    /// from it.
    pub(super) fn lend(
        &mut self,
        ty: Ty<'db>,
        from: &Form<'db>,
        to: &Form<'db>,
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match (from, to) {
            _ if from == to => Ok(regs.to_vec()),
            (Form::Words(_), _) => self.unboxed(ty, to, regs),
            (Form::Fields(_), Form::Fields(fields)) => {
                let mut out = Vec::new();
                for (name, t, f) in fields {
                    let (at, _, inner) = from.field(*name).ok_or("records of this type")?;
                    let part = regs[at..at + inner.words()].to_vec();
                    out.extend(self.lend(*t, inner, f, &part)?);
                }
                Ok(out)
            }
            _ => Err("records of this type"),
        }
    }

    /// The registers of a value in the form `to`, from its registers in
    /// the form `from`, which they take the references of.
    pub(super) fn reform(
        &mut self,
        ty: Ty<'db>,
        from: &Form<'db>,
        to: &Form<'db>,
        regs: &[VReg],
    ) -> Result<Vec<VReg>, Unsupported> {
        match (from, to) {
            _ if from == to => Ok(regs.to_vec()),
            (Form::Fields(_), Form::Fields(fields)) => {
                let mut out = Vec::new();
                for (name, t, f) in fields {
                    let (at, _, inner) = from.field(*name).ok_or("records of this type")?;
                    let part = regs[at..at + inner.words()].to_vec();
                    out.extend(self.reform(*t, inner, f, &part)?);
                }
                Ok(out)
            }
            (_, Form::Words(_)) => self.boxed(ty, from, regs),
            (Form::Words(_), _) => self.owned_fields(ty, to, regs),
            _ => {
                let words = self.boxed(ty, from, regs)?;
                self.owned_fields(ty, to, &words)
            }
        }
    }
}
