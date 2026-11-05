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

//! Registers and storage forms: packing a value's registers into the
//! words that store it, and unpacking them again, with the tags and
//! niches of unions and the bits of narrow fields.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    /// The register form of a flat record or union from the words of its
    /// storage form (Compiler Architecture §A11.4).
    pub(super) fn unpack(&mut self, slots: &[Slot], words: &[VReg], registers: usize) -> Vec<VReg> {
        let mut out: Vec<Option<VReg>> = vec![None; registers];
        self.unpack_into(slots, words, &mut out);
        out.into_iter()
            .map(|r| r.unwrap_or_else(|| self.constant(0)))
            .collect()
    }

    fn unpack_into(&mut self, slots: &[Slot], words: &[VReg], out: &mut [Option<VReg>]) {
        for slot in slots {
            let w = (slot.offset / 8) as usize;
            let byte = slot.offset % 8;
            match &slot.kind {
                SlotKind::Words => {
                    for k in 0..(slot.size / 8) as usize {
                        out[slot.at + k] = Some(words[w + k]);
                    }
                }
                SlotKind::Int { signed } => {
                    let bits = 8 * slot.size;
                    out[slot.at] = Some(match (bits, signed) {
                        (64, _) => words[w],
                        // Up to the field, then down with its sign.
                        (_, true) => {
                            let up = self.constant(i64::from(64 - 8 * byte - bits));
                            let raised = self.bin(LirBin::Shl, words[w], up);
                            let down = self.constant(i64::from(64 - bits));
                            self.bin(LirBin::SShr, raised, down)
                        }
                        (_, false) => self.field_bits(words[w], 8 * byte, bits),
                    });
                }
                SlotKind::Tag(members) => {
                    let (shift, width) = match slot.bits {
                        Some((bit, width)) => (8 * byte + u32::from(bit), u32::from(width)),
                        None => (8 * byte, 8 * slot.size),
                    };
                    let tag = self.field_bits(words[w], shift, width);
                    out[slot.at] = Some(self.type_of_tag(tag, members));
                }
                SlotKind::Union { tag, members } => {
                    // The member's type index, from its tag or the niche.
                    let index = match tag {
                        UnionTag::Bytes { offset, size } => {
                            let word = words[(offset / 8) as usize];
                            let tag = self.field_bits(word, 8 * (offset % 8), 8 * size);
                            let indices: Vec<i64> = members.iter().map(|m| m.0).collect();
                            self.type_of_tag(tag, &indices)
                        }
                        UnionTag::Niche {
                            empty,
                            offset,
                            test,
                        } => {
                            let niche = self.niche(words, *offset, *test);
                            let other = 1 - *empty;
                            let (e, o) = (
                                self.constant(members[*empty].0),
                                self.constant(members[other].0),
                            );
                            let dst = self.reg();
                            self.push(Inst::Select {
                                dst,
                                cond: niche,
                                a: e,
                                b: o,
                            });
                            dst
                        }
                    };
                    out[slot.at] = Some(index);
                    // Each member's registers, where its index is the one.
                    for (m, member) in members {
                        let mut own: Vec<Option<VReg>> = vec![None; out.len()];
                        self.unpack_into(member, words, &mut own);
                        let m = self.constant(*m);
                        let same = self.cmp(Cond::Eq, index, m);
                        for (r, value) in own.into_iter().enumerate() {
                            let Some(value) = value else { continue };
                            let other = out[r].unwrap_or_else(|| self.constant(0));
                            let dst = self.reg();
                            self.push(Inst::Select {
                                dst,
                                cond: same,
                                a: value,
                                b: other,
                            });
                            out[r] = Some(dst);
                        }
                    }
                }
            }
        }
    }

    /// The type index of the member a local tag numbers.
    fn type_of_tag(&mut self, tag: VReg, members: &[i64]) -> VReg {
        let mut index = self.constant(members[0]);
        for (k, &m) in members.iter().enumerate().skip(1) {
            let k = self.constant(k as i64);
            let same = self.cmp(Cond::Eq, tag, k);
            let m = self.constant(m);
            let dst = self.reg();
            self.push(Inst::Select {
                dst,
                cond: same,
                a: m,
                b: index,
            });
            index = dst;
        }
        index
    }

    /// The local tag of the member whose type index a register holds.
    fn tag_of_type(&mut self, index: VReg, members: &[i64]) -> VReg {
        let mut tag = self.constant(0);
        for (k, &m) in members.iter().enumerate().skip(1) {
            let m = self.constant(m);
            let same = self.cmp(Cond::Eq, index, m);
            let k = self.constant(k as i64);
            let dst = self.reg();
            self.push(Inst::Select {
                dst,
                cond: same,
                a: k,
                b: tag,
            });
            tag = dst;
        }
        tag
    }

    /// Puts the low `width` bits of a value at bit `at` of storage words.
    fn or_bits(&mut self, words: &mut [Option<VReg>], value: VReg, at: u32, width: u32) {
        let mut part = value;
        if width < 64 {
            let mask = self.constant(((1u64 << width) - 1) as i64);
            part = self.bin(LirBin::And, part, mask);
        }
        if !at.is_multiple_of(64) {
            let by = self.constant(i64::from(at % 64));
            part = self.bin(LirBin::Shl, part, by);
        }
        let w = (at / 64) as usize;
        words[w] = Some(match words[w] {
            Some(before) => self.bin(LirBin::Or, before, part),
            None => part,
        });
    }

    /// Whether storage words hold a niche: 1 or 0.
    fn niche(&mut self, words: &[VReg], offset: u32, test: NicheTest) -> VReg {
        let word = words[(offset / 8) as usize];
        let shift = 8 * (offset % 8);
        let (bits, value) = match test {
            NicheTest::Value { size, value } => {
                (self.field_bits(word, shift, 8 * u32::from(size)), value)
            }
            NicheTest::Bit(bit) => (self.field_bits(word, shift + u32::from(bit), 1), 1),
        };
        let value = self.constant(value as i64);
        self.cmp(Cond::Eq, bits, value)
    }

    /// The words of a flat record's or union's storage form from its
    /// register form.
    pub(super) fn pack(&mut self, slots: &[Slot], size: u32, regs: &[VReg]) -> Vec<VReg> {
        let mut words: Vec<Option<VReg>> = vec![None; size.div_ceil(8) as usize];
        self.pack_into(slots, regs, &mut words);
        words
            .into_iter()
            .map(|w| w.unwrap_or_else(|| self.constant(0)))
            .collect()
    }

    fn pack_into(&mut self, slots: &[Slot], regs: &[VReg], words: &mut [Option<VReg>]) {
        for slot in slots {
            let w = (slot.offset / 8) as usize;
            let byte = slot.offset % 8;
            let (value, shift, width) = match &slot.kind {
                SlotKind::Words => {
                    for k in 0..(slot.size / 8) as usize {
                        words[w + k] = Some(regs[slot.at + k]);
                    }
                    continue;
                }
                SlotKind::Int { .. } => (regs[slot.at], 8 * byte, 8 * slot.size),
                SlotKind::Tag(members) => {
                    let tag = self.tag_of_type(regs[slot.at], members);
                    match slot.bits {
                        Some((bit, width)) => (tag, 8 * byte + u32::from(bit), u32::from(width)),
                        None => (tag, 8 * byte, 8 * slot.size),
                    }
                }
                SlotKind::Union { tag, members } => {
                    // Each member's words with its tag or niche, where its
                    // index is the one.
                    let mut chosen: Vec<Option<VReg>> = vec![None; words.len()];
                    for (k, (m, member)) in members.iter().enumerate() {
                        let mut own: Vec<Option<VReg>> = vec![None; words.len()];
                        self.pack_into(member, regs, &mut own);
                        match tag {
                            UnionTag::Bytes { offset, size } => {
                                let k = self.constant(k as i64);
                                self.or_bits(&mut own, k, 8 * offset, 8 * size);
                            }
                            // The member of no words is the other's niche.
                            UnionTag::Niche {
                                empty,
                                offset,
                                test,
                            } if *empty == k => {
                                let (value, at, width) = match *test {
                                    NicheTest::Value { size, value } => {
                                        (value as i64, 8 * offset, 8 * u32::from(size))
                                    }
                                    NicheTest::Bit(bit) => (1, 8 * offset + u32::from(bit), 1),
                                };
                                let value = self.constant(value);
                                self.or_bits(&mut own, value, at, width);
                            }
                            UnionTag::Niche { .. } => {}
                        }
                        let m = self.constant(*m);
                        let same = self.cmp(Cond::Eq, regs[slot.at], m);
                        for (w, value) in own.into_iter().enumerate() {
                            let Some(value) = value else { continue };
                            let other = chosen[w].unwrap_or_else(|| self.constant(0));
                            let dst = self.reg();
                            self.push(Inst::Select {
                                dst,
                                cond: same,
                                a: value,
                                b: other,
                            });
                            chosen[w] = Some(dst);
                        }
                    }
                    for (w, value) in chosen.into_iter().enumerate() {
                        if let Some(value) = value {
                            words[w] = Some(match words[w] {
                                Some(before) => self.bin(LirBin::Or, before, value),
                                None => value,
                            });
                        }
                    }
                    continue;
                }
            };
            self.or_bits(words, value, 64 * w as u32 + shift, width);
        }
    }

    /// The `width` bits of a word from bit `shift` up, zero-extended.
    fn field_bits(&mut self, word: VReg, shift: u32, width: u32) -> VReg {
        let mut value = word;
        if shift > 0 {
            let by = self.constant(i64::from(shift));
            value = self.bin(LirBin::UShr, value, by);
        }
        if width < 64 {
            let mask = self.constant(((1u64 << width) - 1) as i64);
            value = self.bin(LirBin::And, value, mask);
        }
        value
    }

    /// The words of an argument that passes by value: a split local's
    /// registers packed, or a boxed record's fields loaded, which take
    /// references of their own as the call takes the box's.
    pub(super) fn flat_argument(
        &mut self,
        op: &Operand<'db>,
        ty: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let (size, slots) = storage(self.db, self.program, ty).ok_or("records of this type")?;
        let regs = self.flat_value(op, ty)?;
        Ok(self.pack(&slots, size, &regs))
    }

    /// The registers of a value that passes by value, which takes the
    /// operand's references: a split local's registers, a boxed value's
    /// loaded, or a tag's type index.
    pub(super) fn flat_value(
        &mut self,
        op: &Operand<'db>,
        ty: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let f = form(self.db, self.program, ty).ok_or("records of this type")?;
        match op {
            Operand::Local(l) if self.forms[l.index()].is_some() => {
                Ok(self.locals[l.index()].clone())
            }
            Operand::Local(l) => {
                let words = self.locals[l.index()].clone();
                self.owned_fields(ty, &f, &words)
            }
            Operand::Const(Constant::Tag(tag)) => {
                let mut regs = vec![self.constant(self.index(self.member_of(*tag, ty)))];
                while regs.len() < f.words() {
                    regs.push(self.constant(0));
                }
                Ok(regs)
            }
            Operand::Const(_) => Err("this conversion"),
        }
    }
}
