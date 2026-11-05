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

//! Conversions between types a value fits, and arithmetic with its
//! overflow checks.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    /// A value of `from` as a value of `to`: a member put into a union or
    /// taken out of it, or a record as its parent.
    pub(super) fn convert(
        &mut self,
        values: Vec<VReg>,
        from: Ty<'db>,
        to: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let (f, t) = (self.layout_of(from)?, self.layout_of(to)?);
        let tag = self.index(self.member_of(from, to));
        // A conditioned alias's values and its target's are the same.
        let plain = |ty| crag_types::unrefined(self.db, self.program, ty);
        if f == t && plain(from) == plain(to) && !matches!(f, Layout::Tag | Layout::Union) {
            return Ok(values);
        }
        Ok(match (f, t) {
            (Layout::Zero, Layout::Zero) => Vec::new(),
            (Layout::Zero, Layout::Tag) => vec![self.constant(tag)],
            (Layout::Zero, Layout::Union) => vec![self.constant(tag), self.constant(0)],
            (Layout::Imm(_) | Layout::Box, Layout::Union) => vec![self.constant(tag), values[0]],
            (Layout::Tag, Layout::Union) => vec![self.retag(values[0], from, to), self.constant(0)],
            (Layout::Union, Layout::Union) => vec![self.retag(values[0], from, to), values[1]],
            (Layout::Tag, Layout::Tag) => vec![self.retag(values[0], from, to)],
            (Layout::Box, Layout::Box) | (Layout::Pair, Layout::Pair) => values,
            (Layout::Union, Layout::Imm(_) | Layout::Box) => vec![values[1]],
            (Layout::Union, Layout::Tag) => vec![values[0]],
            (Layout::Union | Layout::Tag, Layout::Zero) => Vec::new(),
            // A function value fits where one of its type is expected,
            // or one that is not Pure.
            (Layout::Closure, Layout::Closure) if self.same_code(from, to) => values,
            (Layout::Closure, Layout::Closure) => return Err("conversions of function values"),
            // A member of two words goes into a member box, which takes
            // over its references, and comes out with references of its
            // own, giving up the box.
            (Layout::Pair | Layout::Closure, Layout::Union) => {
                let header = match f {
                    Layout::Pair => TEXT_BOX_HEADER,
                    _ => FUNCTION_BOX_HEADER,
                };
                let ptr = self.alloc(MEMBER_BOX_SIZE, header as i64);
                for (k, src) in values.into_iter().enumerate() {
                    let offset = (HEADER_SIZE + 8 * k as u32) as i32;
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset,
                    });
                }
                vec![self.constant(tag), ptr]
            }
            (Layout::Union, Layout::Pair | Layout::Closure) => {
                let words = self.member_words(values[1]);
                self.count_words(Some(t), to, &words, Self::retain)?;
                self.release(values[1]);
                words
            }
            _ => return Err("this conversion"),
        })
    }

    /// The two words of a union's member in the member box at `ptr`.
    pub(super) fn member_words(&mut self, ptr: VReg) -> Vec<VReg> {
        (0..2)
            .map(|k| self.load(ptr, (HEADER_SIZE + 8 * k) as i32))
            .collect()
    }

    /// Whether values of two function types call the same code: their
    /// parameters and results are the same, if not whether they are Pure.
    fn same_code(&self, from: Ty<'db>, to: Ty<'db>) -> bool {
        match (from.as_fn(self.db), to.as_fn(self.db)) {
            (Some((a, r, _)), Some((b, q, _))) => a == b && r == q,
            _ => false,
        }
    }

    /// The member of the union `to` that a value of `from` is tagged
    /// with: the member it is a value of, which may be a parent of its
    /// type. A type test of a finer type reads the box's header.
    pub(super) fn member_of(&self, from: Ty<'db>, to: Ty<'db>) -> Ty<'db> {
        let members = to.members(self.db);
        if members.contains(&from) {
            return from;
        }
        members
            .into_iter()
            .find(|&m| crag_types::is_subtype(self.db, self.program, from, m))
            .unwrap_or(from)
    }

    /// The tag of a union value of `from` as one of `to`, where a member of
    /// `from` may be part of a member of `to`.
    fn retag(&mut self, tag: VReg, from: Ty<'db>, to: Ty<'db>) -> VReg {
        let mut tag = tag;
        for member in from.members(self.db) {
            let target = self.member_of(member, to);
            if target == member {
                continue;
            }
            let (old, new) = (
                self.constant(self.index(member)),
                self.constant(self.index(target)),
            );
            let cond = self.cmp(Cond::Eq, tag, old);
            let dst = self.reg();
            self.push(Inst::Select {
                dst,
                cond,
                a: new,
                b: tag,
            });
            tag = dst;
        }
        tag
    }

    /// The machine operation of a number type.
    pub(super) fn arith(
        &mut self,
        op: BinOp,
        ty: Builtin,
        a: VReg,
        b: VReg,
    ) -> Result<VReg, Unsupported> {
        let unsigned = matches!(
            ty,
            Builtin::UInt8 | Builtin::UInt16 | Builtin::UInt32 | Builtin::UInt64
        );
        let lir = match (ty, op) {
            (Builtin::Float, BinOp::Add) => LirBin::FAdd,
            (Builtin::Float, BinOp::Sub) => LirBin::FSub,
            (Builtin::Float, BinOp::Mul) => LirBin::FMul,
            (Builtin::Float, BinOp::Div) => LirBin::FDiv,
            (Builtin::Float, BinOp::Rem) => return Err("Float remainders"),
            (_, BinOp::Add) => LirBin::Add,
            (_, BinOp::Sub) => LirBin::Sub,
            (_, BinOp::Mul) => LirBin::Mul,
            (_, BinOp::Div) if unsigned => LirBin::UDiv,
            (_, BinOp::Div) => LirBin::SDiv,
            (_, BinOp::Rem) if unsigned => LirBin::URem,
            (_, BinOp::Rem) => LirBin::SRem,
        };
        let result = self.bin(lir, a, b);
        Ok(self.narrow(ty, result))
    }

    /// A 64-bit result wrapped to the width of a narrow integer type.
    pub(super) fn narrow(&mut self, ty: Builtin, value: VReg) -> VReg {
        let (bits, signed) = match ty {
            Builtin::Int8 => (8, true),
            Builtin::Int16 => (16, true),
            Builtin::Int32 => (32, true),
            Builtin::UInt8 => (8, false),
            Builtin::UInt16 => (16, false),
            Builtin::UInt32 => (32, false),
            _ => return value,
        };
        if signed {
            let shift = self.constant(64 - bits);
            let up = self.bin(LirBin::Shl, value, shift);
            self.bin(LirBin::SShr, up, shift)
        } else {
            let mask = self.constant((1i64 << bits) - 1);
            self.bin(LirBin::And, value, mask)
        }
    }

    /// 1 if the operation overflows its type, else 0.
    pub(super) fn overflows(
        &mut self,
        op: BinOp,
        ty: Builtin,
        a: VReg,
        b: VReg,
    ) -> Result<VReg, Unsupported> {
        let (least, greatest) = match ty {
            Builtin::Fixed(_) => (i64::MIN.into(), i64::MAX.into()),
            b => b.int_range().ok_or("overflow of this type")?,
        };
        if op == BinOp::Div {
            // Only the least value divided by -1 overflows.
            let min = self.constant(least as i64);
            let minus_one = self.constant(-1);
            let is_min = self.cmp(Cond::Eq, a, min);
            let is_minus_one = self.cmp(Cond::Eq, b, minus_one);
            return Ok(self.bin(LirBin::And, is_min, is_minus_one));
        }
        let wide = matches!(ty, Builtin::Int | Builtin::UInt64 | Builtin::Fixed(_));
        if wide {
            let unsigned = ty == Builtin::UInt64;
            let op = match (op, unsigned) {
                (BinOp::Add, false) => OverflowOp::SAdd,
                (BinOp::Add, true) => OverflowOp::UAdd,
                (BinOp::Sub, false) => OverflowOp::SSub,
                (BinOp::Sub, true) => OverflowOp::USub,
                (BinOp::Mul, false) => OverflowOp::SMul,
                (BinOp::Mul, true) => OverflowOp::UMul,
                _ => return Err("overflow of this operation"),
            };
            let dst = self.reg();
            self.push(Inst::Overflow { op, dst, a, b });
            return Ok(dst);
        }
        // Narrow operands cannot overflow 64 bits; the result is then
        // compared with the type's range.
        let lir = match op {
            BinOp::Add => LirBin::Add,
            BinOp::Sub => LirBin::Sub,
            BinOp::Mul => LirBin::Mul,
            _ => return Err("overflow of this operation"),
        };
        let result = self.bin(lir, a, b);
        let min = self.constant(least as i64);
        let max = self.constant(greatest as i64);
        let below = self.cmp(Cond::Lt, result, min);
        let above = self.cmp(Cond::Gt, result, max);
        Ok(self.bin(LirBin::Or, below, above))
    }

    // Terminators.
}
