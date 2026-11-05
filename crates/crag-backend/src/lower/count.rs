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

//! Counting and the heap: retaining and releasing what a local holds,
//! reclaiming a box whose count dropped, dispose code, and allocation
//! inline with the runtime's slow path.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    /// Retains or releases the box a local holds, if it holds one.
    pub(super) fn count(&mut self, local: Local, how: Count) -> Result<(), Unsupported> {
        let regs = self.locals[local.index()].clone();
        let ty = self.local_ty(local);
        let form = match self.forms[local.index()].clone() {
            Some(form) => form,
            None => match self.layouts[local.index()] {
                Some(layout) => Form::Words(layout),
                None => return Ok(()),
            },
        };
        self.count_form(&form, ty, &regs, how)
    }

    /// Gives up a record's reference as a release does, but takes apart a
    /// box that no one else holds (Plan §11.10.1): the kept fields'
    /// references pass to the locals that read them, which have the
    /// field's words as the record holds them, the other fields are
    /// released, and the box, empty, goes to the token or is freed. A
    /// shared box gives each kept local a reference of its own, and the
    /// token a static empty box.
    pub(super) fn reclaim(
        &mut self,
        local: Local,
        token: Option<Local>,
        kept: &[(Name<'db>, Local)],
    ) -> Result<(), Unsupported> {
        let ty = self.local_ty(local);
        let token = match token {
            Some(t) => {
                let empty = self.empty_box();
                let reg = word(&self.locals[t.index()])?;
                self.push(Inst::Move {
                    dst: reg,
                    src: empty,
                });
                Some((reg, self.local_ty(t)))
            }
            None => None,
        };
        let split = self.forms[local.index()].clone();
        let b = box_form(self.db, self.program, ty);
        let holder = match (&split, &b) {
            (Some(f), _) => f.clone(),
            (None, Some(b)) => b.form.clone(),
            (None, None) => return Err("records of this type"),
        };
        let mut moved = Vec::new();
        for &(name, k) in kept {
            // A read that gave a value of its own needs no reference.
            if let Some(i) = self.owned.iter().position(|&o| o == k) {
                self.owned.swap_remove(i);
                continue;
            }
            let own = match self.forms[k.index()].clone() {
                Some(f) => Some(f),
                None => self.layouts[k.index()].map(Form::Words),
            };
            let field = holder.field(name).map(|(_, _, f)| f.clone());
            match own.is_some() && own == field {
                true => moved.push(name),
                false => self.count(k, Count::Retain)?,
            }
        }
        let retain_moved = |this: &mut Self| -> Result<(), Unsupported> {
            for &(name, k) in kept {
                if moved.contains(&name) {
                    this.count(k, Count::Retain)?;
                }
            }
            Ok(())
        };
        // A split record's registers hold its fields' references alone.
        if split.is_some() {
            let regs = self.locals[local.index()].clone();
            return self.release_fields(&holder, &regs, &moved);
        }
        let b = b.expect("a box form");
        let ptr = word(&self.locals[local.index()])?;
        // Fields the runtime closes when it frees the box stay with it.
        let plain = match type_descriptor(self.db, self.program, ty) {
            Some(TypeDescriptor::Record { counted, dispose }) => {
                dispose.is_none()
                    && counted.iter().all(|f| {
                        matches!(
                            f,
                            CountedField::Box(_)
                                | CountedField::Union { .. }
                                | CountedField::Guarded { .. }
                        )
                    })
            }
            _ => false,
        };
        if !plain || b.dispose.is_some() {
            retain_moved(self)?;
            self.release(ptr);
            return Ok(());
        }
        // A token takes only a box of its record's size class.
        let token = token.filter(|&(_, t)| {
            box_form(self.db, self.program, t).is_some_and(|t| {
                size_class(t.size).is_some() && size_class(t.size) == size_class(b.size)
            })
        });
        // Without a box to keep, taking it apart pays only when no field
        // is left to release: the runtime frees a box and its fields at
        // once.
        let Form::Fields(fields) = &b.form else {
            return Err("records of this type");
        };
        let left = fields
            .iter()
            .any(|(name, _, f)| !moved.contains(name) && counted_form(f));
        if token.is_none() && (left || moved.is_empty()) {
            retain_moved(self)?;
            self.release(ptr);
            return Ok(());
        }
        let (check, claim, shared, done) = (
            self.new_block(),
            self.new_block(),
            self.new_block(),
            self.new_block(),
        );
        // A count of one is the only reference; a static box's is negative.
        let count = self.load(ptr, COUNT_OFFSET);
        let one = self.constant(1);
        let unique = self.cmp(Cond::Eq, count, one);
        self.end(
            Term::Branch {
                cond: unique,
                then: check,
                otherwise: shared,
            },
            Some(check),
        );
        // A local of a record type may hold a subtype's larger box.
        let header = self.load(ptr, TYPE_INDEX_OFFSET);
        let index = self.constant(self.index(ty));
        let exact = self.cmp(Cond::Eq, header, index);
        self.end(
            Term::Branch {
                cond: exact,
                then: claim,
                otherwise: shared,
            },
            Some(claim),
        );
        let regs = self.load_stored(ptr, &b.slots, b.form.words());
        self.release_fields(&b.form, &regs, &moved)?;
        // An empty box holds no references: freed by a trap, it is freed
        // as a buffer is.
        let empty = self.constant(BUFFER_HEADER as i64);
        self.push(Inst::Store {
            src: empty,
            addr: ptr,
            offset: TYPE_INDEX_OFFSET,
        });
        match token {
            Some((t, _)) => self.push(Inst::Move { dst: t, src: ptr }),
            None => self.release(ptr),
        }
        self.end(Term::Jump(done), Some(shared));
        retain_moved(self)?;
        self.release(ptr);
        self.end(Term::Jump(done), Some(done));
        Ok(())
    }

    /// Releases the fields of a record's registers in a `Form::Fields`,
    /// but those `moved`.
    fn release_fields(
        &mut self,
        form: &Form<'db>,
        regs: &[VReg],
        moved: &[Name<'db>],
    ) -> Result<(), Unsupported> {
        let Form::Fields(fields) = form else {
            return Err("records of this type");
        };
        let mut at = 0;
        for (name, t, f) in fields {
            let n = f.words();
            if !moved.contains(name) {
                self.count_form(f, *t, &regs[at..at + n], Count::Release)?;
            }
            at += n;
        }
        Ok(())
    }

    /// A static empty box: a token that holds no box to reuse.
    fn empty_box(&mut self) -> VReg {
        let mut bytes = Vec::with_capacity(16);
        bytes.extend(STATIC_COUNT.to_le_bytes());
        bytes.extend(BUFFER_HEADER.to_le_bytes());
        let data = match self.data.iter().position(|d| *d == bytes) {
            Some(d) => d,
            None => {
                self.data.push(bytes);
                self.data.len() - 1
            }
        };
        let ptr = self.reg();
        self.push(Inst::DataAddr {
            dst: ptr,
            data: data as u32,
        });
        ptr
    }

    /// Retains or releases what the registers of a split value hold: each
    /// field's, and a union's member's by its type index.
    pub(super) fn count_form(
        &mut self,
        f: &Form<'db>,
        ty: Ty<'db>,
        regs: &[VReg],
        how: Count,
    ) -> Result<(), Unsupported> {
        match f {
            Form::Words(l) => {
                let op = match how {
                    Count::Retain => Self::retain,
                    // A long chain of boxes is freed between fibers (§13.5).
                    Count::Release if deferred(self.db, self.program, ty) => Self::release_deferred,
                    Count::Release => Self::release,
                };
                self.count_words(Some(*l), ty, regs, op)
            }
            Form::Fields(fields) => {
                let mut at = 0;
                for (_, t, inner) in fields {
                    let n = inner.words();
                    self.count_form(inner, *t, &regs[at..at + n], how)?;
                    at += n;
                }
                Ok(())
            }
            Form::Union(members) => {
                let done = self.new_block();
                for (m, inner) in members {
                    if !counted_form(inner) {
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
                    self.count_form(inner, *m, &regs[1..1 + inner.words()], how)?;
                    self.end(Term::Jump(done), Some(next));
                }
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
        }
    }

    /// Retains or releases the box the words of a value hold, if they hold
    /// one.
    pub(super) fn count_words(
        &mut self,
        layout: Option<Layout>,
        ty: Ty<'db>,
        regs: &[VReg],
        op: fn(&mut Self, VReg),
    ) -> Result<(), Unsupported> {
        match layout {
            Some(Layout::Box) => {
                op(self, regs[0]);
                Ok(())
            }
            Some(Layout::Union) => {
                let boxed =
                    boxed_indices(self.db, self.program, ty).ok_or("values of this type")?;
                let boxed: Vec<i64> = boxed.into_iter().map(i64::from).collect();
                let (call, done) = (self.new_block(), self.new_block());
                self.test_index(regs[0], &boxed, call, done);
                self.current = (call.0 as usize, Vec::new());
                op(self, regs[1]);
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            // A function value without an environment has a null one.
            Some(Layout::Closure) => {
                let (call, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: regs[1],
                        then: call,
                        otherwise: done,
                    },
                    Some(call),
                );
                op(self, regs[1]);
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            // A buffer, unless the bytes are inline.
            Some(Layout::Pair) => {
                let one = self.constant(1);
                let inline = self.bin(LirBin::And, regs[0], one);
                let (call, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: inline,
                        then: done,
                        otherwise: call,
                    },
                    Some(call),
                );
                op(self, regs[0]);
                self.end(Term::Jump(done), Some(done));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Adds a reference to a box, unless it is static (see `crag_abi`).
    pub(super) fn retain(&mut self, ptr: VReg) {
        let (add, done) = (self.new_block(), self.new_block());
        let counted = self.counted(ptr);
        self.end(
            Term::Branch {
                cond: counted,
                then: add,
                otherwise: done,
            },
            Some(add),
        );
        let one = self.constant(1);
        self.atomic_add(ptr, one);
        self.end(Term::Jump(done), Some(done));
    }

    /// Gives up a reference to a box, unless it is static, and has the
    /// runtime free it with the last.
    pub(super) fn release(&mut self, ptr: VReg) {
        self.release_by(ptr, RuntimeFn::Release);
    }

    /// Gives up a reference as `release` does, but has the runtime free
    /// the box with the last through deferred teardown, a bounded part at
    /// once and the rest between fibers (Plan §11.7.12).
    fn release_deferred(&mut self, ptr: VReg) {
        self.release_by(ptr, RuntimeFn::ReleaseDeferred);
    }

    fn release_by(&mut self, ptr: VReg, func: RuntimeFn) {
        let (sub, free, done) = (self.new_block(), self.new_block(), self.new_block());
        let counted = self.counted(ptr);
        self.end(
            Term::Branch {
                cond: counted,
                then: sub,
                otherwise: done,
            },
            Some(sub),
        );
        let minus_one = self.constant(-1);
        let before = self.atomic_add(ptr, minus_one);
        let one = self.constant(1);
        let last = self.cmp(Cond::Eq, before, one);
        self.end(
            Term::Branch {
                cond: last,
                then: free,
                otherwise: done,
            },
            Some(free),
        );
        self.push(Inst::CallRuntime {
            func,
            args: vec![ptr],
            dsts: Vec::new(),
        });
        self.dispose();
        self.end(Term::Jump(done), Some(done));
    }

    /// Runs the dispose code of each box the runtime queued, until none is
    /// left (§11.6.11): after a release that may have freed boxes, so that
    /// each handler runs at the drop, on the fiber that dropped the box.
    pub(super) fn dispose(&mut self) {
        let (next, run, done) = (self.new_block(), self.new_block(), self.new_block());
        self.end(Term::Jump(next), Some(next));
        let [ptr, code] = self.runtime2(RuntimeFn::Disposal, Vec::new())[..] else {
            unreachable!("two words");
        };
        let zero = self.constant(0);
        let none = self.cmp(Cond::Eq, ptr, zero);
        self.end(
            Term::Branch {
                cond: none,
                then: done,
                otherwise: run,
            },
            Some(run),
        );
        self.push(Inst::CallIndirect {
            callee: code,
            args: vec![ptr],
            dsts: Vec::new(),
        });
        self.end(Term::Jump(next), Some(done));
    }

    /// Whether a box is counted: its count is not negative, which a static
    /// box's is.
    fn counted(&mut self, ptr: VReg) -> VReg {
        let count = self.load(ptr, COUNT_OFFSET);
        let zero = self.constant(0);
        self.cmp(Cond::Ge, count, zero)
    }

    /// Adds `value` to a box's count atomically; the count before.
    fn atomic_add(&mut self, ptr: VReg, value: VReg) -> VReg {
        let dst = self.reg();
        self.push(Inst::AtomicAdd {
            dst,
            addr: ptr,
            offset: COUNT_OFFSET,
            value,
        });
        dst
    }

    /// A new box as `alloc` makes it, in the empty box a reclaim kept in
    /// `token` when it holds one, whose count is one already; a static box
    /// holds none.
    pub(super) fn alloc_in(&mut self, token: VReg, size: u32, index: i64) -> VReg {
        let ptr = self.reg();
        let (reuse, fresh, done) = (self.new_block(), self.new_block(), self.new_block());
        let counted = self.counted(token);
        self.end(
            Term::Branch {
                cond: counted,
                then: reuse,
                otherwise: fresh,
            },
            Some(reuse),
        );
        let header = self.constant(index);
        self.push(Inst::Store {
            src: header,
            addr: token,
            offset: TYPE_INDEX_OFFSET,
        });
        self.push(Inst::Move {
            dst: ptr,
            src: token,
        });
        self.end(Term::Jump(done), Some(fresh));
        let new = self.alloc(size, index);
        self.push(Inst::Move { dst: ptr, src: new });
        self.end(Term::Jump(done), Some(done));
        ptr
    }

    /// A new box of `size` bytes with a count of one and the type index in
    /// its header: popped inline from the free list of the heap's current
    /// page of its size class, or from `rt_alloc` when that list is empty
    /// or the box is too large for a class (see `crag_abi`).
    pub(super) fn alloc(&mut self, size: u32, index: i64) -> VReg {
        let ptr = self.reg();
        let size_reg = self.constant(i64::from(size));
        let index = self.constant(index);
        let call = |this: &mut Self| {
            this.push(Inst::CallRuntime {
                func: RuntimeFn::Alloc,
                args: vec![size_reg, index],
                dsts: vec![ptr],
            })
        };
        let Some(class) = size_class(size) else {
            call(self);
            return ptr;
        };
        let ctx = self.reg();
        self.push(Inst::Context { dst: ctx });
        let heap = self.load(ctx, HEAP_OFFSET);
        let page = self.load(heap, 8 * class as i32);
        let block = self.load(page, PAGE_FREE_OFFSET);
        let (fast, slow, done) = (self.new_block(), self.new_block(), self.new_block());
        self.end(
            Term::Branch {
                cond: block,
                then: fast,
                otherwise: slow,
            },
            Some(fast),
        );
        let next = self.load(block, 0);
        self.push(Inst::Store {
            src: next,
            addr: page,
            offset: PAGE_FREE_OFFSET,
        });
        let used = self.load(page, PAGE_USED_OFFSET);
        let one = self.constant(1);
        let used = self.bin(LirBin::Add, used, one);
        self.push(Inst::Store {
            src: used,
            addr: page,
            offset: PAGE_USED_OFFSET,
        });
        self.push(Inst::Store {
            src: one,
            addr: block,
            offset: COUNT_OFFSET,
        });
        self.push(Inst::Store {
            src: index,
            addr: block,
            offset: TYPE_INDEX_OFFSET,
        });
        self.push(Inst::Move {
            dst: ptr,
            src: block,
        });
        self.end(Term::Jump(done), Some(slow));
        call(self);
        self.end(Term::Jump(done), Some(done));
        ptr
    }

    pub(super) fn load(&mut self, addr: VReg, offset: i32) -> VReg {
        let dst = self.reg();
        self.push(Inst::Load { dst, addr, offset });
        dst
    }

    /// Ends the block with a test whether an index is one of `indices`.
    pub(super) fn test_index(
        &mut self,
        index: VReg,
        indices: &[i64],
        hit: LirBlockId,
        miss: LirBlockId,
    ) {
        for (k, &i) in indices.iter().enumerate() {
            let c = self.constant(i);
            let same = self.cmp(Cond::Eq, index, c);
            let next = match k + 1 == indices.len() {
                true => miss,
                false => self.new_block(),
            };
            let term = Term::Branch {
                cond: same,
                then: hit,
                otherwise: next,
            };
            let more = (next != miss).then_some(next);
            self.end(term, more);
        }
        if indices.is_empty() {
            self.end(Term::Jump(miss), None);
        }
    }

    /// The words a read gives a local, from where the value is: `from` is
    /// its form when it is split in registers. A record or union stored
    /// flat is loaded into a split local, borrowed, and boxed for one that
    /// is not split, a value of its own, as is a split union's member.
    pub(super) fn take(
        &mut self,
        dst: Local,
        found: Found<'db>,
        from: Option<Form<'db>>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let ty = self.local_ty(dst);
        let (values, from) = match found {
            Found::Words(values) => (values, from),
            Found::Stored { ptr, form, slots } => {
                (self.load_stored(ptr, &slots, form.words()), Some(form))
            }
        };
        match (self.forms[dst.index()].clone(), from) {
            (Some(form), None) => self.unboxed(ty, &form, &values),
            // A cycle's edge has a form of its own.
            (Some(form), Some(f)) if form != f && words_form(&f) => {
                self.unboxed(ty, &form, &values)
            }
            (Some(form), Some(f)) if form != f => {
                self.fresh = Some(dst);
                self.count_form(&f, ty, &values, Count::Retain)?;
                let words = self.boxed(ty, &f, &values)?;
                self.owned_fields(ty, &form, &words)
            }
            (None, Some(f)) if !words_form(&f) => {
                self.fresh = Some(dst);
                self.count_form(&f, ty, &values, Count::Retain)?;
                self.boxed(ty, &f, &values)
            }
            _ => Ok(values),
        }
    }
}
