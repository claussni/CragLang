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

//! Places and collections: reading a place, finding where a field or an
//! element is, the descriptors of the types reached, and the values a
//! list, map or ref holds in its storage form.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    /// Where a call of an instance goes: through its slot, or straight to
    /// it in release code.
    pub(super) fn slot(&self, callee: InstanceKey<'db>) -> CallTarget {
        match self.direct {
            true => CallTarget::Direct(func_id(callee)),
            false => CallTarget::Slot(slot_key(self.db, self.program, callee)),
        }
    }

    /// The address of a function value's code, of the function type `ty`,
    /// which is loaded with this function.
    pub(super) fn code_addr(
        &mut self,
        code: InstanceKey<'db>,
        ty: Ty<'db>,
    ) -> Result<VReg, Unsupported> {
        let (params, returns) = self.value_words(ty)?;
        if !self.calls.contains(&code) {
            self.calls.push(code);
        }
        let dst = self.reg();
        self.push(Inst::FuncAddr {
            dst,
            func: self.slot(code),
            params,
            returns,
        });
        Ok(dst)
    }

    /// The words of the parameters, the environment's included, and of the
    /// result of a function value's code.
    fn value_words(&self, ty: Ty<'db>) -> Result<(u32, u32), Unsupported> {
        let Some((params, result, _)) = ty.as_fn(self.db) else {
            return Err("values of this type");
        };
        let mut words = 1;
        for &p in params {
            words += self.layout_of(p)?.words() as u32;
        }
        let returns = self.layout_of(result)?.words() as u32;
        if returns > 2 {
            return Err("types of parameters or results");
        }
        Ok((words, returns))
    }

    /// The words of the value at a place, borrowed: a record or union
    /// stored inline in a box is none.
    pub(super) fn read(&mut self, place: &Place<'db>) -> Result<Vec<VReg>, Unsupported> {
        match self.find(place)? {
            Found::Words(values) => Ok(values),
            Found::Stored { ptr, form, slots } if words_form(&form) => {
                Ok(self.load_stored(ptr, &slots, form.words()))
            }
            Found::Stored { .. } => Err("this place"),
        }
    }

    /// Where the value at a place is: in registers, or stored inline in a
    /// box, a record's or a union's form there.
    pub(super) fn find(&mut self, place: &Place<'db>) -> Result<Found<'db>, Unsupported> {
        let db = self.db;
        let mut ty = self.local_ty(place.local);
        let mut values = self.split_operand(&Operand::Local(place.local), ty)?;
        let mut path = &place.path[..];
        // A split local's fields are its registers.
        if let Some(form) = &self.forms[place.local.index()] {
            let (at, t, f, rest) = place_form(form, ty, path).ok_or("this place")?;
            values = values[at..at + f.words()].to_vec();
            ty = t;
            path = &place.path[place.path.len() - rest.len()..];
        }
        let mut stored: Option<(VReg, Form<'db>, Vec<Slot>)> = None;
        for step in path {
            // Within a box's storage, a field or a member is where its
            // slots say.
            if let Some((ptr, form, slots)) = stored.take() {
                let (t, f, slots) = match step {
                    Step::Field(name) => {
                        let (at, t, f) = form.field(*name).ok_or("this place")?;
                        (t, f.clone(), select(&slots, at, f.words()))
                    }
                    Step::As(t) if *t == ty => (ty, form, slots),
                    Step::As(t) => {
                        let f = form.member(*t).ok_or("this conversion")?.clone();
                        (
                            *t,
                            f,
                            member_slots(&slots, self.index(*t)).ok_or("this conversion")?,
                        )
                    }
                    _ => return Err("this place"),
                };
                ty = t;
                match f {
                    Form::Words(_) => values = self.load_stored(ptr, &slots, f.words()),
                    f => stored = Some((ptr, f, slots)),
                }
                continue;
            }
            let current = self.layout_of(ty)?;
            match step {
                Step::As(member) => {
                    let target = self.layout_of(*member)?;
                    values = match (current, target) {
                        (Layout::Union, Layout::Zero) | (Layout::Tag, Layout::Zero) => Vec::new(),
                        // Borrowed from the member box.
                        (Layout::Union, Layout::Pair | Layout::Closure) => {
                            self.member_words(values[1])
                        }
                        (Layout::Union, _) => vec![values[1]],
                        (Layout::Box, Layout::Box) => values,
                        _ => return Err("this conversion"),
                    };
                    ty = *member;
                }
                Step::Field(name) => {
                    let b = box_form(db, self.program, ty).ok_or("records of this type")?;
                    let (at, t, f) = b.form.field(*name).ok_or("records of this type")?;
                    let slots = select(&b.slots, at, f.words());
                    let ptr = word(&values)?;
                    ty = t;
                    match f {
                        Form::Words(_) => values = self.load_stored(ptr, &slots, f.words()),
                        f => stored = Some((ptr, f.clone(), slots)),
                    }
                }
                Step::Elem(_) | Step::ElemBack(_) => {
                    let list = word(&values)?;
                    let index = match step {
                        Step::Elem(i) => self.constant(i64::from(*i)),
                        Step::ElemBack(i) => {
                            let len = self.load(list, LEN_OFFSET);
                            let from_end = self.constant(i64::from(*i) + 1);
                            self.bin(LirBin::Sub, len, from_end)
                        }
                        _ => unreachable!("an element step"),
                    };
                    match self.element(list, ty, index)? {
                        Found::Words(words) => values = words,
                        Found::Stored { ptr, form, slots } => stored = Some((ptr, form, slots)),
                    }
                    ty = element_of(db, ty)?;
                }
                Step::Slice { .. } => return Err("this place"),
            }
        }
        Ok(match stored {
            Some((ptr, form, slots)) => Found::Stored { ptr, form, slots },
            None => Found::Words(values),
        })
    }

    /// The type of the value at a place.
    pub(super) fn place_ty(&self, place: &Place<'db>) -> Result<Ty<'db>, Unsupported> {
        let db = self.db;
        let mut ty = self.local_ty(place.local);
        for step in &place.path {
            ty = match step {
                Step::As(t) => *t,
                Step::Field(name) => crag_types::fields_of(db, self.program, ty)
                    .and_then(|fs| fs.into_iter().find(|(n, _)| n == name))
                    .map(|(_, t)| t)
                    .ok_or("records of this type")?,
                Step::Elem(_) | Step::ElemBack(_) => element_of(db, ty)?,
                Step::Slice { .. } => ty,
            };
        }
        Ok(ty)
    }

    /// Registers the descriptor of a record or collection type, which the
    /// runtime needs to free its boxes and to store its elements.
    pub(super) fn describe(&mut self, ty: Ty<'db>) -> Result<(), Unsupported> {
        let index = self.index(ty) as u32;
        if self.types.iter().any(|(i, _)| *i == index) {
            return Ok(());
        }
        let Some(descriptor) = type_descriptor(self.db, self.program, ty) else {
            return Err(match ty.as_builtin(self.db) {
                Some((Builtin::Map | Builtin::Set, [key, ..]))
                    if !word_keys(self.db, self.program, *key) && !is_text(self.db, *key) =>
                {
                    "maps with keys of this type"
                }
                Some(_) => "collections of this type",
                None => "records of this type",
            });
        };
        self.types.push((index, descriptor));
        Ok(())
    }

    /// Describes the types of the boxes a value of `ty` may hold, so that
    /// the runtime can build one.
    pub(super) fn describe_reachable(&mut self, ty: Ty<'db>) -> Result<(), Unsupported> {
        let (db, program) = (self.db, self.program);
        let mut seen = Vec::new();
        let mut pending = vec![ty];
        while let Some(t) = pending.pop() {
            if seen.contains(&t) {
                continue;
            }
            seen.push(t);
            if layout(db, program, t) == Some(Layout::Box) {
                self.describe(t)?;
            }
            match t.kind(db) {
                TyKind::Union(members) => pending.extend(members),
                TyKind::Builtin(_, args) => pending.extend(args),
                TyKind::Named(..) | TyKind::Record { .. } => {
                    let fields = crag_types::fields_of(db, program, t).unwrap_or_default();
                    pending.extend(fields.into_iter().map(|(_, f)| f));
                    pending.extend(crag_types::record_subtypes(db, program, t));
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Calls a runtime function with one result.
    pub(super) fn runtime(&mut self, func: RuntimeFn, args: Vec<VReg>) -> VReg {
        let dst = self.reg();
        self.push(Inst::CallRuntime {
            func,
            args,
            dsts: vec![dst],
        });
        dst
    }

    /// The words of a map or set key, padded to two: as the map stores it,
    /// packed when it takes fewer bytes than its word. A `Float` key -0.0
    /// becomes 0.0, which it equals, so that equal keys have equal words
    /// (Specification §12.2).
    pub(super) fn key(
        &mut self,
        key: &Operand<'db>,
        ty: Ty<'db>,
    ) -> Result<[VReg; 2], Unsupported> {
        let mut words = self.element_value(key, ty)?;
        if matches!(ty.as_builtin(self.db), Some((Builtin::Float, _))) {
            let zero = self.constant(0);
            words[0] = self.bin(LirBin::FAdd, words[0], zero);
        }
        Ok(self.pad(words))
    }

    /// A value's words as the two arguments of a runtime function, zero
    /// where it has fewer.
    pub(super) fn pad(&mut self, words: Vec<VReg>) -> [VReg; 2] {
        let mut out = [VReg(0); 2];
        for (k, slot) in out.iter_mut().enumerate() {
            *slot = match words.get(k) {
                Some(&w) => w,
                None => self.constant(0),
            };
        }
        out
    }

    /// The words of a value that goes into a list, map or grid, which take
    /// the operand's references: a value stored flat there packed into its
    /// storage form (`split::element_storage`), anything else in its
    /// layout's words.
    pub(super) fn element_value(
        &mut self,
        op: &Operand<'db>,
        ty: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let Some((size, slots)) = element_storage(self.db, self.program, ty) else {
            return self.operand(op, ty);
        };
        let regs = match form(self.db, self.program, ty) {
            Some(_) => self.flat_value(op, ty)?,
            None => self.operand(op, ty)?,
        };
        Ok(self.pack(&slots, size, &regs))
    }

    /// The words of a value that goes into a ref cell, which take the
    /// operand's references: a value stored flat there packed into its
    /// storage form (`split::ref_storage`), anything else in its layout's
    /// words.
    pub(super) fn ref_value(
        &mut self,
        op: &Operand<'db>,
        ty: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        match ref_storage(self.db, self.program, ty) {
            Some((size, slots)) => {
                let regs = self.flat_value(op, ty)?;
                Ok(self.pack(&slots, size, &regs))
            }
            None => self.operand(op, ty),
        }
    }

    /// An element's words as the two arguments of a runtime function: as
    /// `pad` gives them, or more than two at the address of side-stack
    /// words that hold them (`crag_abi::ElementLayout`), valid until the
    /// next element is passed.
    pub(super) fn pass_element(&mut self, words: Vec<VReg>) -> [VReg; 2] {
        if words.len() <= 2 {
            return self.pad(words);
        }
        let buffer = self.c_buffer(words.len() as u32);
        for (k, src) in words.into_iter().enumerate() {
            self.push(Inst::Store {
                src,
                addr: buffer,
                offset: 8 * k as i32,
            });
        }
        [buffer, self.constant(0)]
    }

    /// A new empty list or map of `size` bytes: its header, and zero for
    /// the rest (see `crag_abi`).
    pub(super) fn empty(&mut self, ty: Ty<'db>, size: u32) -> Result<VReg, Unsupported> {
        self.describe(ty)?;
        let ptr = self.alloc(size, self.index(ty));
        let zero = self.constant(0);
        for offset in (LEN_OFFSET..size as i32).step_by(8) {
            self.push(Inst::Store {
                src: zero,
                addr: ptr,
                offset,
            });
        }
        Ok(ptr)
    }

    /// A map or set with the entries, each a key and, for a map, a value.
    pub(super) fn map(
        &mut self,
        ty: Ty<'db>,
        key: Ty<'db>,
        value: Option<Ty<'db>>,
        entries: &[(Operand<'db>, Option<Operand<'db>>)],
    ) -> Result<VReg, Unsupported> {
        let mut words = Vec::new();
        for (k, v) in entries {
            let k = self.key(k, key)?;
            let v = match (v, value) {
                (Some(v), Some(value)) => self.element_value(v, value)?,
                _ => Vec::new(),
            };
            words.push((k, v));
        }
        let mut map = self.empty(ty, MAP_SIZE)?;
        for ([k0, k1], v) in words {
            let [v0, v1] = self.pass_element(v);
            map = self.runtime(RuntimeFn::MapInsert, vec![map, k0, k1, v0, v1]);
        }
        // A key written twice releases the value it had first.
        self.dispose();
        Ok(map)
    }

    /// Where element `index` of a list of type `ty` is: its words loaded,
    /// borrowed, or a record or union the list stores flat.
    pub(super) fn element(
        &mut self,
        list: VReg,
        ty: Ty<'db>,
        index: VReg,
    ) -> Result<Found<'db>, Unsupported> {
        let (db, program) = (self.db, self.program);
        let element = element_of(db, ty)?;
        self.describe(ty)?;
        let at = self.runtime(RuntimeFn::ListElem, vec![list, index]);
        if let Some((_, slots)) = element_storage(db, program, element) {
            let form = element_form(db, program, element).ok_or("values of this type")?;
            // A number or a tag is loaded at once, as its word.
            if words_form(&form) {
                return Ok(Found::Words(self.load_stored(at, &slots, form.words())));
            }
            return Ok(Found::Stored {
                ptr: at,
                form,
                slots,
            });
        }
        let words = self.layout_of(element)?.words();
        Ok(Found::Words(
            (0..words).map(|k| self.load(at, 8 * k as i32)).collect(),
        ))
    }

    /// The `Option` of a map's value for `dst`: the value at `at`, or
    /// `Empty` when `at` is null. A `boxed` value gets a reference of its
    /// own, which its member box takes; so does a value the map stores
    /// flat, which is boxed.
    pub(super) fn option(
        &mut self,
        dst: Local,
        at: VReg,
        value: Ty<'db>,
        ty: Ty<'db>,
        boxed: bool,
    ) -> Result<Vec<VReg>, Unsupported> {
        let db = self.db;
        // Typed as the value itself, the key is known to be there.
        if ty == value && !boxed {
            return self.map_value(dst, at, value);
        }
        let present = value.members(db);
        let empty = ty
            .members(db)
            .into_iter()
            .find(|m| !present.contains(m))
            .ok_or("this conversion")?;
        let out: Vec<VReg> = (0..self.layout_of(ty)?.words())
            .map(|_| self.reg())
            .collect();
        let (hit, miss, done) = (self.new_block(), self.new_block(), self.new_block());
        let term = Term::Branch {
            cond: at,
            then: hit,
            otherwise: miss,
        };
        self.end(term, Some(hit));
        let found = self.map_value(dst, at, value)?;
        let layout = self.layout_of(value)?;
        if boxed != matches!(layout, Layout::Pair | Layout::Closure) {
            return Err("this conversion");
        }
        if boxed {
            self.count_words(Some(layout), value, &found, Self::retain)?;
        }
        let found = self.convert(found, value, ty)?;
        self.moves(&out, found)?;
        self.end(Term::Jump(done), Some(miss));
        let nothing = self.convert(Vec::new(), empty, ty)?;
        self.moves(&out, nothing)?;
        self.end(Term::Jump(done), Some(done));
        Ok(out)
    }

    /// The words of a map's value at `at` for `dst`: borrowed, or a value
    /// stored flat in a box of its own, which a retain of `dst` takes.
    fn map_value(
        &mut self,
        dst: Local,
        at: VReg,
        value: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let (db, program) = (self.db, self.program);
        let Some((_, slots)) = element_storage(db, program, value) else {
            let words = self.layout_of(value)?.words();
            return Ok((0..words).map(|k| self.load(at, 8 * k as i32)).collect());
        };
        let f = element_form(db, program, value).ok_or("values of this type")?;
        let regs = self.load_stored(at, &slots, f.words());
        if words_form(&f) {
            return Ok(regs);
        }
        self.fresh = Some(dst);
        self.count_form(&f, value, &regs, Count::Retain)?;
        self.boxed(value, &f, &regs)
    }

    /// Copies values into registers.
    fn moves(&mut self, dsts: &[VReg], values: Vec<VReg>) -> Result<(), Unsupported> {
        if dsts.len() != values.len() {
            return Err("this conversion");
        }
        for (&dst, src) in dsts.iter().zip(values) {
            self.push(Inst::Move { dst, src });
        }
        Ok(())
    }
}
