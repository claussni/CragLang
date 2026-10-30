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

//! Flat locals (Implementation Plan §11.10.10): a local of a flat record
//! type that never needs a box is kept in registers, one value per field,
//! instead of in a box of its own.
//!
//! A split local's register form is its fields' in the order of their
//! storage form, a field of a flat record type split in turn and any other
//! field in the words of its layout (`layout::layout`). Building such a
//! record allocates nothing and reading a field picks its registers. A
//! flat union with a member that is a flat record splits too: its
//! member's type index, then the member's words in its own form, as many
//! as the widest member's. Within a split value, every union with a
//! payload splits that way, a string member too, and a cycle's edge
//! holds its box. Where a union meets a box, it has its layout's two
//! words, the member boxed.
//!
//! A split local is used in registers by field reads, type tests,
//! counting, steps, and copies into another split local or a field of
//! one. A use that gives it away to a call, a return or a box boxes it
//! there, which takes its fields' references; a use that only borrows it
//! where it must be in a box keeps it boxed. A record read from a box, a
//! field or an element, is loaded into a split local field by field. A
//! list, map or grid stores a flat record or union in its storage form
//! too, and a sized integer or a union of tags in its bytes
//! (`element_storage`): it goes in packed from registers and comes out
//! loaded into them.
//!
//! Splitting makes no more boxes than there are: a local that is boxed
//! where it escapes must not be retained, which a second use needs, nor
//! come out of a box, which it could pass on as it is. A record a call
//! returns, or that is converted from a union, stays in its box for now.
//!
//! A flat record passes to a parameter of a function's body by value, in
//! its storage form packed into at most four words (Compiler Architecture
//! §A11.4.6): the parameter is split, and an argument is packed from its
//! registers or loaded from its box. A function's body with parameters
//! returns a flat record by value too: in at most two words, or written
//! to a buffer the caller pushes on its side stack, which a tail call
//! passes on; a tail call to code that returns otherwise becomes a call.
//! A flat union passes the same way: its member's local tag, or for a
//! `T | Empty` the niche of `T`, and the member's storage form. The
//! values of the code that function values, the runtime and the host call
//! still pass in their box.
//!
//! With `CRAG_FLAT=0` in the environment no local is split and every
//! record passes in its box.

use std::sync::OnceLock;

use crag_db::Db;
use crag_hir::{ItemKind, Name, Owner, Program, c_function};
use crag_mir::{
    ClosurePlacement, Entry, InstanceKey, Intrinsic, MirBody, Operand, Place, Rvalue, Statement,
    Terminator, Tier, mir,
};
use crag_types::{Builtin, Step, Ty, TyKind, TypeDefKind, lifecycle_handler, type_def};

use crate::boxes::stored_form;
use crate::flat::{self, LayoutClass, NicheKind, TagPlace};
use crate::layout::{self, Layout, type_index};

/// Whether flat layouts are on: unless `CRAG_FLAT` is `0`, read once.
pub fn flat_layouts() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("CRAG_FLAT").map_or(true, |v| v != "0"))
}

/// The register form of a value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Form<'db> {
    /// The words of its layout.
    Words(Layout),
    /// A flat record's fields, in storage order, each in its own form.
    Fields(Vec<(Name<'db>, Ty<'db>, Form<'db>)>),
    /// A union with a member that is a flat record: the type index of the
    /// value's member, then the member's words in its own form, as many as
    /// the widest member's.
    Union(Vec<(Ty<'db>, Form<'db>)>),
}

impl<'db> Form<'db> {
    pub fn words(&self) -> usize {
        match self {
            Form::Words(l) => l.words(),
            Form::Fields(fields) => fields.iter().map(|(_, _, f)| f.words()).sum(),
            Form::Union(members) => 1 + members.iter().map(|(_, f)| f.words()).max().unwrap_or(0),
        }
    }

    /// The values that are not records split further, words or unions,
    /// with their first word's index, in order.
    pub fn leaves(&self, ty: Ty<'db>) -> Vec<(usize, &Form<'db>, Ty<'db>)> {
        let mut out = Vec::new();
        self.leaves_into(ty, 0, &mut out);
        out
    }

    fn leaves_into<'a>(
        &'a self,
        ty: Ty<'db>,
        at: usize,
        out: &mut Vec<(usize, &'a Form<'db>, Ty<'db>)>,
    ) {
        match self {
            Form::Words(_) | Form::Union(_) => out.push((at, self, ty)),
            Form::Fields(fields) => {
                let mut at = at;
                for (_, t, f) in fields {
                    f.leaves_into(*t, at, out);
                    at += f.words();
                }
            }
        }
    }

    /// A member's form, whose words start at the second.
    pub fn member(&self, ty: Ty<'db>) -> Option<&Form<'db>> {
        let Form::Union(members) = self else {
            return None;
        };
        members.iter().find(|(m, _)| *m == ty).map(|(_, f)| f)
    }

    /// A field's first word, type and form.
    pub fn field(&self, name: Name<'db>) -> Option<(usize, Ty<'db>, &Form<'db>)> {
        let Form::Fields(fields) = self else {
            return None;
        };
        let mut at = 0;
        for (n, t, f) in fields {
            if *n == name {
                return Some((at, *t, f));
            }
            at += f.words();
        }
        None
    }
}

/// The register form of a split value of `ty`: none unless it is a flat
/// record, or a flat union with a member that is one. Within it, flat
/// records are split too, and so are unions with a payload: a field or a
/// member that is the edge of a cycle holds a box.
pub fn form<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Form<'db>> {
    if let TyKind::Union(_) = ty.kind(db) {
        let flat = flat::layout(db, program, ty).as_ref()?;
        if flat.is_boxed() {
            return None;
        }
        let f = union_form(db, program, flat)?;
        let Form::Union(members) = &f else {
            return None;
        };
        let records = members.iter().any(|(_, m)| matches!(m, Form::Fields(_)));
        return records.then_some(f);
    }
    let record = match ty.kind(db) {
        TyKind::Named(item, _) => {
            matches!(
                type_def(db, program, *item).kind,
                TypeDefKind::Record { .. }
            )
        }
        TyKind::Record { open, fields } => !open && !fields.is_empty(),
        _ => false,
    };
    if !record {
        return None;
    }
    let flat = flat::layout(db, program, ty).as_ref()?;
    if let LayoutClass::Boxed(_) = flat.class {
        return None;
    }
    fields_form(db, program, &flat.fields)
}

/// The fields of a record, each in its form inside a split value.
pub(crate) fn fields_form<'db>(
    db: &'db dyn Db,
    program: Program,
    places: &[flat::FieldPlace<'db>],
) -> Option<Form<'db>> {
    let mut fields = Vec::new();
    for place in places {
        let inner = match &place.edges {
            Some(l) if l.union.is_some() => union_form(db, program, l)?,
            Some(_) => Form::Words(Layout::Box),
            None => inner_form(db, program, place.ty)?,
        };
        fields.push((place.name, place.ty, inner));
    }
    Some(Form::Fields(fields))
}

/// The form of a value inside a split one: a flat record split, a union
/// with a payload as its member's type index and the member's words, and
/// anything else as the words of its layout.
pub fn inner_form<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Form<'db>> {
    if let Some(f) = form(db, program, ty) {
        return Some(f);
    }
    let l = layout::layout(db, program, ty)?;
    if l == Layout::Union
        && let Some(flat) = flat::layout(db, program, ty)
        && flat.union.is_some()
    {
        return union_form(db, program, flat);
    }
    Some(Form::Words(l))
}

/// A union's members, each in its form inside a split value; a member
/// that is the edge of a cycle holds a box.
fn union_form<'db>(
    db: &'db dyn Db,
    program: Program,
    flat: &flat::Layout<'db>,
) -> Option<Form<'db>> {
    let mut members = Vec::new();
    for place in &flat.union.as_ref()?.members {
        let inner = match place.boxed {
            Some(_) => Form::Words(Layout::Box),
            None => inner_form(db, program, place.ty)?,
        };
        members.push((place.ty, inner));
    }
    Some(Form::Union(members))
}

/// The form of the value a place reaches when the local is split: the
/// first word, type and form, and the steps left once a step leaves the
/// split part. None for a step the split part does not have.
pub fn place_form<'a, 'db>(
    root: &'a Form<'db>,
    ty: Ty<'db>,
    path: &'a [Step<'db>],
) -> Option<(usize, Ty<'db>, &'a Form<'db>, &'a [Step<'db>])> {
    let (mut at, mut ty, mut form) = (0, ty, root);
    for (i, step) in path.iter().enumerate() {
        if let Form::Words(_) = form {
            return Some((at, ty, form, &path[i..]));
        }
        match step {
            Step::Field(name) => {
                let (offset, t, f) = form.field(*name)?;
                at += offset;
                ty = t;
                form = f;
            }
            Step::As(t) if *t == ty => {}
            // A member's words follow the union's type index.
            Step::As(t) => {
                form = form.member(*t)?;
                at += 1;
                ty = *t;
            }
            _ => return None,
        }
    }
    Some((at, ty, form, &[]))
}

/// Marks the locals of a body that code generation keeps split (see the
/// module's comment).
pub fn scalar_replace<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    body: &mut MirBody<'db>,
) {
    if !flat_layouts() {
        return;
    }
    // A parameter is split when it passes by value.
    let params = flat_params(db, program, instance);
    let first = body.params.max(usize::from(body.env));
    let forms: Vec<Option<Form<'db>>> = body
        .locals
        .iter()
        .enumerate()
        .map(|(i, l)| match i < first && params.get(i) != Some(&true) {
            true => None,
            false => form(db, program, l.ty),
        })
        .collect();
    let mut split: Vec<bool> = forms.iter().map(Option::is_some).collect();
    let mut retained = vec![false; split.len()];
    for block in &body.blocks {
        for statement in &block.statements {
            if let Statement::Retain(l) = statement {
                retained[l.index()] = true;
            }
        }
    }
    // Keeping one local boxed may keep others boxed: those it is copied
    // from or into.
    loop {
        let n = split.len();
        let mut check = Check {
            db,
            program,
            gives_flat: flat_result(db, program, instance).is_some(),
            body,
            forms: &forms,
            split: &split,
            keep: vec![false; n],
            escapes: vec![false; n],
            from_box: vec![false; n],
        };
        for block in &body.blocks {
            for statement in &block.statements {
                check.statement(statement);
            }
            check.terminator(&block.terminator);
        }
        let Check {
            keep,
            escapes,
            from_box,
            ..
        } = check;
        let mut changed = false;
        for (i, s) in split.iter_mut().enumerate() {
            // A local boxed where it escapes must not be boxed twice: not
            // when it is retained to be used again, and not when its value
            // came out of a box, which it could pass on as it is.
            let twice = escapes[i] && (retained[i] || from_box[i]);
            if *s && (keep[i] || twice) {
                *s = false;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (decl, s) in body.locals.iter_mut().zip(split) {
        decl.split = s;
    }
}

/// Finds the uses of locals that need them in a box.
struct Check<'a, 'db> {
    db: &'db dyn Db,
    program: Program,
    /// Whether the body gives its result by value.
    gives_flat: bool,
    body: &'a MirBody<'db>,
    forms: &'a [Option<Form<'db>>],
    split: &'a [bool],
    /// Locals that must stay boxed.
    keep: Vec<bool>,
    /// Locals a use gives away into a box, which code generation makes.
    escapes: Vec<bool>,
    /// Locals assigned a record borrowed from a box, read from it.
    from_box: Vec<bool>,
}

impl<'db> Check<'_, 'db> {
    /// The arguments of a call: one that passes by value takes a split
    /// local's registers, or is loaded from its box.
    fn arguments(&mut self, func: InstanceKey<'db>, args: &[Operand<'db>]) {
        let flat = flat_params(self.db, self.program, func);
        for (k, o) in args.iter().enumerate() {
            if flat.get(k) != Some(&true) {
                self.consumed(o);
            }
        }
    }

    /// The use gives the local's value away: a split local is boxed.
    fn consumed(&mut self, op: &Operand<'db>) {
        if let Operand::Local(l) = op {
            self.escapes[l.index()] = true;
        }
    }

    /// The use borrows the local's value where it must be in a box.
    fn borrowed(&mut self, op: &Operand<'db>) {
        if let Operand::Local(l) = op {
            self.keep[l.index()] = true;
        }
    }

    /// Whether the value at the place is in registers when its local is
    /// split, and whether it is a split record there.
    fn place(&self, place: &Place<'db>) -> Option<bool> {
        let form = self.forms[place.local.index()].as_ref()?;
        let ty = self.body.locals[place.local.index()].ty;
        let (_, _, form, _) = place_form(form, ty, &place.path)?;
        Some(matches!(form, Form::Fields(_) | Form::Union(_)))
    }

    /// Whether the value at the place is a record or a union a box
    /// stores inline.
    fn inline(&self, place: &Place<'db>) -> bool {
        let mut ty = self.body.locals[place.local.index()].ty;
        let mut path = &place.path[..];
        if let Some(form) = &self.forms[place.local.index()]
            && self.split[place.local.index()]
        {
            let Some((_, t, _, rest)) = place_form(form, ty, path) else {
                return false;
            };
            ty = t;
            path = rest;
        }
        stored_form(self.db, self.program, ty, path).is_some()
    }

    /// Whether the value at the place is a union split in registers.
    fn union_at(&self, place: &Place<'db>) -> bool {
        let Some(form) = self.forms[place.local.index()].as_ref() else {
            return false;
        };
        let ty = self.body.locals[place.local.index()].ty;
        matches!(
            place_form(form, ty, &place.path),
            Some((_, _, Form::Union(_), _))
        )
    }

    /// The form of a member of a split union that a value of `from` is.
    fn member(&self, union: &Form<'db>, from: Ty<'db>, to: Ty<'db>) -> Option<Form<'db>> {
        let members = to.members(self.db);
        let member = match members.contains(&from) {
            true => from,
            false => members
                .into_iter()
                .find(|&m| crag_types::is_subtype(self.db, self.program, from, m))?,
        };
        union.member(member).cloned()
    }

    /// A place read that must give words, not a split record.
    fn place_words(&mut self, place: &Place<'db>) {
        if self.forms[place.local.index()].is_some() && self.place(place) != Some(false) {
            self.keep[place.local.index()] = true;
        }
    }

    fn statement(&mut self, statement: &Statement<'db>) {
        let Statement::Assign(dst, rvalue) = statement else {
            return;
        };
        let into_split = self.split[dst.index()];
        let mut defines = false;
        match rvalue {
            Rvalue::Use(Operand::Local(src)) if into_split && self.split[src.index()] => {
                defines = true;
            }
            Rvalue::Read(place) => {
                let source = place.local.index();
                match (self.split[source], self.place(place)) {
                    // A split record goes into a split local.
                    (true, Some(true)) if into_split && self.split[source] => defines = true,
                    // A split union goes into one that is not with its
                    // member boxed.
                    (true, Some(true)) if !into_split && self.union_at(place) => {}
                    // Words, or a record read from its box or from where
                    // a box stores it inline, which is not a box of its own.
                    (false, _) | (true, Some(false)) => {
                        if into_split {
                            defines = true;
                            self.from_box[dst.index()] = !self.inline(place);
                        }
                    }
                    _ => self.keep[source] = true,
                }
            }
            Rvalue::Index { list, index } => {
                self.place_words(list);
                self.borrowed(index);
                if into_split {
                    defines = true;
                    // An element stored flat is no box of its own.
                    let ty = self.body.locals[dst.index()].ty;
                    self.from_box[dst.index()] =
                        element_storage(self.db, self.program, ty).is_none();
                }
            }
            // A ref's value is loaded as an element is.
            Rvalue::Intrinsic(Intrinsic::RefValue, _) if into_split => {
                defines = true;
                let ty = self.body.locals[dst.index()].ty;
                self.from_box[dst.index()] = ref_storage(self.db, self.program, ty).is_none();
            }
            Rvalue::Record {
                fields,
                dispose: None,
                ..
            } if into_split => {
                defines = true;
                let form = self.forms[dst.index()].as_ref();
                for (name, op) in fields {
                    // A split record or union goes into a field split in
                    // turn; a boxed union's member is loaded.
                    let field = form.and_then(|f| f.field(*name));
                    match (op, field) {
                        (Operand::Local(l), Some((_, _, Form::Fields(_) | Form::Union(_))))
                            if self.split[l.index()] => {}
                        (_, Some((_, _, Form::Fields(_)))) => {
                            self.consumed(op);
                            self.keep[dst.index()] = true;
                        }
                        _ => self.consumed(op),
                    }
                }
            }
            Rvalue::Convert(o) => self.convert(*dst, o, into_split, &mut defines),
            Rvalue::Use(o) | Rvalue::FnValue { env: o, .. } => self.consumed(o),
            Rvalue::Record { fields, .. } => fields.iter().for_each(|(_, o)| self.consumed(o)),
            Rvalue::List(items) => items.iter().for_each(|o| self.consumed(o)),
            Rvalue::Map(entries) => {
                for (k, v) in entries {
                    self.consumed(k);
                    self.consumed(v);
                }
            }
            Rvalue::Intrinsic(intrinsic, args) => {
                for (k, o) in args.iter().enumerate() {
                    match intrinsic.consumes(k) {
                        true => self.consumed(o),
                        false => self.borrowed(o),
                    }
                }
            }
            Rvalue::Closure {
                captures,
                placement,
                ..
            } => {
                for o in captures {
                    match placement {
                        ClosurePlacement::Heap => self.consumed(o),
                        ClosurePlacement::SideStack => self.borrowed(o),
                    }
                }
            }
            Rvalue::Len(place) | Rvalue::Slice { list: place, .. } => self.place_words(place),
            Rvalue::MapGet { map, key, .. } => {
                self.place_words(map);
                self.borrowed(key);
            }
            Rvalue::FloatOverflow(_) => {}
            Rvalue::Binary { .. }
            | Rvalue::Overflows { .. }
            | Rvalue::Compare { .. }
            | Rvalue::Cast { .. }
            | Rvalue::Concat(_) => {
                let mut rvalue = rvalue.clone();
                for l in rvalue.locals_mut() {
                    self.keep[l.index()] = true;
                }
            }
        }
        if !defines {
            self.keep[dst.index()] = true;
        }
    }

    /// A conversion into a split union, of a member or the union itself,
    /// or out of one, to a member a test established.
    fn convert(
        &mut self,
        dst: crag_mir::Local,
        op: &Operand<'db>,
        into_split: bool,
        defines: &mut bool,
    ) {
        let to = self.body.locals[dst.index()].ty;
        let from = match op {
            Operand::Local(l) => self.body.locals[l.index()].ty,
            Operand::Const(_) => to,
        };
        if into_split && let Some(union @ Form::Union(_)) = self.forms[dst.index()].clone() {
            match op {
                // A tag goes in as its type index.
                Operand::Const(_) => *defines = true,
                Operand::Local(l) if from == to => {
                    *defines = self.split[l.index()];
                }
                Operand::Local(l) => match self.member(&union, from, to) {
                    Some(Form::Words(_)) => *defines = true,
                    Some(_) if self.split[l.index()] => *defines = true,
                    _ => self.consumed(op),
                },
            }
            return;
        }
        if let Operand::Local(l) = op
            && self.split[l.index()]
            && let Some(union @ Form::Union(_)) = &self.forms[l.index()]
            && let Some(member) = union.member(to)
        {
            match member {
                // A member's words, as they are.
                Form::Words(_) => {}
                Form::Fields(_) | Form::Union(_) if into_split => *defines = true,
                // Boxed, which gives the union's references to the box.
                _ => self.escapes[l.index()] = true,
            }
            return;
        }
        self.consumed(op);
    }

    fn terminator(&mut self, terminator: &Terminator<'db>) {
        match terminator {
            Terminator::Switch { place, .. } => {
                // A test of a split record is decided by its type.
                if self.forms[place.local.index()].is_some() && self.place(place).is_none() {
                    self.keep[place.local.index()] = true;
                }
            }
            Terminator::Call {
                func, args, dst, ..
            } => {
                self.arguments(*func, args);
                // A result given by value is in registers.
                if flat_result(self.db, self.program, *func).is_none() {
                    self.keep[dst.index()] = true;
                }
            }
            Terminator::TailCall { func, args, .. } => self.arguments(*func, args),
            Terminator::CallValue {
                callee, args, dst, ..
            } => {
                self.consumed(callee);
                args.iter().for_each(|o| self.consumed(o));
                self.keep[dst.index()] = true;
            }
            Terminator::TailCallValue { callee, args, .. } => {
                self.consumed(callee);
                args.iter().for_each(|o| self.consumed(o));
            }
            // A result given by value is packed from registers, or loaded
            // from its box.
            Terminator::Return(_) if self.gives_flat => {}
            Terminator::Return(o) => self.consumed(o),
            Terminator::Branch { cond, .. } => self.borrowed(cond),
            Terminator::Jump(_) | Terminator::Trap { .. } => {}
        }
    }
}

/// Where a value of a flat record's or union's register form is in its
/// storage form (Compiler Architecture §A11.4): the register it starts
/// at, and how its bytes or bits hold it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct Slot {
    pub at: usize,
    /// The byte it starts at, and its bytes.
    pub offset: u32,
    pub size: u32,
    /// Its first bit and width in the flag byte at `offset`.
    pub bits: Option<(u8, u8)>,
    pub kind: SlotKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum SlotKind {
    /// An integer, stored in `size` bytes and extended to a word with its
    /// sign or with zeros.
    Int { signed: bool },
    /// Words as they are: a `Float`, a box pointer, a string or a
    /// function value.
    Words,
    /// A union of tags: its local tag, which numbers the members whose
    /// type indices these are.
    Tag(Vec<i64>),
    /// A union whose register at `at` holds its member's type index: how
    /// storage tells the member, and each member's type index and slots.
    Union {
        tag: UnionTag,
        members: Vec<(i64, Vec<Slot>)>,
    },
}

/// How the storage form of a union tells its member.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum UnionTag {
    /// The member's local tag in `size` bytes at `offset`.
    Bytes { offset: u32, size: u32 },
    /// The member `empty`, of no words, is the other's niche: `size`
    /// bytes at `offset` that hold `value`, or a set bit of the flag byte
    /// there.
    Niche {
        empty: usize,
        offset: u32,
        test: NicheTest,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum NicheTest {
    Value { size: u8, value: u64 },
    Bit(u8),
}

/// The storage form of a flat record or union that passes by value, as
/// slots, with its bytes: none for what is not one.
pub fn storage<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<(u32, Vec<Slot>)> {
    let f = form(db, program, ty)?;
    let flat = flat::layout(db, program, ty).as_ref()?;
    let mut slots = Vec::new();
    let leaf = Leaf {
        size: flat.size,
        bits: None,
        narrowed: flat.narrowed,
    };
    slots_of(db, program, ty, &f, 0, 0, leaf, &mut slots)?;
    Some((flat.size, slots))
}

/// The storage form of a value of `ty` where a list, map or grid stores it
/// flat, as an element, a key or a value (Compiler Architecture §A11.3,
/// §A11.4.2–§A11.4.5): that of a flat record or union that passes by
/// value, or of a sized integer, a code point or a union of tags in fewer
/// bytes than its word. None without flat layouts.
pub fn element_storage<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<(u32, Vec<Slot>)> {
    if !flat_layouts() {
        return None;
    }
    if let Some(stored) = storage(db, program, ty) {
        return Some(stored);
    }
    let l = layout::layout(db, program, ty)?;
    if !matches!(l, Layout::Imm(_) | Layout::Tag) {
        return None;
    }
    let flat = flat::layout(db, program, ty).as_ref()?;
    if flat.class != LayoutClass::Immediate || flat.size >= 8 {
        return None;
    }
    let leaf = Leaf {
        size: flat.size,
        bits: None,
        narrowed: flat.narrowed,
    };
    let mut slots = Vec::new();
    slots_of(db, program, ty, &Form::Words(l), 0, 0, leaf, &mut slots)?;
    Some((flat.size, slots))
}

/// The storage form of a value of `ty` where a ref cell stores it flat,
/// beside its version (Compiler Architecture §A11.4.1, §A11.4.6): that of
/// a flat record or union that passes by value and takes at most the
/// cell's two words. An integer keeps its word, which `RefApply` works
/// on. None without flat layouts.
pub fn ref_storage<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<(u32, Vec<Slot>)> {
    if !flat_layouts() {
        return None;
    }
    storage(db, program, ty).filter(|&(size, _)| size <= 16)
}

/// The register form of a value of `ty` that a collection stores flat: a
/// split value's, or the words of its layout.
pub fn element_form<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Form<'db>> {
    form(db, program, ty).or_else(|| layout::layout(db, program, ty).map(Form::Words))
}

/// How a value is stored where its parent places it: its bytes, its bits
/// in a flag byte, and the builtin an integer is narrowed to.
#[derive(Clone, Copy)]
struct Leaf {
    size: u32,
    bits: Option<(u8, u8)>,
    narrowed: Option<Builtin>,
}

#[allow(clippy::too_many_arguments)]
fn slots_of<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    f: &Form<'db>,
    at: usize,
    offset: u32,
    leaf: Leaf,
    out: &mut Vec<Slot>,
) -> Option<()> {
    match f {
        Form::Fields(fields) => {
            let flat = flat::layout(db, program, ty).as_ref()?;
            fields_slots(db, program, &flat.fields, fields, at, offset, out)?;
        }
        Form::Union(members) => {
            let flat = flat::layout(db, program, ty).as_ref()?;
            out.push(union_slot(db, program, flat, members, at, offset)?);
        }
        Form::Words(l) => {
            let kind = match l {
                Layout::Zero => return Some(()),
                Layout::Imm(b) => match leaf.narrowed.unwrap_or(*b) {
                    Builtin::Int | Builtin::Int8 | Builtin::Int16 | Builtin::Int32 => {
                        SlotKind::Int { signed: true }
                    }
                    Builtin::UInt8
                    | Builtin::UInt16
                    | Builtin::UInt32
                    | Builtin::UInt64
                    | Builtin::CodePoint
                    | Builtin::CF32 => SlotKind::Int { signed: false },
                    Builtin::Float | Builtin::Fixed(_) | Builtin::CPtr => SlotKind::Words,
                    _ => return None,
                },
                Layout::Box | Layout::Pair | Layout::Closure => SlotKind::Words,
                // Split values split their unions.
                Layout::Union => return None,
                Layout::Tag => {
                    let union = flat::layout(db, program, ty).as_ref()?.union.as_ref()?;
                    let TagPlace::Bytes(_) = union.tag else {
                        return None;
                    };
                    SlotKind::Tag(union.members.iter().map(|m| type_index(m.ty)).collect())
                }
            };
            let size = match kind {
                SlotKind::Words => 8 * l.words() as u32,
                _ => leaf.size,
            };
            out.push(Slot {
                at,
                offset,
                size,
                bits: leaf.bits,
                kind,
            });
        }
    }
    Some(())
}

/// The slots of a record's fields in their places, from register `at`
/// and byte `offset` on.
pub(crate) fn fields_slots<'db>(
    db: &'db dyn Db,
    program: Program,
    places: &[flat::FieldPlace<'db>],
    fields: &[(Name<'db>, Ty<'db>, Form<'db>)],
    at: usize,
    offset: u32,
    out: &mut Vec<Slot>,
) -> Option<()> {
    let mut at = at;
    for (name, t, inner) in fields {
        let place = places.iter().find(|p| p.name == *name)?;
        let offset = offset + place.offset;
        match (inner, &place.edges) {
            // A union with edges is laid out where its record is.
            (Form::Union(members), Some(l)) => {
                out.push(union_slot(db, program, l, members, at, offset)?)
            }
            _ => {
                let leaf = Leaf {
                    size: place.size,
                    bits: place.bits,
                    narrowed: place.narrowed,
                };
                slots_of(db, program, *t, inner, at, offset, leaf, out)?;
            }
        }
        at += inner.words();
    }
    Some(())
}

/// The slot of a union laid out as `flat` at `offset`, whose type index
/// is register `at` and whose members' words follow it.
fn union_slot<'db>(
    db: &'db dyn Db,
    program: Program,
    flat: &flat::Layout<'db>,
    members: &[(Ty<'db>, Form<'db>)],
    at: usize,
    offset: u32,
) -> Option<Slot> {
    let union = flat.union.as_ref()?;
    let tag = match union.tag {
        TagPlace::Bytes(size) => UnionTag::Bytes { offset, size },
        TagPlace::Niche(n) => UnionTag::Niche {
            empty: union
                .members
                .iter()
                .position(|m| matches!(layout::layout(db, program, m.ty), Some(Layout::Zero)))?,
            offset: offset + n.offset,
            test: match n.kind {
                NicheKind::Value { size, value } => NicheTest::Value { size, value },
                NicheKind::Bit(bit) => NicheTest::Bit(bit),
            },
        },
    };
    let mut placed = Vec::new();
    for place in &union.members {
        let (_, f) = members.iter().find(|(m, _)| *m == place.ty)?;
        let own = flat::layout(db, program, place.ty).as_ref()?;
        let leaf = Leaf {
            size: if place.boxed.is_some() { 8 } else { own.size },
            bits: None,
            narrowed: own.narrowed,
        };
        let mut slots = Vec::new();
        slots_of(
            db,
            program,
            place.ty,
            f,
            at + 1,
            offset + place.offset,
            leaf,
            &mut slots,
        )?;
        placed.push((type_index(place.ty), slots));
    }
    Some(Slot {
        at,
        offset,
        size: flat.size,
        bits: None,
        kind: SlotKind::Union {
            tag,
            members: placed,
        },
    })
}

/// Whether an instance is a function's body, which takes and gives flat
/// records by value. Other code, which the runtime or a function value
/// calls, takes every record in its box.
fn by_value<'db>(db: &'db dyn Db, instance: InstanceKey<'db>) -> bool {
    let Owner::Item(item) = *instance.owner(db) else {
        return false;
    };
    let function = *item.kind(db) == ItemKind::Function && c_function(db, item).is_none();
    flat_layouts() && function && *instance.entry(db) == Entry::Body
}

/// Which parameters of an instance pass by value in storage form: those
/// of flat record types of a function's body.
#[crag_db::tracked(returns(ref))]
pub fn flat_params<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
) -> Vec<bool> {
    if !by_value(db, instance) {
        return Vec::new();
    }
    let Some(body) = mir(db, program, instance, Tier::Baseline) else {
        return Vec::new();
    };
    body.locals[..body.params]
        .iter()
        .map(|l| storage(db, program, l.ty).is_some())
        .collect()
}

/// The storage form of an instance's result when it gives it by value: a
/// flat record that a function's body with parameters returns. The host
/// runs functions without parameters as roots, and the `Embed` handlers
/// of types, which return records in their boxes: so do all functions
/// with no parameters, or a result of a type with an `Embed` handler.
#[crag_db::tracked(returns(ref))]
pub fn flat_result<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
) -> Option<(u32, Vec<Slot>)> {
    if !by_value(db, instance) {
        return None;
    }
    let body = mir(db, program, instance, Tier::Baseline).as_ref()?;
    if body.params == 0 || lifecycle_handler(db, program, body.result, "Embed").is_some() {
        return None;
    }
    storage(db, program, body.result)
}
