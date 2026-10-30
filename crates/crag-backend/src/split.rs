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
//! record allocates nothing and reading a field picks its registers.
//!
//! A split local is used in registers by field reads, type tests,
//! counting, steps, and copies into another split local or a field of
//! one. A use that gives it away to a call, a return or a box boxes it
//! there, which takes its fields' references; a use that only borrows it
//! where it must be in a box keeps it boxed. A record read from a box, a
//! field or an element, is loaded into a split local field by field.
//!
//! Splitting makes no more boxes than there are: a local that is boxed
//! where it escapes must not be retained, which a second use needs, nor
//! come out of a box, which it could pass on as it is. A record a call
//! returns, or that is converted from a union, stays in its box for now.
//! With `CRAG_FLAT=0` in the environment no local is split.

use std::sync::OnceLock;

use crag_db::Db;
use crag_hir::{Name, Program};
use crag_mir::{ClosurePlacement, MirBody, Operand, Place, Rvalue, Statement, Terminator};
use crag_types::{Step, Ty, TyKind, TypeDefKind, type_def};

use crate::flat::{self, LayoutClass};
use crate::layout::{self, Layout};

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
}

impl<'db> Form<'db> {
    pub fn words(&self) -> usize {
        match self {
            Form::Words(l) => l.words(),
            Form::Fields(fields) => fields.iter().map(|(_, _, f)| f.words()).sum(),
        }
    }

    /// The values that are not records split further, with their words'
    /// first index, in order.
    pub fn leaves(&self, ty: Ty<'db>) -> Vec<(usize, Layout, Ty<'db>)> {
        let mut out = Vec::new();
        self.leaves_into(ty, 0, &mut out);
        out
    }

    fn leaves_into(&self, ty: Ty<'db>, at: usize, out: &mut Vec<(usize, Layout, Ty<'db>)>) {
        match self {
            Form::Words(l) => out.push((at, *l, ty)),
            Form::Fields(fields) => {
                let mut at = at;
                for (_, t, f) in fields {
                    f.leaves_into(*t, at, out);
                    at += f.words();
                }
            }
        }
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
/// record. Flat records within it are split too, but a field that is the
/// edge of a cycle holds a box.
pub fn form<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Form<'db>> {
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
    let mut fields = Vec::new();
    for place in &flat.fields {
        let inner = match place.boxed {
            Some(_) => None,
            None => form(db, program, place.ty),
        };
        let inner = match inner {
            Some(f) => f,
            None => Form::Words(layout::layout(db, program, place.ty)?),
        };
        fields.push((place.name, place.ty, inner));
    }
    Some(Form::Fields(fields))
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
            _ => return None,
        }
    }
    Some((at, ty, form, &[]))
}

/// Marks the locals of a body that code generation keeps split (see the
/// module's comment).
pub fn scalar_replace<'db>(db: &'db dyn Db, program: Program, body: &mut MirBody<'db>) {
    if !flat_layouts() {
        return;
    }
    let first = body.params.max(usize::from(body.env));
    let forms: Vec<Option<Form<'db>>> = body
        .locals
        .iter()
        .enumerate()
        .map(|(i, l)| match i < first {
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
        Some(matches!(form, Form::Fields(_)))
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
                    // Words, or a record read from its box.
                    (false, _) | (true, Some(false)) => {
                        if into_split {
                            defines = true;
                            self.from_box[dst.index()] = true;
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
                    self.from_box[dst.index()] = true;
                }
            }
            Rvalue::Record {
                fields,
                dispose: None,
                ..
            } if into_split => {
                defines = true;
                let form = self.forms[dst.index()].as_ref();
                for (name, op) in fields {
                    // A split record goes into a field split in turn.
                    let field = form.and_then(|f| f.field(*name));
                    let split_field = matches!(field, Some((_, _, Form::Fields(_))));
                    match op {
                        Operand::Local(l) if split_field && self.split[l.index()] => {}
                        _ if split_field => {
                            self.consumed(op);
                            self.keep[dst.index()] = true;
                        }
                        _ => self.consumed(op),
                    }
                }
            }
            Rvalue::Use(o) | Rvalue::Convert(o) | Rvalue::FnValue { env: o, .. } => {
                self.consumed(o)
            }
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

    fn terminator(&mut self, terminator: &Terminator<'db>) {
        match terminator {
            Terminator::Switch { place, .. } => {
                // A test of a split record is decided by its type.
                if self.forms[place.local.index()].is_some() && self.place(place).is_none() {
                    self.keep[place.local.index()] = true;
                }
            }
            Terminator::Call { args, dst, .. } => {
                args.iter().for_each(|o| self.consumed(o));
                self.keep[dst.index()] = true;
            }
            Terminator::TailCall { args, .. } => args.iter().for_each(|o| self.consumed(o)),
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
            Terminator::Return(o) => self.consumed(o),
            Terminator::Branch { cond, .. } => self.borrowed(cond),
            Terminator::Jump(_) | Terminator::Trap { .. } => {}
        }
    }
}
