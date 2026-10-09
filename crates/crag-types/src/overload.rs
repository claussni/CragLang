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

//! Ranking overloads by specificity (Implementation Plan §11.5.4).
//!
//! Candidate A is more specific than B when every call A accepts, B
//! accepts too, but not the reverse (§5.6.1). Per parameter, A's type is
//! at least as specific as B's when B's type, its type parameters taken as
//! unknowns, can be instantiated to a type A's fits. Where both are
//! instances of each other, a concrete type beats a type parameter, and of
//! two type parameters the one with the larger requirement set wins: its
//! named bound fits the other's, it has every form the other has, and a
//! union of forms is weaker than each of its members.
//!
//! Only candidates of one module are ranked. A module must not declare two
//! overloads with the same parameter shape and incomparable bounds unless
//! it declares their combined overload too, so a call never meets that
//! ambiguity inside one module.

use crag_db::Db;
use crag_hir::{ItemId, ItemKind, ModuleId, Name, Program, item_tree};

use crate::def::signature;
use crate::generic::{FormBound, bind, bounds, mentions};
use crate::relate::{is_subtype, subst};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Ty, TyKind};

/// How one candidate's parameter compares with another's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Specificity {
    More,
    Less,
    Equal,
    Incomparable,
}

/// A candidate as ranking sees it: the function whose type parameters its
/// parameter types name, its module, and the type of the parameter each
/// argument goes to.
#[derive(Clone, Debug)]
pub struct Ranked<'db> {
    pub function: ItemId<'db>,
    pub module: ModuleId,
    pub params: Vec<Option<Ty<'db>>>,
}

/// The type arguments of `owner` that make `general` a type `specific`
/// fits, if there are such.
fn instance_of<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: ItemId<'db>,
    general: Ty<'db>,
    specific: Ty<'db>,
) -> Option<Vec<Option<Ty<'db>>>> {
    let count = type_param_count(db, program, owner);
    let mut args = vec![None; count];
    bind(db, program, owner, general, specific, &mut args);
    let unbound = |i: u32| args.get(i as usize).is_some_and(Option::is_none);
    if mentions(db, general, owner, &unbound) {
        return None;
    }
    let filled: Vec<Ty<'db>> = args
        .iter()
        .map(|a| a.unwrap_or_else(|| Ty::error(db)))
        .collect();
    is_subtype(
        db,
        program,
        specific,
        subst(db, program, general, owner, &filled),
    )
    .then_some(args)
}

fn type_param_count(db: &dyn Db, program: Program, owner: ItemId) -> usize {
    match *owner.kind(db) {
        ItemKind::Function => signature(db, program, owner).type_params,
        _ => 0,
    }
}

/// One requirement on a type parameter, its own parameter replaced by a
/// marker and the function's other parameters by the error type.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Atom<'db> {
    Type(Ty<'db>),
    Form(FormBound<'db>),
    AnyOf(Vec<FormBound<'db>>),
}

/// The requirements on type parameter `index` of `owner`: its named
/// bound, the forms of its bounds that name it, and unions of forms.
fn requirements<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: ItemId<'db>,
    index: u32,
) -> Vec<Atom<'db>> {
    if *owner.kind(db) != ItemKind::Function {
        return Vec::new();
    }
    let count = type_param_count(db, program, owner);
    let marker = Ty::new(
        db,
        TyKind::Param(None, u32::MAX, Name::new(db, "_".to_string())),
    );
    let args: Vec<Ty<'db>> = (0..count as u32)
        .map(|j| if j == index { marker } else { Ty::error(db) })
        .collect();
    let at = |t: Ty<'db>| subst(db, program, t, owner, &args);
    let names_it = |t: &Ty<'db>| mentions(db, *t, owner, &|j| j == index);
    let form = |f: &FormBound<'db>| FormBound {
        form: f.form,
        args: f.args.iter().map(|&t| at(t)).collect(),
    };
    let b = bounds(db, program, owner);
    let mut atoms: Vec<Atom<'db>> = b
        .types
        .iter()
        .filter(|(i, _)| *i == index)
        .map(|&(_, t)| Atom::Type(at(t)))
        .collect();
    atoms.extend(
        b.forms
            .iter()
            .filter(|f| f.args.iter().any(names_it))
            .map(|f| Atom::Form(form(f))),
    );
    atoms.extend(
        b.any_of
            .iter()
            .filter(|u| u.iter().any(|f| f.args.iter().any(names_it)))
            .map(|u| Atom::AnyOf(u.iter().map(form).collect())),
    );
    atoms
}

/// Whether the requirements `a` imply the requirement `b`.
fn implies<'db>(db: &'db dyn Db, program: Program, a: &[Atom<'db>], b: &Atom<'db>) -> bool {
    match b {
        Atom::Type(t) => a
            .iter()
            .any(|x| matches!(x, Atom::Type(s) if is_subtype(db, program, *s, *t))),
        Atom::Form(f) => a.contains(b) || a.iter().any(|x| matches!(x, Atom::Form(g) if g == f)),
        Atom::AnyOf(union) => a.iter().any(|x| match x {
            Atom::Form(f) => union.contains(f),
            Atom::AnyOf(other) => other.iter().all(|f| union.contains(f)),
            Atom::Type(_) => false,
        }),
    }
}

/// How requirement set `a` compares with `b`.
fn compare_requirements<'db>(
    db: &'db dyn Db,
    program: Program,
    a: &[Atom<'db>],
    b: &[Atom<'db>],
) -> Specificity {
    let a_covers = b.iter().all(|x| implies(db, program, a, x));
    let b_covers = a.iter().all(|x| implies(db, program, b, x));
    match (a_covers, b_covers) {
        (true, true) => Specificity::Equal,
        (true, false) => Specificity::More,
        (false, true) => Specificity::Less,
        (false, false) => Specificity::Incomparable,
    }
}

/// How parameter type `a` of `fa` compares with `b` of `fb`, and whether
/// they have the same shape: each an instance of the other.
fn compare<'db>(
    db: &'db dyn Db,
    program: Program,
    (fa, a): (ItemId<'db>, Ty<'db>),
    (fb, b): (ItemId<'db>, Ty<'db>),
) -> (Specificity, bool) {
    let b_of_a = instance_of(db, program, fb, b, a);
    let a_of_b = instance_of(db, program, fa, a, b);
    let (b_args, a_args) = match (b_of_a, a_of_b) {
        (Some(b_args), Some(a_args)) => (b_args, a_args),
        (Some(_), None) => return (Specificity::More, false),
        (None, Some(_)) => return (Specificity::Less, false),
        (None, None) => return (Specificity::Incomparable, false),
    };
    // The same shape: a type where the other has a type parameter is more
    // specific, and of two type parameters the larger requirement set.
    let bare = |t: Option<Ty<'db>>, owner: ItemId<'db>| match t.map(|t| t.kind(db)) {
        Some(TyKind::Param(Some(o), i, _)) if *o == owner => Some(*i),
        _ => None,
    };
    let mut more = false;
    let mut less = false;
    for (i, arg) in b_args.iter().enumerate() {
        match (arg, bare(*arg, fa)) {
            (None, _) => {}
            (Some(_), None) => more = true,
            (Some(_), Some(j)) => {
                let ra = requirements(db, program, fa, j);
                let rb = requirements(db, program, fb, i as u32);
                match compare_requirements(db, program, &ra, &rb) {
                    Specificity::More => more = true,
                    Specificity::Less => less = true,
                    Specificity::Incomparable => {
                        more = true;
                        less = true;
                    }
                    Specificity::Equal => {}
                }
            }
        }
    }
    for arg in &a_args {
        if arg.is_some() && bare(*arg, fb).is_none() {
            less = true;
        }
    }
    let spec = match (more, less) {
        (true, false) => Specificity::More,
        (false, true) => Specificity::Less,
        (false, false) => Specificity::Equal,
        (true, true) => Specificity::Incomparable,
    };
    (spec, true)
}

/// How parameter type `a` of function `fa` compares with `b` of `fb`.
pub fn compare_param<'db>(
    db: &'db dyn Db,
    program: Program,
    a: (ItemId<'db>, Ty<'db>),
    b: (ItemId<'db>, Ty<'db>),
) -> Specificity {
    compare(db, program, a, b).0
}

/// Whether `a` is at least as specific as `b` on every parameter both
/// take an argument for, and more specific on one.
fn dominates<'db>(db: &'db dyn Db, program: Program, a: &Ranked<'db>, b: &Ranked<'db>) -> bool {
    let mut strictly = false;
    for (pa, pb) in a.params.iter().zip(&b.params) {
        let (Some(pa), Some(pb)) = (pa, pb) else {
            continue;
        };
        match compare_param(db, program, (a.function, *pa), (b.function, *pb)) {
            Specificity::More => strictly = true,
            Specificity::Equal => {}
            Specificity::Less | Specificity::Incomparable => return false,
        }
    }
    strictly
}

/// The candidates no other candidate is more specific than, by index; the
/// modules of the candidates if they come from several, which are never
/// ranked.
pub fn most_specific<'db>(
    db: &'db dyn Db,
    program: Program,
    candidates: &[Ranked<'db>],
) -> Result<Vec<usize>, Vec<ModuleId>> {
    let mut modules: Vec<ModuleId> = Vec::new();
    for c in candidates {
        if !modules.contains(&c.module) {
            modules.push(c.module);
        }
    }
    if modules.len() > 1 {
        return Err(modules);
    }
    Ok((0..candidates.len())
        .filter(|&i| {
            !(0..candidates.len())
                .any(|j| j != i && dominates(db, program, &candidates[j], &candidates[i]))
        })
        .collect())
}

/// The overloads of a module with the same parameter shape and
/// incomparable bounds that lack their combined overload (§5.6.1). Each
/// is reported at the later of the two, naming the signature to add.
#[crag_db::tracked(returns(ref))]
pub fn overload_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(ItemId<'db>, TypeError<'db>)> {
    let functions: Vec<ItemId<'db>> = item_tree(db, module)
        .items
        .iter()
        .map(|i| i.id)
        .filter(|id| *id.kind(db) == ItemKind::Function)
        .collect();
    let mut errors = Vec::new();
    for (j, &b) in functions.iter().enumerate() {
        for &a in &functions[..j] {
            if a.name(db) != b.name(db) {
                continue;
            }
            let Some(binding) = clash(db, program, a, b) else {
                continue;
            };
            let combined = functions.iter().any(|&c| {
                c != a
                    && c != b
                    && c.name(db) == a.name(db)
                    && covers(db, program, c, a)
                    && covers(db, program, c, b)
            });
            if !combined {
                let signature = combined_signature(db, program, a, b, &binding);
                let kind = ErrorKind::MissingCombined {
                    other: a,
                    signature,
                };
                errors.push((
                    b,
                    TypeError {
                        site: Site::Name,
                        kind,
                    },
                ));
            }
        }
    }
    errors
}

/// Whether `a` and `b` have the same parameter shape and incomparable
/// bounds; then the type each type parameter of `b` stands for in `a`.
fn clash<'db>(
    db: &'db dyn Db,
    program: Program,
    a: ItemId<'db>,
    b: ItemId<'db>,
) -> Option<Vec<Option<Ty<'db>>>> {
    let (sa, sb) = (signature(db, program, a), signature(db, program, b));
    if sa.params.len() != sb.params.len() || (sa.type_params == 0 && sb.type_params == 0) {
        return None;
    }
    let mut more = false;
    let mut less = false;
    let mut binding = vec![None; sb.type_params];
    for (pa, pb) in sa.params.iter().zip(&sb.params) {
        let (spec, same_shape) = compare(db, program, (a, pa.ty), (b, pb.ty));
        if !same_shape {
            return None;
        }
        match spec {
            Specificity::More => more = true,
            Specificity::Less => less = true,
            Specificity::Incomparable => {
                more = true;
                less = true;
            }
            Specificity::Equal => {}
        }
        bind(db, program, b, pb.ty, pa.ty, &mut binding);
    }
    (more && less).then_some(binding)
}

/// Whether `c` has the parameter shape of `a` and requirements that cover
/// those of `a`.
fn covers<'db>(db: &'db dyn Db, program: Program, c: ItemId<'db>, a: ItemId<'db>) -> bool {
    let (sc, sa) = (signature(db, program, c), signature(db, program, a));
    sc.params.len() == sa.params.len()
        && sc.params.iter().zip(&sa.params).all(|(pc, pa)| {
            let (spec, same_shape) = compare(db, program, (c, pc.ty), (a, pa.ty));
            same_shape && matches!(spec, Specificity::More | Specificity::Equal)
        })
}

/// The signature of `a` with the requirements of both `a` and `b`, those
/// of `b` in `a`'s type parameters, as source writes it.
fn combined_signature<'db>(
    db: &'db dyn Db,
    program: Program,
    a: ItemId<'db>,
    b: ItemId<'db>,
    binding: &[Option<Ty<'db>>],
) -> String {
    let sig = signature(db, program, a);
    let names = crate::generic::type_param_names(db, program, a);
    let params: Vec<String> = sig
        .params
        .iter()
        .map(|p| match p.name {
            Some(n) => format!("{}: {}", n.text(db), p.ty.display(db)),
            None => p.ty.display(db),
        })
        .collect();
    let mut wanted: Vec<String> = Vec::new();
    let mut add = |s: String| {
        if !wanted.contains(&s) {
            wanted.push(s);
        }
    };
    let (ba, bb) = (bounds(db, program, a), bounds(db, program, b));
    let to_a: Vec<Ty<'db>> = binding
        .iter()
        .map(|t| t.unwrap_or_else(|| Ty::error(db)))
        .collect();
    for &(i, t) in &ba.types {
        add(format!("{}: {}", names[i as usize].text(db), t.display(db)));
    }
    for &(i, t) in &bb.types {
        if let Some(target) = to_a.get(i as usize) {
            add(format!(
                "{}: {}",
                target.display(db),
                subst(db, program, t, b, &to_a).display(db)
            ));
        }
    }
    for f in &ba.forms {
        add(f.display(db));
    }
    for f in &bb.forms {
        add(FormBound {
            form: f.form,
            args: f
                .args
                .iter()
                .map(|&t| subst(db, program, t, b, &to_a))
                .collect(),
        }
        .display(db));
    }
    for union in ba.any_of.iter().chain(&bb.any_of) {
        let forms: Vec<String> = union.iter().map(|f| f.display(db)).collect();
        add(forms.join(" | "));
    }
    let result = sig
        .result
        .map_or_else(String::new, |r| format!(" -> {}", r.display(db)));
    let type_params: Vec<String> = names.iter().map(|n| n.text(db).clone()).collect();
    format!(
        "fn {}[{}]({}){} where {}",
        a.name(db).text(db),
        type_params.join(", "),
        params.join(", "),
        result,
        wanted.join(", ")
    )
}
