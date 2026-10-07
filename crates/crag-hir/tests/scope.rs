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

extern crate crag_db as salsa;

use std::sync::atomic::{AtomicUsize, Ordering};

use crag_db::{Db, RootDatabase, Setter};
use crag_hir::{
    ItemId, ModuleId, NameError, Origin, PathError, Program, Resolution, SourceFile, import_graph,
    module_scope,
};

fn program(db: &RootDatabase, files: &[(&str, &str)]) -> (Program, Vec<ModuleId>) {
    let modules: Vec<ModuleId> = files
        .iter()
        .map(|(path, text)| {
            let file = SourceFile::new(db, text.to_string());
            ModuleId::new(db, path.to_string(), file)
        })
        .collect();
    (Program::new(db, modules.clone()), modules)
}

fn id(db: &dyn Db, id: ItemId) -> String {
    format!(
        "{}.{}#{}",
        id.module(db).path(db),
        id.name(db).text(db),
        id.ordinal(db)
    )
}

fn origin(origin: Origin) -> String {
    match origin {
        Origin::Declared => "declared".into(),
        Origin::Imported(decl) => format!("import @{decl}"),
        Origin::Prelude => "prelude".into(),
    }
}

/// The scope's names, sorted, each with what it resolves to.
fn names(db: &dyn Db, program: Program, module: ModuleId) -> Vec<String> {
    let scope = module_scope(db, program, module);
    let mut names: Vec<String> = scope
        .names
        .iter()
        .map(|(name, resolution)| {
            let target = match resolution {
                Resolution::Type(t) => format!("type {}", id(db, *t)),
                Resolution::Form(f) => format!("form {}", id(db, *f)),
                Resolution::Value { value, functions } => {
                    let mut parts: Vec<String> = value
                        .iter()
                        .map(|v| format!("value {}", id(db, *v)))
                        .collect();
                    if !functions.is_empty() {
                        let fs: Vec<String> = functions.iter().map(|f| id(db, *f)).collect();
                        parts.push(format!("fn {}", fs.join(" ")));
                    }
                    parts.join(", ")
                }
            };
            format!("{} = {target}", name.text(db))
        })
        .collect();
    names.sort();
    names
}

fn errors(db: &dyn Db, program: Program, module: ModuleId) -> Vec<String> {
    let path = |m: &ModuleId| m.path(db).clone();
    module_scope(db, program, module)
        .errors
        .iter()
        .map(|error| match error {
            NameError::Path { decl, error } => match error {
                PathError::Unknown(p) => format!("@{decl}: no module or directory {p}"),
                PathError::PastElement(p) => format!("@{decl}: {p} goes on past an element"),
            },
            NameError::ModuleRenamed { decl, path } => format!("@{decl}: {path} renamed"),
            NameError::UnknownElement { decl, module, name } => {
                format!("@{decl}: {} has no {}", path(module), name.text(db))
            }
            NameError::PrivateElement { decl, module, name } => {
                format!("@{decl}: {} is private in {}", name.text(db), path(module))
            }
            NameError::ModuleBesideDirectory { path } => format!("{path} beside a directory"),
            NameError::Collision { name, items } => {
                let items: Vec<String> = items
                    .iter()
                    .map(|(i, o)| format!("{} ({})", id(db, *i), origin(*o)))
                    .collect();
                format!("{} collides: {}", name.text(db), items.join(", "))
            }
        })
        .collect()
}

const SHAPE: &str = r#"pub type Point(x: Int, y: Int)
pub fn area(p: Point) -> Float { 0.0 }
fn helper() -> Int { 1 }
let origin = Point(x: 0, y: 0)
"#;

const CIRCLE: &str = r#"pub type Circle(r: Float)
pub fn area(c: Circle) -> Float { 3.14 * c.r * c.r }
"#;

#[test]
fn imports_bring_public_elements() {
    let db = RootDatabase::new();
    let (program, modules) = program(
        &db,
        &[
            ("geo.shape", SHAPE),
            ("geo.circle", CIRCLE),
            ("geo.sub.deep", "pub fn deep() -> Int { 1 }"),
            (
                "app",
                "import geo.shape\nimport geo.circle.area\nfn main() { area(Point(x: 0, y: 0)) }",
            ),
            (
                "renames",
                "import geo.shape.area as surface\nimport geo.shape.{Point, area as a}",
            ),
            ("dir", "import geo"),
            ("pick", "import geo.{circle}"),
        ],
    );
    let [_, _, _, app, renames, dir, pick] = modules[..] else {
        unreachable!()
    };
    // Overloads from two modules form one set; private items stay home.
    assert_eq!(
        names(&db, program, app),
        [
            "Point = type geo.shape.Point#0",
            "area = fn geo.shape.area#0 geo.circle.area#0",
            "main = fn app.main#0",
        ]
    );
    assert_eq!(
        names(&db, program, renames),
        [
            "Point = type geo.shape.Point#0",
            "a = fn geo.shape.area#0",
            "surface = fn geo.shape.area#0",
        ]
    );
    // A directory brings the modules directly in it, not those below.
    assert_eq!(
        names(&db, program, dir),
        [
            "Circle = type geo.circle.Circle#0",
            "Point = type geo.shape.Point#0",
            "area = fn geo.circle.area#0 geo.shape.area#0",
        ]
    );
    assert_eq!(
        names(&db, program, pick),
        [
            "Circle = type geo.circle.Circle#0",
            "area = fn geo.circle.area#0",
        ]
    );
    for module in modules {
        assert_eq!(errors(&db, program, module), Vec::<String>::new());
    }
}

#[test]
fn the_prelude_is_imported_everywhere_else() {
    let db = RootDatabase::new();
    let (program, modules) = program(
        &db,
        &[
            ("std.core", "pub type Int\npub fn print(s: Str) {}"),
            ("app", "fn main() {}"),
            // Naming the prelude again is no collision.
            ("again", "import std.core\nimport std.core.print as say"),
        ],
    );
    let [core, app, again] = modules[..] else {
        unreachable!()
    };
    assert_eq!(
        names(&db, program, core),
        ["Int = type std.core.Int#0", "print = fn std.core.print#0"]
    );
    assert_eq!(
        names(&db, program, app),
        [
            "Int = type std.core.Int#0",
            "main = fn app.main#0",
            "print = fn std.core.print#0",
        ]
    );
    assert_eq!(
        names(&db, program, again),
        [
            "Int = type std.core.Int#0",
            "print = fn std.core.print#0",
            "say = fn std.core.print#0",
        ]
    );
    assert_eq!(errors(&db, program, again), Vec::<String>::new());
    assert!(import_graph(&db, program).cycles.is_empty());
}

#[test]
fn bad_imports_are_reported() {
    let db = RootDatabase::new();
    let (program, modules) = program(&db, &[("geo.shape", SHAPE), ("geo", "pub fn clash() {}")]);
    assert_eq!(errors(&db, program, modules[1]), ["geo beside a directory"]);
    let db = RootDatabase::new();
    let (program, modules) = self::program(
        &db,
        &[
            ("geo.shape", SHAPE),
            (
                "app",
                "import geo.shap\nimport geo.shape.area.more\nimport geo.shape as s\n\
                 import geo.shape.volume\nimport geo.shape.origin\nimport geo.shape.area.{x}\n\
                 import geo as g\nimport geo.{shape as s}",
            ),
        ],
    );
    let app_alone = modules[1];
    assert_eq!(
        errors(&db, program, app_alone),
        [
            "@0: no module or directory geo.shap",
            "@1: geo.shape.area.more goes on past an element",
            "@2: geo.shape renamed",
            "@5: geo.shape.area goes on past an element",
            "@6: geo renamed",
            "@7: geo.shape renamed",
            "@3: geo.shape has no volume",
            "@4: origin is private in geo.shape",
        ]
    );
}

#[test]
fn names_that_meet_merge_or_collide() {
    let db = RootDatabase::new();
    let (program, modules) = program(
        &db,
        &[
            (
                "a",
                "pub type Point(x: Int, y: Int)\npub fn f(x: Int) -> Int { x }\npub type Id = Int",
            ),
            // The same type in another module, written differently.
            (
                "b",
                "type Unused\npub type Point(\n  x: Int, y: Int  // same fields\n)\npub fn f(y: Int) -> Int { 0 }",
            ),
            (
                "c",
                "pub type Point(x: Int)\npub distinct type Id = Int\npub fn g() {}",
            ),
            (
                "merge",
                "import a.Point\nimport b.Point\nimport a.f\nlet f = 1",
            ),
            ("clash", "import a\nimport b\nimport c"),
            ("fixed", "import a\nimport b.{f as bf, Point}"),
            (
                "own",
                "type T\nfn T() {}\nfn h(a: Int) -> Int { a }\nfn h(b: Int) -> Int { b }\n\
                 fn h(a: Str) -> Int { 0 }\nlet (w, w) = p\nembed Id: Bytes from \"id\"\nimport a.Id",
            ),
        ],
    );
    let [_, _, _, merge, clash, fixed, own] = modules[..] else {
        unreachable!()
    };
    // Indistinguishable types merge, a value may share its name with
    // functions.
    assert_eq!(errors(&db, program, merge), Vec::<String>::new());
    assert_eq!(
        names(&db, program, merge),
        ["Point = type a.Point#0", "f = value merge.f#0, fn a.f#0",]
    );
    assert_eq!(
        errors(&db, program, clash),
        [
            "Point collides: a.Point#0 (import @0), b.Point#0 (import @1), c.Point#0 (import @2)",
            "f collides: a.f#0 (import @0), b.f#0 (import @1)",
            "Id collides: a.Id#0 (import @0), c.Id#0 (import @2)",
        ]
    );
    // A rename resolves a clash.
    assert_eq!(errors(&db, program, fixed), Vec::<String>::new());
    assert_eq!(
        errors(&db, program, own),
        [
            "T collides: own.T#0 (declared), own.T#0 (declared)",
            "h collides: own.h#0 (declared), own.h#1 (declared)",
            "w collides: own.w#0 (declared), own.w#1 (declared)",
            "Id collides: own.Id#0 (declared), a.Id#0 (import @7)",
        ]
    );
}

#[test]
fn bare_let_names_that_are_types_bind_nothing() {
    let db = RootDatabase::new();
    let (program, modules) = program(
        &db,
        &[
            (
                "colors",
                "pub type Red\nlet Red = c\nlet (Blue, x) = pair\npub type Blue",
            ),
            (
                "app",
                "import colors\nlet Red = r\nlet [first, ..Red] = list",
            ),
        ],
    );
    let [colors, app] = modules[..] else {
        unreachable!()
    };
    assert_eq!(errors(&db, program, colors), Vec::<String>::new());
    assert_eq!(
        names(&db, program, colors),
        [
            "Blue = type colors.Blue#0",
            "Red = type colors.Red#0",
            "x = value colors.x#0",
        ]
    );
    // `Red` is a type here too, through the import, but `..Red` binds.
    assert_eq!(
        errors(&db, program, app),
        ["Red collides: app.Red#1 (declared), colors.Red#0 (import @0)"]
    );
}

#[test]
fn import_cycles_are_found() {
    let db = RootDatabase::new();
    let (program, modules) = program(
        &db,
        &[
            ("a", "import b"),
            ("b", "fn f() {}\nimport c.g\nimport a"),
            ("c", "pub fn g() {}\nimport b"),
            ("self", "import self"),
            ("fine", "import a"),
        ],
    );
    let path = |m: &ModuleId| m.path(&db).clone();
    let cycles: Vec<Vec<String>> = import_graph(&db, program)
        .cycles
        .iter()
        .map(|cycle| {
            cycle
                .steps
                .iter()
                .map(|(m, decl)| format!("{} @{}", path(m), decl.unwrap()))
                .collect()
        })
        .collect();
    assert_eq!(cycles, [vec!["a @0", "b @2"], vec!["self @0"]]);
    let _ = modules;
}

/// A query that reads a module's scope and counts its runs.
static RUNS: AtomicUsize = AtomicUsize::new(0);

#[crag_db::tracked]
fn scope_size(db: &dyn Db, program: Program, module: ModuleId) -> usize {
    RUNS.fetch_add(1, Ordering::SeqCst);
    module_scope(db, program, module).names.len()
}

#[test]
fn edits_to_bodies_of_imported_modules_stop_at_the_scope() {
    let mut db = RootDatabase::new();
    let (program, modules) = program(&db, &[("geo.shape", SHAPE), ("app", "import geo.shape")]);
    let [shape, app] = modules[..] else {
        unreachable!()
    };
    let runs = |db: &RootDatabase| {
        scope_size(db, program, app);
        RUNS.load(Ordering::SeqCst)
    };
    let start = runs(&db);
    let edit = |db: &mut RootDatabase, text: String| {
        let file = *shape.file(db);
        file.set_text(db).to(text);
    };
    edit(&mut db, SHAPE.replace("{ 0.0 }", "{ 1.0 }"));
    edit(
        &mut db,
        SHAPE.replace("fn helper() -> Int", "fn helper2() -> Int"),
    );
    assert_eq!(runs(&db), start, "a body or a private item changed");
    edit(&mut db, format!("{SHAPE}pub fn more() {{}}"));
    assert_eq!(runs(&db), start + 1, "a public item was added");
}
