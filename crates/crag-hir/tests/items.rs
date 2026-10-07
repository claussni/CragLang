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
use crag_hir::{Import, Item, ItemTree, ModuleId, SourceFile, item_tree};
use crag_syntax::{GreenNode, SyntaxNode};

const MODULE: &str = r#"import std.io
import std.text.split as cut
import std.coll.{List, Map as Dict}
import cLib("libm").{ sin(x: Float) -> Float, cos(x: Float) -> Float }

// A point.
pub type Point(x: Int, y: Int = 0)
opaque type Meters = Float
pub form Show[T] {
  show(value: T) -> Str
}

pub fn area(s: Shape) -> Float
  where s.valid() {
  let local = 1
  s.size * local
}
fn area(p: Point) -> Float { 0.0 }
fn sin(x: Int) -> Int { x }

let origin: Point = Point(x: 0, y: 0)
let (left, right: r, Point(a, b), [first, ..rest]) = pair
embed logo: Bytes from "logo.png"

test "addition works" {
  fn helper() -> Int { 1 }
}
"#;

fn module(db: &RootDatabase, text: &str) -> ModuleId {
    let file = SourceFile::new(db, text.to_string());
    ModuleId::new(db, "geo.shape".to_string(), file)
}

/// The tokens of a signature, separated by spaces. Significant newlines
/// are tokens too.
fn tokens(green: &GreenNode) -> String {
    let root = SyntaxNode::new_root(green.clone());
    let texts: Vec<String> = root
        .descendant_tokens()
        .map(|t| t.text().to_string())
        .collect();
    texts.join(" ")
}

fn describe(db: &dyn Db, item: &Item) -> String {
    let id = item.id;
    format!(
        "{}{:?} {}#{} @{}: {}",
        if item.public { "pub " } else { "" },
        id.kind(db),
        id.name(db).text(db),
        id.ordinal(db),
        item.decl,
        tokens(&item.signature)
    )
}

fn names(db: &dyn Db, names: &[crag_hir::Name]) -> Vec<String> {
    names.iter().map(|n| n.text(db).clone()).collect()
}

#[test]
fn the_item_tree_lists_declarations_with_their_signatures() {
    let db = RootDatabase::new();
    let module = module(&db, MODULE);
    let tree: &ItemTree = item_tree(&db, module);

    let items: Vec<String> = tree.items.iter().map(|i| describe(&db, i)).collect();
    assert_eq!(
        items,
        [
            "pub Type Point#0 @4: pub type Point ( x : Int , y : Int = 0 )",
            "Type Meters#0 @5: opaque type Meters = Float",
            "pub Form Show#0 @6: pub form Show [ T ] { \n show ( value : T ) -> Str \n }",
            "pub Function area#0 @7: pub fn area ( s : Shape ) -> Float \n where s . valid ( )",
            "Function area#1 @8: fn area ( p : Point ) -> Float",
            // Ordinals count the C function of the same name too.
            "Function sin#1 @9: fn sin ( x : Int ) -> Int",
            "Value origin#0 @10: let origin : Point",
            "Value left#0 @11: let ( left , right : r , Point ( a , b ) , [ first , .. rest ] )",
            "Value r#0 @11: let ( left , right : r , Point ( a , b ) , [ first , .. rest ] )",
            "Value a#0 @11: let ( left , right : r , Point ( a , b ) , [ first , .. rest ] )",
            "Value b#0 @11: let ( left , right : r , Point ( a , b ) , [ first , .. rest ] )",
            "Value first#0 @11: let ( left , right : r , Point ( a , b ) , [ first , .. rest ] )",
            "Value rest#0 @11: let ( left , right : r , Point ( a , b ) , [ first , .. rest ] )",
            "Embed logo#0 @12: embed logo : Bytes from \"logo.png\"",
        ]
    );

    let imports: Vec<String> = tree
        .imports
        .iter()
        .map(|import| match import {
            Import::Module {
                path,
                alias,
                items,
                decl,
            } => format!(
                "@{decl} {:?} as {:?} items {:?}",
                names(&db, path),
                alias.map(|a| a.text(&db).clone()),
                items.as_ref().map(|items| items
                    .iter()
                    .map(|i| (
                        i.name.text(&db).clone(),
                        i.alias.map(|a| a.text(&db).clone())
                    ))
                    .collect::<Vec<_>>()),
            ),
            Import::C {
                library,
                functions,
                decl,
            } => format!(
                "@{decl} C {library} {:?}",
                functions
                    .iter()
                    .map(|f| describe(&db, f))
                    .collect::<Vec<_>>()
            ),
        })
        .collect();
    assert_eq!(
        imports,
        [
            r#"@0 ["std", "io"] as None items None"#,
            r#"@1 ["std", "text", "split"] as Some("cut") items None"#,
            r#"@2 ["std", "coll"] as None items Some([("List", None), ("Map", Some("Dict"))])"#,
            r#"@3 C "libm" ["Function sin#0 @3: sin ( x : Float ) -> Float", "Function cos#0 @3: cos ( x : Float ) -> Float"]"#,
        ]
    );

    assert_eq!(tree.tests.len(), 1);
    assert_eq!(tree.tests[0].label, "\"addition works\"");
    assert_eq!(tree.tests[0].decl, 13);
}

static SUMMARY_RUNS: AtomicUsize = AtomicUsize::new(0);

/// A query that reads only the item tree, like name resolution will.
#[crag_db::tracked]
fn summary(db: &dyn Db, module: ModuleId) -> usize {
    SUMMARY_RUNS.fetch_add(1, Ordering::Relaxed);
    item_tree(db, module).items.len()
}

#[test]
fn edits_that_leave_the_signatures_alone_stop_at_the_item_tree() {
    let mut db = RootDatabase::new();
    let module = module(&db, MODULE);
    let runs = || SUMMARY_RUNS.load(Ordering::Relaxed);
    let edit = |db: &mut RootDatabase, from: &str, to: &str| {
        let text = module.file(db).text(db).replacen(from, to, 1);
        assert_ne!(&text, module.file(db).text(db), "{from}");
        module.file(db).set_text(db).to(text);
        summary(db, module);
        runs()
    };

    summary(&db, module);
    assert_eq!(runs(), 1);
    // A body, a value, a test, a comment and the layout of a signature.
    assert_eq!(edit(&mut db, "s.size * local", "s.size * local * 2"), 1);
    assert_eq!(edit(&mut db, "Point(x: 0, y: 0)", "Point(x: 1, y: 2)"), 1);
    assert_eq!(edit(&mut db, "fn helper() -> Int { 1 }", ""), 1);
    assert_eq!(edit(&mut db, "// A point.", "// A point on the canvas."), 1);
    assert_eq!(
        edit(&mut db, "fn area(p: Point)", "fn area( p : Point )"),
        1
    );
    // A signature.
    assert_eq!(
        edit(&mut db, "fn sin(x: Int) -> Int", "fn sin(x: Int) -> Float"),
        2
    );
    // A new item.
    assert_eq!(edit(&mut db, "let origin", "fn extra() {}\nlet origin"), 3);
}
