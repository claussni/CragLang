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

//! Receiving code (Implementation Plan §11.10.8, Specification §18.7): a
//! tree is checked again by the receiver against the type it expects.

mod common;

use std::fs;
use std::path::PathBuf;

use crag_backend::tree::{Value, decode_tree, encode_tree, expr_tree, type_value};
use crag_driver::project::Project;
use crag_hir::{Owner, item_tree, owners};
use crag_receive::{Accept, Checked, Rejection, Slot, check_received};
use crag_types::{TyKind, body_types, signature};

const MANIFEST: &str = "package demo 0.1\nruntime 0.0\nmain demo.app\n";

/// A project of the app module's text, loaded.
fn load(name: &str, app: &str) -> Project {
    let root = common::project(
        &format!("receive-{name}"),
        &[("package.crag", MANIFEST), ("app.crag", app)],
    );
    let project = Project::load(&root);
    let _ = fs::remove_dir_all(PathBuf::from(&root));
    let project = project.unwrap();
    let errors = crag_driver::check(&project);
    assert!(errors.is_empty(), "{errors:?}");
    project
}

fn app(project: &Project) -> crag_hir::ModuleId {
    project.module("demo.app").expect("the app module")
}

/// The bytes of the tree of the one closure or function the function
/// sends as an `Expr`.
fn sent(project: &Project, function: &str) -> Vec<u8> {
    let (db, program) = (&project.db, project.program);
    let owner = owners(db, app(project))
        .into_iter()
        .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == function))
        .unwrap();
    let sent = body_types(db, program, owner).sent.clone();
    assert_eq!(sent.len(), 1, "{function}");
    expr_tree(db, program, owner, sent[0], None).unwrap().1
}

/// The function type `send` takes an `Expr` of, spelled out.
fn expected(project: &Project, function: &str) -> Value {
    let (db, program) = (&project.db, project.program);
    let item = item_tree(db, app(project))
        .items
        .iter()
        .find(|i| i.id.name(db).text(db) == function)
        .unwrap()
        .id;
    let param = signature(db, program, item).params[0].ty;
    let TyKind::Builtin(_, args) = param.kind(db) else {
        panic!("an Expr");
    };
    type_value(db, program, args[0]).unwrap()
}

/// Checks a tree in a slot of its own.
fn check(
    receiver: &mut Project,
    bytes: &[u8],
    function: &str,
    accept: Accept,
) -> Result<Checked, Rejection> {
    let mut slot = Slot::new(&mut receiver.db, receiver.program);
    check_in(receiver, &mut slot, bytes, function, accept)
}

fn check_in(
    receiver: &mut Project,
    slot: &mut Slot,
    bytes: &[u8],
    function: &str,
    accept: Accept,
) -> Result<Checked, Rejection> {
    let expected = expected(receiver, function);
    check_received(&mut receiver.db, slot, bytes, &expected, accept)
}

/// The sender's function that sends a closure calling `limit`.
const CHECKED: &str = "fn checked(min: Int) -> Int { send({ age -> min < limit(age) }) }\n";

const SENDER: &str = r#"import std.transport
pub type Pair(a: Int, b: Int)
pub fn adult(age: Int) -> Bool { 17 < age }
pub fn limit(age: Int) -> Int { age }
fn older(age: Int, by: Int) -> Int { age + by }
fn send(p: Expr[((Int) -> Bool is Pure)]) -> Int { 0 }
fn sendText(p: Expr[((Str) -> Bool is Pure)]) -> Int { 0 }
fn named() -> Int { send(adult) }
fn simple(min: Int) -> Int { send({ age -> min < older(age, -1) }) }
fn checked(min: Int) -> Int { send({ age -> min < limit(age) }) }
fn rich(k: Int) -> Int {
  send({ n ->
    let p = Pair(a: n, b: k)
    let xs = [p.a, p.b, -3]
    var total = 0
    for x in xs {
      total = total + x
    }
    let label = "n={n} \"total\" {{ {total} }}"
    let flag = if total > 10 { True } else { False }
    case xs {
      [first, ..rest] where first > 0 -> flag and label != "" and rest != []
      [_, second, _] -> second == 1 or not flag
      _ -> False
    }
  })
}
"#;

#[test]
fn received_code_reads_back_as_sent() {
    // Loopback: the sender's own program accepts each of its trees under
    // every policy, closures with captures and helpers and a named `pub`
    // function alike, and nothing diverges. All trees take turns in the
    // one received module, each under names of its own.
    let mut project = load("loopback", SENDER);
    let mut slot = Slot::new(&mut project.db, project.program);
    let mut roots = Vec::new();
    for function in ["named", "simple", "checked", "rich"] {
        let bytes = sent(&project, function);
        for accept in [Accept::Exact, Accept::SameMajor, Accept::Signature] {
            let checked = check_in(&mut project, &mut slot, &bytes, "send", accept)
                .unwrap_or_else(|e| panic!("{function}: {e:?}"));
            assert!(checked.mismatched.is_empty(), "{function}");
            assert_eq!(checked.program, slot.program(), "{function}");
            roots.push(checked.root);
        }
    }
    roots.dedup();
    assert_eq!(roots.len(), 12, "{roots:?}");
    // A literal keeps its sign in the tree.
    let bytes = sent(&project, "simple");
    let simple = check_in(&mut project, &mut slot, &bytes, "send", Accept::Exact).unwrap();
    assert!(simple.source.contains("(-1)"), "{}", simple.source);
    assert!(simple.source.contains("fn h12_0("), "{}", simple.source);
    assert!(
        simple.source.contains("fn received12("),
        "{}",
        simple.source
    );
}

#[test]
fn a_receiver_resolves_references_as_its_policy_says() {
    // §18.7: under `Exact` a callee's body must hash as the sender's;
    // under `Signature` its module, name and signature suffice, and the
    // mismatch is signalled; a callee the receiver lacks is unresolved.
    let sender = load("policy-sender", SENDER);
    let bytes = sent(&sender, "checked");
    let changed = SENDER.replace(
        "pub fn limit(age: Int) -> Int { age }",
        "pub fn limit(age: Int) -> Int { age + 1 }",
    );
    let mut receiver = load("policy-changed", &changed);
    let exact = check(&mut receiver, &bytes, "send", Accept::Exact);
    assert!(
        matches!(&exact, Err(Rejection::Unresolved(m)) if m.contains("`demo.app.limit`")),
        "{exact:?}"
    );
    for accept in [Accept::SameMajor, Accept::Signature] {
        let checked = check(&mut receiver, &bytes, "send", accept).unwrap();
        assert_eq!(
            checked.mismatched,
            [("demo.app".to_string(), "limit".to_string())]
        );
    }
    let retyped = SENDER.replace(
        "pub fn limit(age: Int) -> Int { age }",
        "pub fn limit(age: Int, by: Int = 0) -> Int { age + by }",
    );
    let mut receiver = load("policy-retyped", &retyped);
    let signature = check(&mut receiver, &bytes, "send", Accept::Signature);
    assert!(
        matches!(signature, Err(Rejection::Unresolved(_))),
        "{signature:?}"
    );
    let missing = SENDER.replace("pub fn limit(age: Int) -> Int { age }\n", "");
    let missing = missing.replace(CHECKED, "");
    let mut receiver = load("policy-missing", &missing);
    let lacking = check(&mut receiver, &bytes, "send", Accept::Signature);
    assert!(
        matches!(lacking, Err(Rejection::Unresolved(_))),
        "{lacking:?}"
    );
}

#[test]
fn received_code_is_checked_against_the_expected_type_and_purity() {
    // The tree is re-type-checked against the receiver's own type, and a
    // callee that has effects in the receiver makes the code impure.
    let mut project = load("types", SENDER);
    let bytes = sent(&project, "simple");
    let wrong = check(&mut project, &bytes, "sendText", Accept::Exact);
    assert!(matches!(wrong, Err(Rejection::IllTyped(_))), "{wrong:?}");
    let sender = load("impure-sender", SENDER);
    let bytes = sent(&sender, "checked");
    let loud = format!(
        "import std.io\n{}",
        SENDER
            .replace(
                "pub fn limit(age: Int) -> Int { age }",
                "pub fn limit(age: Int) -> Int {\n  printLine(\"x\")\n  age\n}"
            )
            .replace(CHECKED, "")
    );
    let mut receiver = load("impure-receiver", &loud);
    let impure = check(&mut receiver, &bytes, "send", Accept::Signature);
    assert!(matches!(impure, Err(Rejection::Impure(_))), "{impure:?}");
}

/// Replaces the first value `f` changes, depth first.
fn forge(v: &mut Value, f: &mut impl FnMut(&mut Value) -> bool) -> bool {
    if f(v) {
        return true;
    }
    match v {
        Value::Record(_, fields) => fields.iter_mut().any(|(_, v)| forge(v, f)),
        Value::List(items) => items.iter_mut().any(|v| forge(v, f)),
        _ => false,
    }
}

#[test]
fn forged_trees_are_rejected() {
    // A tree is data and can be forged (§18.7): bytes that are no tree, a
    // capture that is not Solid, a name that is no name and a reference
    // to a private function are all rejected, and none panics.
    let mut project = load("forged", SENDER);
    let bytes = sent(&project, "simple");
    for cut in [0, 1, 7, bytes.len() / 2, bytes.len() - 1] {
        let truncated = check(&mut project, &bytes[..cut], "send", Accept::Exact);
        assert!(
            matches!(truncated, Err(Rejection::IllTyped(_))),
            "{truncated:?}"
        );
    }
    let mut noise = bytes.clone();
    for (i, b) in noise.iter_mut().enumerate().skip(8) {
        *b = b.wrapping_mul(31).wrapping_add(i as u8);
    }
    assert!(check(&mut project, &noise, "send", Accept::Exact).is_err());
    let tree = decode_tree(&project.db, project.program, &bytes).unwrap();
    let encode =
        |project: &Project, v: &Value| encode_tree(&project.db, project.program, v).unwrap();
    // A capture of a function type that is not `is Pure`.
    let mut impure = tree.clone();
    assert!(forge(&mut impure, &mut |v| match v {
        Value::Record(name, fields) if name == "Tree" => {
            let captures = &mut fields.iter_mut().find(|(n, _)| n == "captures").unwrap().1;
            let Value::List(items) = captures else {
                panic!()
            };
            let int = items[0].clone();
            items[0] = Value::Record(
                "FnType".into(),
                vec![
                    ("params".into(), Value::List(Vec::new())),
                    ("result".into(), int),
                    ("pure".into(), Value::Tag("False".into())),
                ],
            );
            true
        }
        _ => false,
    }));
    let forged = encode(&project, &impure);
    let rejected = check(&mut project, &forged, "send", Accept::Exact);
    assert!(
        matches!(rejected, Err(Rejection::Impure(_))),
        "{rejected:?}"
    );
    // A field name that would be code.
    let mut injected = tree.clone();
    assert!(forge(&mut injected, &mut |v| match v {
        Value::Record(name, fields) if name == "FnRef" => {
            fields[3].1 = Value::Str("lessThan(1, 2) }\nfn evil() -> Int { 1".into());
            true
        }
        _ => false,
    }));
    let forged = encode(&project, &injected);
    let rejected = check(&mut project, &forged, "send", Accept::Exact);
    assert!(
        matches!(&rejected, Err(Rejection::IllTyped(m)) if m.contains("is no name")),
        "{rejected:?}"
    );
    // A reference to a function the receiver keeps private.
    let mut private = tree.clone();
    assert!(forge(&mut private, &mut |v| match v {
        Value::Record(name, fields) if name == "FnRef" => {
            fields[2].1 = Value::Str("demo.app".into());
            fields[3].1 = Value::Str("older".into());
            true
        }
        _ => false,
    }));
    let forged = encode(&project, &private);
    let rejected = check(&mut project, &forged, "send", Accept::Signature);
    assert!(
        matches!(rejected, Err(Rejection::Unresolved(_))),
        "{rejected:?}"
    );
}
