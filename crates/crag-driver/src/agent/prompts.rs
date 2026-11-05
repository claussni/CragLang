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

//! The prompts of the agent server (Implementation Plan §11.12.9): named
//! instructions an agent loads before a task, with their texts in the
//! knowledge bundle.

use crag_mcp::PromptSpec;
use serde_json::{Map, Value};

pub(super) fn specs() -> Vec<PromptSpec> {
    vec![
        PromptSpec {
            name: "crag-principles",
            title: "Write Crag like Crag",
            description: "The design principles as working instructions: immutability first, \
                          visible mutation, the three channels, structural typing, inferred \
                          effects, and names proposed to the user.",
            arguments: &[],
            text: |_| crag_knowledge::prompt_principles().to_string(),
        },
        PromptSpec {
            name: "crag-write-module",
            title: "Write a module",
            description: "Write a module, then check, test and fmt until clean.",
            arguments: &[(
                "module",
                "The module path to write, such as demo.parser.",
                true,
            )],
            text: |args| {
                crag_knowledge::prompt_write_module().replace("{module}", &text(args, "module"))
            },
        },
        PromptSpec {
            name: "crag-fix-diagnostics",
            title: "Fix diagnostics",
            description: "Read each diagnostic's explanation before changing code, then fix \
                          and re-check until clean.",
            arguments: &[(
                "module",
                "The module to fix; without it, the whole project.",
                false,
            )],
            text: |args| {
                let target = match args.get("module").and_then(Value::as_str) {
                    Some(module) if !module.is_empty() => format!("the module {module}"),
                    _ => "the project".to_string(),
                };
                crag_knowledge::prompt_fix_diagnostics().replace("{target}", &target)
            },
        },
    ]
}

fn text(args: &Map<String, Value>, name: &str) -> String {
    args.get(name)
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string()
}
