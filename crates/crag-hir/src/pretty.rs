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

//! A body written out as S-expressions, for tests and debugging.
//!
//! A binding is written `name$n`, with `n` its index; the bindings lowering
//! makes itself are `_$n`. A name of items is written with what it is:
//! `name:type`, `name:form`, `name:value`, or `name/n` for `n` functions.

use std::fmt::Write;

use crag_db::Db;

use crate::hir::*;
use crate::literal::Literal;
use crate::scope::Resolution;

pub fn pretty(db: &dyn Db, body: &Body) -> String {
    let p = Printer { db, body };
    let mut out = String::new();
    if !body.params.is_empty() || body.result.is_some() {
        let _ = write!(out, "(params{})", p.params(&body.params));
        if let Some(result) = body.result {
            let _ = write!(out, " -> {}", p.ty(result));
        }
        out.push(' ');
    }
    if let Some((pat, ty)) = body.pattern {
        let _ = write!(out, "(pattern {}{}) ", p.pat(pat), p.annotation(ty));
    }
    match body.root {
        Some(root) => out.push_str(&p.expr(root)),
        None => out.push_str("<no body>"),
    }
    out
}

struct Printer<'a, 'db> {
    db: &'db dyn Db,
    body: &'a Body<'db>,
}

impl Printer<'_, '_> {
    fn binding(&self, id: BindingId) -> String {
        match self.body.binding(id).name {
            Some(name) => format!("{}${}", name.text(self.db), id.0),
            None => format!("_${}", id.0),
        }
    }

    fn list(&self, exprs: &[ExprId]) -> String {
        exprs
            .iter()
            .map(|&e| format!(" {}", self.expr(e)))
            .collect()
    }

    fn fields(&self, fields: &[FieldArg]) -> String {
        let fields: Vec<String> = fields
            .iter()
            .map(|f| match f {
                FieldArg::Field { path, value } => {
                    let path: Vec<&str> = path.iter().map(|n| n.text(self.db).as_str()).collect();
                    format!("{}: {}", path.join("."), self.expr(*value))
                }
                FieldArg::Spread(value) => format!("..{}", self.expr(*value)),
            })
            .collect();
        format!("{{{}}}", fields.join(", "))
    }

    fn call_args(&self, args: &[ExprId], fields: &Option<Vec<FieldArg>>) -> String {
        let mut out = self.list(args);
        if let Some(fields) = fields {
            out.push(' ');
            out.push_str(&self.fields(fields));
        }
        out
    }

    fn params(&self, params: &[Param]) -> String {
        params
            .iter()
            .map(|param| {
                let default = param
                    .default
                    .map(|d| format!(" = {}", self.expr(d)))
                    .unwrap_or_default();
                format!(
                    " {}: {}{default}",
                    self.binding(param.binding),
                    self.ty(param.ty)
                )
            })
            .collect()
    }

    fn annotation(&self, ty: Option<TypeRefId>) -> String {
        ty.map(|t| format!(": {}", self.ty(t))).unwrap_or_default()
    }

    fn expr(&self, id: ExprId) -> String {
        match self.body.expr(id) {
            Expr::Missing => "<missing>".into(),
            Expr::Hole => "???".into(),
            Expr::Literal(literal) => self.literal(literal),
            Expr::Str(parts) => {
                let parts: String = parts
                    .iter()
                    .map(|p| match p {
                        StrPart::Text(t) => format!(" {t:?}"),
                        StrPart::Expr(e) => format!(" {}", self.expr(*e)),
                    })
                    .collect();
                format!("(str{parts})")
            }
            Expr::Name { name, local, item } => {
                let mut out = match local {
                    Some(binding) => self.binding(*binding),
                    None => name.text(self.db).clone(),
                };
                match item {
                    Some(Resolution::Type(_)) => out.push_str(":type"),
                    Some(Resolution::Form(_)) => out.push_str(":form"),
                    Some(Resolution::Value { value, functions }) => {
                        if value.is_some() {
                            out.push_str(":value");
                        }
                        if !functions.is_empty() {
                            let _ = write!(out, "/{}", functions.len());
                        }
                    }
                    None => {}
                }
                out
            }
            Expr::Call {
                callee,
                args,
                fields,
            } => format!(
                "(call {}{})",
                self.expr(*callee),
                self.call_args(args, fields)
            ),
            Expr::MethodCall {
                receiver,
                name,
                functions,
                optional,
                args,
                fields,
            } => format!(
                "({} {} {}/{}{})",
                if *optional { "?." } else { "." },
                self.expr(*receiver),
                name.text(self.db),
                functions.len(),
                self.call_args(args, fields)
            ),
            Expr::TypedCall {
                ty,
                name,
                functions,
                args,
                fields,
            } => format!(
                "(typed {} {}/{}{})",
                self.ty(*ty),
                name.text(self.db),
                functions.len(),
                self.call_args(args, fields)
            ),
            Expr::Field {
                receiver,
                name,
                functions,
                optional,
            } => format!(
                "(field{} {} {}/{})",
                if *optional { "?" } else { "" },
                self.expr(*receiver),
                name.text(self.db),
                functions.len()
            ),
            Expr::Index { base, args } => {
                format!("(index {}{})", self.expr(*base), self.list(args))
            }
            Expr::TypeArgs { base, args } => {
                let args: String = args
                    .iter()
                    .map(|a| format!(" {}", self.type_arg(a)))
                    .collect();
                format!("(type-args {}{args})", self.expr(*base))
            }
            Expr::Compare { op, call } => format!("(compare {op:?} {})", self.expr(*call)),
            Expr::And(a, b) => format!("(and {} {})", self.expr(*a), self.expr(*b)),
            Expr::Or(a, b) => format!("(or {} {})", self.expr(*a), self.expr(*b)),
            Expr::Not(a) => format!("(not {})", self.expr(*a)),
            Expr::Range { start, end } => format!(
                "(range {}{})",
                self.expr(*start),
                end.map(|e| format!(" {}", self.expr(e)))
                    .unwrap_or_default()
            ),
            Expr::Is { expr, ty } => format!("(is {} {})", self.expr(*expr), self.ty(*ty)),
            Expr::Record(fields) => format!("(record {})", self.fields(fields)),
            Expr::List(items) => format!("(list{})", self.list(items)),
            Expr::Map(entries) => {
                let entries: String = entries
                    .iter()
                    .map(|&(k, v)| format!(" {}: {}", self.expr(k), self.expr(v)))
                    .collect();
                format!("(map{entries})")
            }
            Expr::Grid(rows) => {
                let rows: Vec<String> = rows.iter().map(|r| self.list(r)).collect();
                format!("(grid{})", rows.join(" ;"))
            }
            Expr::Block { stmts, tail } => {
                let mut parts: Vec<String> = stmts.iter().map(|s| self.stmt(s)).collect();
                parts.extend(tail.map(|t| self.expr(t)));
                format!("{{{}}}", parts.join("; "))
            }
            Expr::Closure { params, body } => {
                let params: Vec<String> = params
                    .iter()
                    .map(|p| format!("{}{}", self.pat(p.pat), self.annotation(p.ty)))
                    .collect();
                format!("(fn [{}] {})", params.join(", "), self.expr(*body))
            }
            Expr::If {
                condition,
                then,
                otherwise,
            } => format!(
                "(if {} {}{})",
                self.expr(*condition),
                self.expr(*then),
                otherwise
                    .map(|e| format!(" {}", self.expr(e)))
                    .unwrap_or_default()
            ),
            Expr::Case { subject, arms } => {
                let arms: String = arms
                    .iter()
                    .map(|arm| {
                        let guard = arm
                            .guard
                            .map(|g| format!(" where {}", self.expr(g)))
                            .unwrap_or_default();
                        format!(" [{}{guard} -> {}]", self.pat(arm.pat), self.expr(arm.body))
                    })
                    .collect();
                format!("(case {}{arms})", self.expr(*subject))
            }
            Expr::Pass => "pass".into(),
            Expr::Atomic(e) => format!("(atomic {})", self.expr(*e)),
            Expr::Lazy(e) => format!("(lazy {})", self.expr(*e)),
        }
    }

    fn stmt(&self, stmt: &Stmt) -> String {
        match stmt {
            Stmt::Expr(e) => self.expr(*e),
            Stmt::Let { pat, ty, value } => format!(
                "(let {}{} {})",
                self.pat(*pat),
                self.annotation(*ty),
                self.expr(*value)
            ),
            Stmt::LetElse {
                pat,
                ty,
                value,
                otherwise,
            } => format!(
                "(let {}{} {} else {})",
                self.pat(*pat),
                self.annotation(*ty),
                self.expr(*value),
                self.expr(*otherwise)
            ),
            Stmt::Bind { binding, ty, value } => format!(
                "({:?} {}{} {})",
                self.body.binding(*binding).kind,
                self.binding(*binding),
                self.annotation(*ty),
                self.expr(*value)
            )
            .to_lowercase(),
            Stmt::Assign { binding, value } => {
                format!("(set {} {})", self.binding(*binding), self.expr(*value))
            }
            Stmt::For {
                pat,
                iterable,
                body,
            } => format!(
                "(for {} {} {})",
                self.pat(*pat),
                self.expr(*iterable),
                self.expr(*body)
            ),
            Stmt::Emit { kind, value } => match kind {
                Some(kind) => format!("(emit {kind:?} {})", self.expr(*value)),
                None => format!("(emit {})", self.expr(*value)),
            },
            Stmt::Return(value) => match value {
                Some(v) => format!("(return {})", self.expr(*v)),
                None => "(return)".into(),
            },
            Stmt::On { ty, handler } => format!("(on {} {})", self.ty(*ty), self.expr(*handler)),
            Stmt::Fn { binding, function } => format!(
                "(local-fn {} (params{}){} {})",
                self.binding(*binding),
                self.params(&function.params),
                function
                    .result
                    .map(|r| format!(" -> {}", self.ty(r)))
                    .unwrap_or_default(),
                function
                    .body
                    .map(|b| self.expr(b))
                    .unwrap_or_else(|| "<no body>".into())
            ),
        }
    }

    fn pat(&self, id: PatId) -> String {
        match self.body.pat(id) {
            Pat::Missing => "<missing>".into(),
            Pat::Wildcard => "_".into(),
            Pat::Bind { binding, sub } => match sub {
                Some(sub) => format!("{} @ {}", self.binding(*binding), self.pat(*sub)),
                None => self.binding(*binding),
            },
            Pat::Type(ty) => self.ty(*ty),
            Pat::Record { ty, fields } => {
                let fields: Vec<String> = fields
                    .iter()
                    .map(|f| match f.name {
                        Some(name) => format!("{}: {}", name.text(self.db), self.pat(f.pat)),
                        None => self.pat(f.pat),
                    })
                    .collect();
                let ty = ty.map(|t| self.ty(t)).unwrap_or_default();
                format!("{ty}({})", fields.join(", "))
            }
            Pat::List {
                before,
                rest,
                after,
            } => {
                let mut items: Vec<String> = before.iter().map(|&p| self.pat(p)).collect();
                if let Some(rest) = rest {
                    items.push(format!(
                        "..{}",
                        rest.map(|b| self.binding(b)).unwrap_or_default()
                    ));
                }
                items.extend(after.iter().map(|&p| self.pat(p)));
                format!("[{}]", items.join(", "))
            }
            Pat::Literal(literal) => self.literal(literal),
            Pat::Range { start, end } => {
                format!("{}..{}", self.literal(start), self.literal(end))
            }
            Pat::Or(alternatives) => {
                let alternatives: Vec<String> = alternatives.iter().map(|&p| self.pat(p)).collect();
                format!("({})", alternatives.join(" | "))
            }
        }
    }

    fn literal(&self, literal: &Literal) -> String {
        match literal {
            Literal::Int(n) => n.to_string(),
            Literal::Float(text) => text.clone(),
            Literal::Str(s) => format!("{s:?}"),
            Literal::Bytes(bytes) => format!("b{bytes:?}"),
            Literal::CodePoint(c) => format!("{c:?}"),
        }
    }

    fn ty(&self, id: TypeRefId) -> String {
        match self.body.type_ref(id) {
            TypeRef::Missing => "<missing>".into(),
            TypeRef::Infer => "_".into(),
            TypeRef::Unit => "()".into(),
            TypeRef::Named { name, target, args } => {
                let mut out = name.text(self.db).clone();
                match target {
                    TypeTarget::Param(index) => {
                        let _ = write!(out, "'{index}");
                    }
                    TypeTarget::Unresolved => out.push('?'),
                    TypeTarget::Item(_) => {}
                }
                if !args.is_empty() {
                    let args: Vec<String> = args.iter().map(|a| self.type_arg(a)).collect();
                    let _ = write!(out, "[{}]", args.join(", "));
                }
                out
            }
            TypeRef::Record { fields, open } => {
                let mut fields: Vec<String> = fields
                    .iter()
                    .map(|f| match f {
                        TypeField::Field { name, ty } => {
                            format!("{}: {}", name.text(self.db), self.ty(*ty))
                        }
                        TypeField::Spread(ty) => format!("..{}", self.ty(*ty)),
                    })
                    .collect();
                if *open {
                    fields.push("..".into());
                }
                format!("({})", fields.join(", "))
            }
            TypeRef::Fn { params, result } => {
                let params: Vec<String> = params.iter().map(|&p| self.ty(p)).collect();
                format!("(({}) -> {})", params.join(", "), self.ty(*result))
            }
            TypeRef::Union(members) => {
                let members: Vec<String> = members.iter().map(|&m| self.ty(m)).collect();
                members.join(" | ")
            }
        }
    }

    fn type_arg(&self, arg: &TypeArg) -> String {
        match arg {
            TypeArg::Type(ty) => self.ty(*ty),
            TypeArg::Int(n) => n.to_string(),
            TypeArg::Is(markers) => {
                let markers: Vec<String> = markers
                    .iter()
                    .map(|&(negated, ty)| {
                        format!("{}{}", if negated { "not " } else { "" }, self.ty(ty))
                    })
                    .collect();
                format!("is {}", markers.join(", "))
            }
        }
    }
}
