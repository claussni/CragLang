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

//! Calls: of a function, of a function value, of a dispatch over union
//! members, of a primitive or an intrinsic of the prelude, and the
//! arguments with their defaults.

use super::*;

impl<'a, 'db> MirBuilder<'a, 'db> {
    /// The operation and the operand `k` of an update closure of the form
    /// `v ⊕ k` on an integer, which the runtime applies under the cell's
    /// lock so that the update never reruns (§9.4): `+`, `*` either way
    /// round and `-` with `v` first, checked, and `k` a literal or another
    /// binding, which the closure captures.
    pub(super) fn commutative(&self, closure: ExprId, ty: Ty<'db>) -> Option<(BinOp, ExprId)> {
        let db = self.db;
        ty.as_builtin(db).and_then(|(b, _)| b.int_range())?;
        let body = self.body;
        let Expr::Closure {
            params,
            body: inner,
        } = body.expr(closure)
        else {
            return None;
        };
        let [param] = params.as_slice() else {
            return None;
        };
        let Pat::Bind { binding, sub: None } = body.pat(param.pat) else {
            return None;
        };
        let mut inner = *inner;
        while let Expr::Block {
            stmts,
            tail: Some(tail),
        } = body.expr(inner)
            && stmts.is_empty()
        {
            inner = *tail;
        }
        let Expr::Call {
            callee: _,
            args,
            fields: None,
        } = body.expr(inner)
        else {
            return None;
        };
        let [a, b] = args.as_slice() else {
            return None;
        };
        let instance = self.callee_instance(self.types.callee(inner)?)?;
        let Some(Primitive::Arith {
            op,
            ty: builtin,
            checked: true,
        }) = self.primitive_of(&instance)
        else {
            return None;
        };
        if Some((builtin, &[][..])) != ty.as_builtin(db) {
            return None;
        }
        let is_v =
            |e: ExprId| matches!(body.expr(e), Expr::Name { local: Some(l), .. } if l == binding);
        let is_k = |e: ExprId| match body.expr(e) {
            Expr::Literal(_) => true,
            Expr::Name { local: Some(l), .. } => l != binding,
            _ => false,
        };
        match op {
            BinOp::Add | BinOp::Mul if is_v(*a) && is_k(*b) => Some((op, *b)),
            BinOp::Add | BinOp::Mul if is_k(*a) && is_v(*b) => Some((op, *a)),
            BinOp::Sub if is_v(*a) && is_k(*b) => Some((op, *b)),
            _ => None,
        }
    }

    /// The runtime operation a function of the standard library without a
    /// body stands for, if it is one.
    fn intrinsic(&self, instance: &Instance<'db>) -> Option<Intrinsic<'db>> {
        let db = self.db;
        let function = instance.function;
        if hir_body(db, self.program, Owner::Item(function))
            .root
            .is_some()
        {
            return None;
        }
        let module = function.module(db).path(db);
        Some(
            match (module.as_str(), function.name(db).text(db).as_str()) {
                ("std.time", "sleepNanos") => Intrinsic::Sleep,
                ("std.transport", "treeHash") => Intrinsic::ExprTreeHash,
                ("std.transport", "tree") => Intrinsic::ExprTree,
                ("std.transport", "transportRun") => Intrinsic::TransportRun,
                ("std.transport", "transportResult") => Intrinsic::TransportResult,
                ("std.transport", "transportMessage" | "transportBytes") => Intrinsic::IoReadBytes,
                ("std.transport", "transportDecoded") => Intrinsic::TransportResult,
                ("std.transport", "transportEncode") => Intrinsic::TransportEncode,
                ("std.transport", "transportDecode") => Intrinsic::TransportDecode {
                    value: *instance.args.first()?,
                },
                ("std.transport", "budgetOp" | "budgetInfo") => Intrinsic::BudgetOp,
                ("std.transport", "transportWord") => Intrinsic::TransportResult,
                ("std.task", "scopeNew") => Intrinsic::ScopeNew,
                ("std.task", "scopeStart") => Intrinsic::ScopeStart,
                ("std.task", "scopeNext") => Intrinsic::ScopeNext,
                ("std.task", "scopeResult") => Intrinsic::ScopeResult,
                ("std.task", "scopeCancel") => Intrinsic::ScopeCancel,
                ("std.task", "scopeEnd") => Intrinsic::ScopeEnd,
                ("std.stream", "streamNew") => Intrinsic::StreamNew {
                    value: *instance.args.first()?,
                },
                ("std.stream", "streamPeer") => Intrinsic::StreamPeer,
                ("std.stream", "streamPut") => Intrinsic::StreamPut { wait: true },
                ("std.stream", "streamTryPut") => Intrinsic::StreamPut { wait: false },
                ("std.stream", "streamNext") => Intrinsic::StreamNext,
                ("std.stream", "streamValue") => Intrinsic::StreamValue,
                ("std.stream", "streamClose") => Intrinsic::StreamClose,
                ("std.stream", "hubNew") => Intrinsic::HubNew {
                    value: *instance.args.first()?,
                },
                ("std.stream", "hubSink") => Intrinsic::HubSink,
                ("std.stream", "hubSource") => Intrinsic::HubSource,
                ("std.stream", "hubSeal") => Intrinsic::HubSeal,
                ("std.stream", "hubRelease") => Intrinsic::HubRelease,
                ("std.io", "ioListen") => Intrinsic::IoListen,
                ("std.io", "ioOwn") => Intrinsic::IoOwn,
                ("std.io", "ioPort") => Intrinsic::IoPort,
                ("std.io", "ioAccept") => Intrinsic::IoAccept,
                ("std.io", "ioSocket") => Intrinsic::IoSocket,
                ("std.io", "ioConnect") => Intrinsic::IoConnect,
                ("std.io", "ioRead") => Intrinsic::IoRead,
                ("std.io", "ioReadBytes") => Intrinsic::IoReadBytes,
                ("std.io", "ioWrite") => Intrinsic::IoWrite,
                ("std.test", "testFailure") => Intrinsic::TestFailure,
                ("std.env", "envArgs") => Intrinsic::EnvArgs,
                ("std.env", "envVar") => Intrinsic::EnvVar,
                ("std.env", "envVarBytes") => Intrinsic::IoReadBytes,
                ("std.env", "envVars") => Intrinsic::EnvVars,
                ("std.env", "envPlatform") => Intrinsic::EnvPlatform,
                ("std.c", "cf32Bits" | "cf32Of" | "ptrWord") => Intrinsic::Word,
                ("std.io", "ioPrint") => Intrinsic::IoPrint,
                ("std.io", "ioFault") => Intrinsic::IoFault,
                ("std.io", "ioReadFile") => Intrinsic::IoReadFile,
                ("std.io", "ioSocketAny") => Intrinsic::IoSocketAny,
                ("std.io", "ioConnectHost") => Intrinsic::IoConnectHost,
                ("std.core", name) => {
                    use crag_abi::text_op::*;
                    match name {
                        "textByteCount" => Intrinsic::TextMeasure(BYTE_COUNT),
                        "textCodePointCount" => Intrinsic::TextMeasure(CODE_POINT_COUNT),
                        "textIsBoundary" => Intrinsic::TextAt(IS_BOUNDARY),
                        "textNext" => Intrinsic::TextAt(NEXT),
                        "textPrevious" => Intrinsic::TextAt(PREVIOUS),
                        "textCodePointAt" => Intrinsic::TextAt(CODE_POINT_AT),
                        "textByteAt" => Intrinsic::TextAt(BYTE_AT),
                        "textIndexOf" => Intrinsic::TextFind(INDEX_OF),
                        "textLastIndexOf" => Intrinsic::TextFind(LAST_INDEX_OF),
                        "textStartsWith" => Intrinsic::TextFind(STARTS_WITH),
                        "textEndsWith" => Intrinsic::TextFind(ENDS_WITH),
                        "textCompare" => Intrinsic::TextFind(COMPARE),
                        "textTrim" => Intrinsic::TextMap(TRIM),
                        "textTrimStart" => Intrinsic::TextMap(TRIM_START),
                        "textTrimEnd" => Intrinsic::TextMap(TRIM_END),
                        "textToUpper" => Intrinsic::TextMap(TO_UPPER),
                        "textToLower" => Intrinsic::TextMap(TO_LOWER),
                        "textHex" => Intrinsic::TextMap(HEX),
                        "textSlice" => Intrinsic::TextSlice,
                        "cpIsLetter" => Intrinsic::CodePointOp(CP_IS_LETTER),
                        "cpIsDigit" => Intrinsic::CodePointOp(CP_IS_DIGIT),
                        "cpIsWhitespace" => Intrinsic::CodePointOp(CP_IS_WHITESPACE),
                        "cpIsUpper" => Intrinsic::CodePointOp(CP_IS_UPPER),
                        "cpIsLower" => Intrinsic::CodePointOp(CP_IS_LOWER),
                        "cpIsNumeric" => Intrinsic::CodePointOp(CP_IS_NUMERIC),
                        "cpToUpper" => Intrinsic::CodePointOp(CP_TO_UPPER),
                        "cpToLower" => Intrinsic::CodePointOp(CP_TO_LOWER),
                        "cpIsValid" => Intrinsic::CodePointOp(CP_IS_VALID),
                        "textParseInt" => Intrinsic::TextParse(PARSE_INT),
                        "textParseFloat" => Intrinsic::TextParse(PARSE_FLOAT),
                        "textParsedInt" | "textParsedFloat" => Intrinsic::TextParsed,
                        "cpOf" | "cpValue" | "wordAs" | "wordOf" => Intrinsic::Word,
                        "textParseUInt" => Intrinsic::TextParse(PARSE_UINT),
                        "bytesRead" => Intrinsic::BytesRead,
                        "bytesWrite" => Intrinsic::BytesWrite,
                        "bytesOfList" => Intrinsic::BytesOfList,
                        "textUtf8" => Intrinsic::TextUtf8,
                        "textOfBytes" | "bytesOfText" => Intrinsic::TextCast,
                        "listAppend" => Intrinsic::ListAppend,
                        "collCount" | "mapCount" | "setCount" => Intrinsic::CollCount,
                        "listSet" => Intrinsic::ListSet,
                        "listConcat" => Intrinsic::ListConcat,
                        "listSlice" => Intrinsic::ListSlice,
                        "mapInsert" => Intrinsic::MapInsert,
                        "setInsert" => Intrinsic::SetInsert,
                        "mapRemove" | "setRemove" => Intrinsic::MapRemove,
                        "setContains" => Intrinsic::SetContains,
                        "mapKeys" | "setKeys" => Intrinsic::MapKeys,
                        "mapValues" => Intrinsic::MapValues,
                        "valueEquals" => Intrinsic::ValueOp {
                            op: crag_abi::value_op::EQUALS,
                            ty: *instance.args.first()?,
                        },
                        "valueCompare" => Intrinsic::ValueOp {
                            op: crag_abi::value_op::COMPARE,
                            ty: *instance.args.first()?,
                        },
                        "valueHash" => Intrinsic::ValueOp {
                            op: crag_abi::value_op::HASH,
                            ty: *instance.args.first()?,
                        },
                        "valueShow" => Intrinsic::ValueShow {
                            ty: *instance.args.first()?,
                        },
                        "trapIndex" => Intrinsic::TrapWith(crag_abi::TrapKind::Index as u8),
                        "trapUnordered" => Intrinsic::TrapWith(crag_abi::TrapKind::Unordered as u8),
                        "bytesCount" => Intrinsic::TextMeasure(BYTE_COUNT),
                        "bytesAt" => Intrinsic::TextAt(BYTE_AT),
                        "bytesSlice" => Intrinsic::TextSlice,
                        "bytesHex" => Intrinsic::TextMap(HEX),
                        "bytesCompare" => Intrinsic::TextFind(COMPARE),
                        "u8Of" => Intrinsic::Word,
                        _ => return None,
                    }
                }
                _ => return None,
            },
        )
    }

    /// The operation a concrete instance stands for, if it is one.
    pub(super) fn primitive_of(&self, instance: &Instance<'db>) -> Option<Primitive> {
        match instance.args.is_empty() {
            true => self.primitive(instance.function),
            false => None,
        }
    }

    /// The code a call of a concrete instance goes to, or none when it
    /// cannot be called yet, which is recorded at the call.
    pub(super) fn callable(
        &mut self,
        expr: ExprId,
        instance: &Instance<'db>,
    ) -> Option<InstanceKey<'db>> {
        let db = self.db;
        if signature(db, self.program, instance.function).type_params != instance.args.len() {
            self.trap(TrapKind::Error, Some(expr));
            return None;
        }
        if instance.args.iter().any(|&t| depth(db, t) > INSTANCE_DEPTH) {
            self.unsupported(expr, "instances whose type arguments nest this deeply");
            return None;
        }
        Some(InstanceKey::of(db, instance))
    }

    /// A closure literal or a local function as a value: its code and its
    /// environment, placed by its escape level.
    pub(super) fn closure_value(
        &mut self,
        frame: ExprId,
        ty: Ty<'db>,
        own: Option<BindingId>,
    ) -> Operand<'db> {
        let (captures, env) = self.environment(frame, own);
        let mut ops = Vec::new();
        for &binding in &captures {
            ops.push(Operand::Local(self.binding(binding)));
        }
        let env = self.with_module_values(frame, env, captures.len());
        let values = self.module_captures(frame);
        // The environment takes what it read of the module values, which
        // no local keeps live for one on the side stack.
        let heap = !values.is_empty();
        for (value, at) in values {
            ops.push(self.module_value(at, value));
        }
        let (env, ops) = self.with_tree(frame, env, ops);
        let level = self
            .types
            .escapes
            .closures
            .iter()
            .find(|(f, _)| *f == frame)
            .map_or(EscapeLevel::Escaping, |(_, l)| *l);
        let placement = match heap {
            true => ClosurePlacement::Heap,
            false => place(level, self.loops > 0),
        };
        let code = self.closure_code(frame);
        self.assign(
            ty,
            Rvalue::Closure {
                code,
                env,
                captures: ops,
                placement,
            },
        )
    }

    /// A call, a method call, or a field access that calls a function.
    pub(super) fn call(&mut self, expr: ExprId, tail: bool) -> Operand<'db> {
        let body = self.body;
        let (receiver, args, fields): (Option<ExprId>, &[ExprId], Option<&[FieldArg<'db>]>) =
            match body.expr(expr) {
                Expr::Call { args, fields, .. } | Expr::TypedCall { args, fields, .. } => {
                    (None, args, fields.as_deref())
                }
                Expr::MethodCall {
                    receiver,
                    args,
                    fields,
                    ..
                } => (Some(*receiver), args, fields.as_deref()),
                Expr::Field { receiver, .. } => (Some(*receiver), &[], None),
                _ => unreachable!("only calls are called"),
            };
        let positional: Vec<ExprId> = receiver.into_iter().chain(args.iter().copied()).collect();
        match self.types.callee(expr).cloned() {
            Some(callee @ (Callee::Function(_) | Callee::Instance(_) | Callee::Slot(_))) => {
                match self.callee_instance(&callee) {
                    Some(instance) => {
                        self.call_function(expr, &instance, &positional, fields, tail)
                    }
                    None => self.trap(TrapKind::Error, Some(expr)),
                }
            }
            Some(Callee::Construct(ty)) => {
                let ty = self.subst(ty);
                self.construct(expr, ty, &positional, fields)
            }
            Some(Callee::Update(ty)) => {
                // The receiver spread, then the list (§6.7.1).
                let ty = self.subst(ty);
                let list: Vec<FieldArg<'db>> = receiver
                    .map(FieldArg::Spread)
                    .into_iter()
                    .chain(fields.unwrap_or_default().iter().cloned())
                    .collect();
                self.record(expr, ty, &[], &list)
            }
            Some(Callee::Refine(ty)) => {
                let ty = self.subst(ty);
                self.refine(expr, ty, positional[0])
            }
            Some(Callee::Dispatch(dispatch)) => self.dispatch(expr, &dispatch, &positional, fields),
            Some(Callee::Value) => self.call_value(expr, tail),
            None => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    /// A call of a function value: a closure, a local function, a
    /// parameter or a field.
    fn call_value(&mut self, expr: ExprId, tail: bool) -> Operand<'db> {
        let db = self.db;
        let body = self.body;
        let (callee, fn_ty, args, fields) = match body.expr(expr) {
            Expr::Call {
                callee,
                args,
                fields,
            } => {
                let op = self.expr(*callee);
                (op, self.ty(*callee), args, fields)
            }
            Expr::MethodCall {
                receiver,
                name,
                args,
                fields,
                ..
            } => {
                let local = self.place_of(*receiver);
                let field = fields_of(db, self.program, self.ty(*receiver))
                    .and_then(|fs| fs.into_iter().find(|(n, _)| n == name));
                let Some((_, field_ty)) = field else {
                    return self.trap(TrapKind::Error, Some(expr));
                };
                let place = Place {
                    local,
                    path: vec![Step::Field(*name)],
                };
                let value = self.assign(field_ty, Rvalue::Read(place));
                (value, field_ty, args, fields)
            }
            _ => return self.trap(TrapKind::Error, Some(expr)),
        };
        let Some((params, result, _)) = fn_ty.as_fn(db) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let callee = self.typed(callee, fn_ty);
        let mut ops = Vec::new();
        for (&arg, &param) in args.iter().zip(params) {
            let op = self.expr(arg);
            ops.push(self.coerce(op, self.ty(arg), param));
        }
        // Named arguments build the last parameter (§5.6.2).
        if let (Some(fields), Some(&record)) = (fields, params.get(args.len())) {
            ops.push(self.record_value(expr, record, &[], fields));
        }
        if tail && result == self.result {
            self.terminate(Terminator::TailCallValue {
                callee,
                args: ops,
                site: expr,
            });
            return self.unit();
        }
        let dst = self.temp(result);
        let target = self.new_block();
        self.terminate(Terminator::CallValue {
            callee,
            args: ops,
            dst,
            target,
            site: expr,
            unwind: None,
            catch: None,
        });
        self.switch_to(target);
        Operand::Local(dst)
    }

    /// A lifted call (§4.6.1): the arguments are evaluated once, then a
    /// switch on the tag of each split argument reaches the call for its
    /// members, which gets them converted to the members' types.
    fn dispatch(
        &mut self,
        expr: ExprId,
        dispatch: &Dispatch<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Operand<'db> {
        let functions = match self.dispatch_functions(expr, dispatch, positional) {
            Ok(functions) => functions,
            Err(op) => return op,
        };
        let args: Vec<(Local, Ty<'db>)> = positional
            .iter()
            .map(|&arg| {
                let ty = self.ty(arg);
                let op = self.expr(arg);
                (self.materialize(op, ty), ty)
            })
            .collect();
        // Named arguments, once, after the positional ones: parameters of
        // every arm, or together the record that every arm's last
        // parameter is (§5.6.2).
        let named = match fields.filter(|f| !f.is_empty()) {
            None => Named::Params(Vec::new()),
            Some(fields) => {
                let params = self.instance_signature(&functions[0]).params;
                let simple: Option<Vec<(Name<'db>, ExprId)>> = fields
                    .iter()
                    .map(|f| match f {
                        FieldArg::Field { path, value } if path.len() == 1 => {
                            Some((path[0], *value))
                        }
                        _ => None,
                    })
                    .collect();
                let names: Vec<Name<'db>> = simple.iter().flatten().map(|(n, _)| *n).collect();
                match simple.filter(|_| named_places(&params, args.len(), &names).is_some()) {
                    Some(simple) => Named::Params(
                        simple
                            .into_iter()
                            .map(|(name, value)| {
                                let ty = self.ty(value);
                                let op = self.expr(value);
                                (name, self.materialize(op, ty), ty)
                            })
                            .collect(),
                    ),
                    None => {
                        let Some(record) = params.get(args.len()).map(|p| p.ty) else {
                            return self.trap(TrapKind::Error, Some(expr));
                        };
                        let op = self.record_value(expr, record, &[], fields);
                        Named::Record(self.materialize(op, record), record)
                    }
                }
            }
        };
        let dst = self.temp(self.ty(expr));
        let join = self.new_block();
        self.dispatch_arms(
            expr,
            dispatch,
            &functions,
            (&args, &named),
            &mut Vec::new(),
            dst,
            join,
        );
        self.switch_to(join);
        Operand::Local(dst)
    }

    /// The concrete instance each arm of a dispatch calls, or what stops
    /// it from being lowered.
    pub(super) fn dispatch_functions(
        &mut self,
        expr: ExprId,
        dispatch: &Dispatch<'db>,
        positional: &[ExprId],
    ) -> Result<Vec<Instance<'db>>, Operand<'db>> {
        let mut functions = Vec::new();
        for arm in &dispatch.arms {
            let Some(instance) = self.callee_instance(&arm.callee) else {
                return Err(self.trap(TrapKind::Error, Some(expr)));
            };
            if self.instance_signature(&instance).params.len() < positional.len() {
                return Err(self.trap(TrapKind::Error, Some(expr)));
            }
            functions.push(instance);
        }
        Ok(functions)
    }

    /// The switch on the split argument at `indices.len()`, or the call
    /// for the members at `indices`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn dispatch_arms(
        &mut self,
        expr: ExprId,
        dispatch: &Dispatch<'db>,
        functions: &[Instance<'db>],
        (args, named): (&[(Local, Ty<'db>)], &Named<'db>),
        indices: &mut Vec<usize>,
        dst: Local,
        join: BlockId,
    ) {
        let level = indices.len();
        if level < dispatch.args.len() {
            let members: Vec<Ty<'db>> = dispatch.members[level]
                .iter()
                .map(|&m| self.subst(m))
                .collect();
            let blocks: Vec<BlockId> = members.iter().map(|_| self.new_block()).collect();
            let fail = self.new_block();
            self.terminate(Terminator::Switch {
                place: Place::local(args[dispatch.args[level]].0),
                cases: members.into_iter().zip(blocks.iter().copied()).collect(),
                otherwise: fail,
            });
            self.switch_to(fail);
            self.trap(TrapKind::NoMatch, Some(expr));
            for (i, block) in blocks.into_iter().enumerate() {
                self.switch_to(block);
                indices.push(i);
                self.dispatch_arms(expr, dispatch, functions, (args, named), indices, dst, join);
                indices.pop();
            }
            return;
        }
        let index = indices
            .iter()
            .zip(&dispatch.members)
            .fold(0, |n, (&i, members)| n * members.len() + i);
        let function = &functions[index];
        let result = self.subst(dispatch.arms[index].result);
        let params = self.instance_signature(function).params;
        // The arguments go where a call puts them; the rest take their
        // defaults.
        let mut given: Vec<Option<Operand<'db>>> = vec![None; params.len()];
        let places = match named {
            Named::Params(named) => {
                let names: Vec<Name<'db>> = named.iter().map(|&(n, ..)| n).collect();
                let Some(places) = named_places(&params, args.len(), &names) else {
                    self.trap(TrapKind::Error, Some(expr));
                    return;
                };
                for (&(_, local, ty), &place) in named.iter().zip(&places[args.len()..]) {
                    given[place] = Some(self.coerce(Operand::Local(local), ty, params[place].ty));
                }
                places[..args.len()].to_vec()
            }
            Named::Record(local, ty) => {
                let Some(last) = params.get(args.len()) else {
                    self.trap(TrapKind::Error, Some(expr));
                    return;
                };
                given[args.len()] = Some(self.coerce(Operand::Local(*local), *ty, last.ty));
                (0..args.len()).collect()
            }
        };
        for (k, (&(local, ty), &place)) in args.iter().zip(&places).enumerate() {
            let (op, from) = match dispatch.args.iter().position(|&a| a == k) {
                Some(level) => {
                    let member = self.subst(dispatch.members[level][indices[level]]);
                    (self.coerce(Operand::Local(local), ty, member), member)
                }
                None => (Operand::Local(local), ty),
            };
            given[place] = Some(self.coerce(op, from, params[place].ty));
        }
        let op = match self.primitive_of(function) {
            Some(primitive) => {
                let ops = given.into_iter().flatten().collect();
                self.primitive_ops(expr, primitive, result, ops)
            }
            None => {
                let Some(func) = self.callable(expr, function) else {
                    return;
                };
                if self
                    .fill_defaults(expr, func, &params, &mut given)
                    .is_none()
                {
                    self.trap(TrapKind::Error, Some(expr));
                    return;
                }
                let ops = given.into_iter().flatten().collect();
                let out = self.temp(result);
                let target = self.new_block();
                self.terminate(Terminator::Call {
                    func,
                    args: ops,
                    dst: out,
                    target,
                    site: expr,
                    unwind: None,
                    catch: None,
                });
                self.switch_to(target);
                Operand::Local(out)
            }
        };
        self.assign_to(dst, op, result);
        self.terminate(Terminator::Jump(join));
    }

    /// A call of a concrete instance: a declared function, an instance of
    /// a generic one, or what fills a slot.
    fn call_function(
        &mut self,
        expr: ExprId,
        instance: &Instance<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
        tail: bool,
    ) -> Operand<'db> {
        if fields.is_none()
            && let Some(primitive) = self.primitive_of(instance)
        {
            return self.primitive_call(expr, primitive, positional);
        }
        if fields.is_none()
            && let Some(value) = self.lazy_read(instance)
            && let [lazy] = positional
        {
            let op = self.expr(*lazy);
            let ty = self.ty(*lazy);
            let lazy = Operand::Local(self.materialize(op, ty));
            return self.lazy_value(expr, lazy, value);
        }
        if fields.is_none()
            && let Some(access) = self.cell_access(instance)
        {
            return self.ref_access(expr, access, instance, positional);
        }
        if fields.is_none()
            && let [value] = positional
            && let Some(mapping) = self.type_mapping(instance)
        {
            if mapping == "number" {
                return self.number_value(expr, *value);
            }
            return self.map_type(expr, mapping, *value);
        }
        // A walk that meets parts with functions of their own has code.
        if fields.is_none()
            && let Some(op) = derive::value_op(self.db, instance.function)
            && let Some(&ty) = instance.args.first()
            && self.reaches(op, ty)
        {
            let ops = positional.iter().map(|&arg| self.expr(arg)).collect();
            return self.derived(op, ty, ops);
        }
        if fields.is_none()
            && let Some(intrinsic) = self.intrinsic(instance)
        {
            let ops = positional.iter().map(|&arg| self.expr(arg)).collect();
            return self.assign(self.ty(expr), Rvalue::Intrinsic(intrinsic, ops));
        }
        let Some(func) = self.callable(expr, instance) else {
            return self.unit();
        };
        let sig = self.instance_signature(instance);
        let Some(args) = self.arguments(expr, func, &sig, positional, fields) else {
            return self.trap(TrapKind::Error, Some(expr));
        };
        let ty = self.ty(expr);
        if tail && ty == self.result {
            self.terminate(Terminator::TailCall {
                func,
                args,
                site: expr,
            });
            return self.unit();
        }
        let dst = self.temp(ty);
        let target = self.new_block();
        self.terminate(Terminator::Call {
            func,
            args,
            dst,
            target,
            site: expr,
            unwind: None,
            catch: None,
        });
        self.switch_to(target);
        Operand::Local(dst)
    }

    /// The arguments for the parameters of the code `func`, in the order
    /// they are written: positional, then named, or named arguments
    /// building the last parameter, a record (§5.6.2). A parameter left out
    /// takes its default, computed by the default's code from the
    /// parameters before it, after the written arguments. None when the
    /// arguments do not fit, which inference reported.
    fn arguments(
        &mut self,
        expr: ExprId,
        func: InstanceKey<'db>,
        sig: &Signature<'db>,
        positional: &[ExprId],
        fields: Option<&[FieldArg<'db>]>,
    ) -> Option<Vec<Operand<'db>>> {
        let db = self.db;
        let params = &sig.params;
        let named: Option<Vec<_>> = fields
            .unwrap_or(&[])
            .iter()
            .map(|f| match f {
                FieldArg::Field { path, value } if path.len() == 1 => Some((path[0], *value)),
                _ => None,
            })
            .collect();
        // As inference places them: the named arguments, then the
        // positional ones.
        let mut slots: Vec<Option<ExprId>> = vec![None; params.len()];
        let mut fits = positional.len() <= params.len();
        if fits {
            match &named {
                Some(named) => {
                    for &(name, value) in named {
                        match params.iter().position(|p| p.name == Some(name)) {
                            Some(i) if slots[i].is_none() => slots[i] = Some(value),
                            _ => fits = false,
                        }
                    }
                }
                None => fits = false,
            }
            let defaults: Vec<bool> = params.iter().map(|p| p.default).collect();
            let taken: Vec<bool> = slots.iter().map(Option::is_some).collect();
            match crag_types::place_positional(&defaults, &taken, positional.len()) {
                Some(places) => {
                    for (&arg, i) in positional.iter().zip(places) {
                        slots[i] = Some(arg);
                    }
                }
                None => fits = false,
            }
        }
        if fits
            && slots
                .iter()
                .zip(params)
                .all(|(s, p)| s.is_some() || p.default)
        {
            let mut ops: Vec<Option<Operand<'db>>> = vec![None; params.len()];
            let order = positional
                .iter()
                .chain(named.iter().flatten().map(|(_, v)| v));
            for &arg in order {
                let i = slots.iter().position(|s| *s == Some(arg))?;
                let op = self.expr(arg);
                ops[i] = Some(self.coerce(op, self.ty(arg), params[i].ty));
            }
            self.fill_defaults(expr, func, params, &mut ops)?;
            return ops.into_iter().collect();
        }
        let last = params.last()?;
        let builds = params.len() == positional.len() + 1
            && fields.is_some()
            && fields_of(db, self.program, last.ty).is_some();
        if !builds || !self.record_fits(last.ty, &[], fields.unwrap_or(&[])) {
            return None;
        }
        let mut ops = Vec::new();
        for (&arg, param) in positional.iter().zip(params) {
            let op = self.expr(arg);
            ops.push(self.coerce(op, self.ty(arg), param.ty));
        }
        ops.push(self.record_value(expr, last.ty, &[], fields.unwrap_or(&[])));
        Some(ops)
    }

    /// Gives each parameter without an argument its default, which takes
    /// the parameters before it, as the call does.
    fn fill_defaults(
        &mut self,
        expr: ExprId,
        func: InstanceKey<'db>,
        params: &[SigParam<'db>],
        ops: &mut [Option<Operand<'db>>],
    ) -> Option<()> {
        if ops.iter().all(Option::is_some) {
            return Some(());
        }
        let db = self.db;
        let Owner::Item(function) = *func.owner(db) else {
            return None;
        };
        let callee = hir_body(db, self.program, Owner::Item(function));
        for i in 0..params.len() {
            if ops[i].is_some() {
                continue;
            }
            let before = (0..i)
                .map(|k| {
                    let op = ops[k].clone()?;
                    let local = self.materialize(op, params[k].ty);
                    ops[k] = Some(Operand::Local(local));
                    Some(Operand::Local(local))
                })
                .collect::<Option<Vec<_>>>()?;
            let code = func.with_entry(db, Entry::Default(callee.params.get(i)?.default?));
            let local = self.call_code(code, before, params[i].ty, expr);
            ops[i] = Some(Operand::Local(local));
        }
        Some(())
    }

    /// The type mapping function of the prelude an instance is, if it is
    /// one (§8.4).
    fn type_mapping(&self, instance: &Instance<'db>) -> Option<&'static str> {
        let db = self.db;
        let function = instance.function;
        if function.module(db).path(db) != crag_hir::PRELUDE {
            return None;
        }
        match function.name(db).text(db).as_str() {
            "discard" => Some("discard"),
            "check" => Some("check"),
            "expect" => Some("expect"),
            "number" => Some("number"),
            _ => None,
        }
    }

    /// `x.number()`: the `Float`, or a `NotFinite` trap at the call that
    /// names the tag it met (§3.1.4).
    fn number_value(&mut self, expr: ExprId, value: ExprId) -> Operand<'db> {
        let db = self.db;
        let ty = self.ty(value);
        let result = self.ty(expr);
        let subject = self.place_of(value);
        let tags: Vec<Ty<'db>> = ty
            .members(db)
            .into_iter()
            .filter(|m| !matches!(m.as_builtin(db), Some((Builtin::Float, _))))
            .collect();
        let raises: Vec<BlockId> = tags.iter().map(|_| self.new_block()).collect();
        let ok = self.new_block();
        self.terminate(Terminator::Switch {
            place: Place::local(subject),
            cases: tags.iter().copied().zip(raises.iter().copied()).collect(),
            otherwise: ok,
        });
        for (&tag, &raise) in tags.iter().zip(&raises) {
            self.switch_to(raise);
            self.terminate(Terminator::Trap {
                kind: TrapKind::NotFinite,
                site: Some(expr),
                detail: Some(tag.display(db)),
                catch: None,
            });
        }
        self.switch_to(ok);
        let out = self.temp(result);
        self.assign_to(out, Operand::Local(subject), ty);
        Operand::Local(out)
    }

    /// `~x`, `?x` and `!!x`: the value's errors kept, or its success with
    /// its errors as `Empty` or as a trap (§8.4).
    fn map_type(&mut self, expr: ExprId, mapping: &str, value: ExprId) -> Operand<'db> {
        let (db, program) = (self.db, self.program);
        let ty = self.ty(value);
        let result = self.ty(expr);
        let subject = self.place_of(value);
        let errors = crag_types::error_members(db, program, ty);
        let successes = crag_types::success_members(db, program, ty);
        let out = self.temp(result);
        let (ok, failed, join) = (self.new_block(), self.new_block(), self.new_block());
        // `!!` names the error it met, so each error gets a trap of its own.
        let members = errors.members(db);
        let raises: Vec<BlockId> = match mapping {
            "expect" => members.iter().map(|_| self.new_block()).collect(),
            _ => Vec::new(),
        };
        let cases = members
            .iter()
            .enumerate()
            .map(|(i, &m)| (m, raises.get(i).copied().unwrap_or(failed)))
            .collect();
        self.terminate(Terminator::Switch {
            place: Place::local(subject),
            cases,
            otherwise: ok,
        });
        for (&m, &raise) in members.iter().zip(&raises) {
            self.switch_to(raise);
            self.terminate(Terminator::Trap {
                kind: TrapKind::Expectation,
                site: Some(expr),
                detail: Some(m.display(db)),
                catch: None,
            });
        }
        // A member of the subject narrowed to `to`, and given as `result`.
        let give = |b: &mut Self, to: Ty<'db>| {
            let narrowed = b.temp(to);
            b.assign_to(narrowed, Operand::Local(subject), ty);
            b.assign_to(out, Operand::Local(narrowed), to);
            b.terminate(Terminator::Jump(join));
        };
        self.switch_to(ok);
        match mapping {
            "discard" => {
                let unit = Ty::unit(db);
                self.assign_to(out, self.unit(), unit);
                self.terminate(Terminator::Jump(join));
            }
            _ => give(self, successes),
        }
        self.switch_to(failed);
        match mapping {
            "discard" => give(self, errors),
            "check" => {
                let empty_item = prelude_item(db, program, "Empty");
                let empty = result.members(db).into_iter().find(
                    |m| matches!(m.kind(db), TyKind::Named(item, _) if Some(*item) == empty_item),
                );
                match empty {
                    Some(empty) => {
                        self.assign_to(out, Operand::Const(Constant::Tag(empty)), empty);
                        self.terminate(Terminator::Jump(join));
                    }
                    None => {
                        self.trap(TrapKind::Error, Some(expr));
                    }
                }
            }
            _ => {
                self.trap(TrapKind::Expectation, Some(expr));
            }
        }
        self.switch_to(join);
        Operand::Local(out)
    }

    /// The operation an operator function of the prelude stands for, if
    /// it is one: a builtin on numbers, or `equals` of strings and bytes.
    fn primitive(&self, function: ItemId<'db>) -> Option<Primitive> {
        let db = self.db;
        if function.module(db).path(db) != PRELUDE
            || hir_body(db, self.program, Owner::Item(function))
                .root
                .is_some()
        {
            return None;
        }
        let sig = signature(db, self.program, function);
        let builtin = |ty: Ty<'db>| match ty.kind(db) {
            TyKind::Builtin(b, args) if args.is_empty() => Some(*b),
            _ => None,
        };
        let params: Vec<Builtin> = sig
            .params
            .iter()
            .map(|p| builtin(p.ty))
            .collect::<Option<_>>()?;
        let result = sig.result.and_then(builtin);
        let number =
            |b: Builtin| b.int_range().is_some() || matches!(b, Builtin::Float | Builtin::Fixed(_));
        let name = function.name(db).text(db).as_str();
        let arith = |op: BinOp, checked: bool| -> Option<Primitive> {
            let [a, b] = params.as_slice() else {
                return None;
            };
            let (a, b, ty) = (*a, *b, result?);
            let fits = match (a, b) {
                _ if !number(a) || !number(b) => false,
                (Builtin::Fixed(_), Builtin::Fixed(_)) => {
                    a == b && matches!(op, BinOp::Add | BinOp::Sub | BinOp::Rem)
                }
                (Builtin::Fixed(_), _) | (_, Builtin::Fixed(_)) => {
                    op == BinOp::Mul && b.int_range().or(a.int_range()).is_some()
                }
                _ => a == b,
            };
            (fits && (checked || ty != Builtin::Float)).then_some(Primitive::Arith {
                op,
                ty,
                checked,
            })
        };
        let compare = |op: CmpOp| -> Option<Primitive> {
            let [a, b] = params.as_slice() else {
                return None;
            };
            let text = matches!(a, Builtin::Str | Builtin::Bytes) && op == CmpOp::Eq;
            let ordered = number(*a) || *a == Builtin::CodePoint;
            (a == b && (ordered || text)).then_some(Primitive::Compare(op, *a))
        };
        let text = |b: Builtin| matches!(b, Builtin::Str | Builtin::Bytes);
        match name {
            "add" if matches!(params.as_slice(), [a, b] if text(*a) && a == b) => {
                Some(Primitive::Concat)
            }
            "bytes" if params == [Builtin::Str] => Some(Primitive::Concat),
            "add" => arith(BinOp::Add, true),
            "subtract" => arith(BinOp::Sub, true),
            "multiply" => arith(BinOp::Mul, true),
            "divide" => arith(BinOp::Div, true),
            "remainder" => arith(BinOp::Rem, true),
            "addWrapping" => arith(BinOp::Add, false),
            "subtractWrapping" => arith(BinOp::Sub, false),
            "multiplyWrapping" => arith(BinOp::Mul, false),
            "negate" => match params.as_slice() {
                [a] if number(*a) => Some(Primitive::Negate(*a)),
                _ => None,
            },
            // The conversions of numbers build on these (§19.13).
            "numberSame" | "numberWrap" | "intToFloat" | "floatToInt" | "floatFloor"
            | "floatCeil" | "floatTrunc" => {
                let ([from], Some(to)) = (params.as_slice(), result) else {
                    return None;
                };
                let op = match name {
                    "numberSame" => CastOp::Same,
                    "numberWrap" => CastOp::Wrap(to),
                    "intToFloat" => CastOp::IntToFloat,
                    "floatToInt" => CastOp::FloatToInt,
                    "floatFloor" => CastOp::Floor,
                    "floatCeil" => CastOp::Ceil,
                    _ => CastOp::Trunc,
                };
                Some(Primitive::Cast(op, *from))
            }
            "equals" => compare(CmpOp::Eq),
            "lessThan" => compare(CmpOp::Lt),
            "lessOrEqual" => compare(CmpOp::Le),
            "greaterThan" => compare(CmpOp::Gt),
            "greaterOrEqual" => compare(CmpOp::Ge),
            _ => None,
        }
    }

    fn primitive_call(
        &mut self,
        expr: ExprId,
        primitive: Primitive,
        args: &[ExprId],
    ) -> Operand<'db> {
        let ty = self.ty(expr);
        // `-1` is a constant, so `Int8.min` can be written.
        if let (Primitive::Negate(_), [x]) = (primitive, args)
            && let Expr::Literal(literal) = self.body.expr(*x)
        {
            let negative = !self.body.is_negative(*x);
            return Operand::Const(self.literal(literal, ty, negative));
        }
        let ops = args.iter().map(|&arg| self.expr(arg)).collect();
        self.primitive_ops(expr, primitive, ty, ops)
    }

    /// The operation of a primitive on operands, giving a `ty`.
    pub(super) fn primitive_ops(
        &mut self,
        expr: ExprId,
        primitive: Primitive,
        ty: Ty<'db>,
        ops: Vec<Operand<'db>>,
    ) -> Operand<'db> {
        if primitive == Primitive::Concat {
            return self.assign(ty, Rvalue::Concat(ops));
        }
        let mut ops = ops.into_iter();
        match (primitive, ops.next(), ops.next()) {
            (Primitive::Arith { op, ty: b, checked }, Some(a), Some(c)) => {
                let check = checked.then_some(expr);
                self.assign(
                    ty,
                    Rvalue::Binary {
                        op,
                        ty: b,
                        a,
                        b: c,
                        check,
                    },
                )
            }
            (Primitive::Negate(b), Some(a), None) => {
                let rvalue = match b {
                    // -0.0 must stay negative zero; -1.0 * x keeps the sign.
                    Builtin::Float => Rvalue::Binary {
                        op: BinOp::Mul,
                        ty: b,
                        a: Operand::Const(Constant::Float((-1.0f64).to_bits())),
                        b: a,
                        check: Some(expr),
                    },
                    _ => Rvalue::Binary {
                        op: BinOp::Sub,
                        ty: b,
                        a: int(0),
                        b: a,
                        check: Some(expr),
                    },
                };
                self.assign(ty, rvalue)
            }
            (Primitive::Compare(op, b), Some(a), Some(c)) => {
                self.assign(ty, Rvalue::Compare { op, ty: b, a, b: c })
            }
            (Primitive::Cast(op, from), Some(value), None) => {
                self.assign(ty, Rvalue::Cast { op, from, value })
            }
            _ => self.trap(TrapKind::Error, Some(expr)),
        }
    }

    /// A call of a type: a tag's value, or a record built from arguments.
    /// Calls code with arguments and gives the local of its result, of
    /// type `ty`.
    pub(super) fn call_code(
        &mut self,
        func: InstanceKey<'db>,
        args: Vec<Operand<'db>>,
        ty: Ty<'db>,
        site: ExprId,
    ) -> Local {
        let dst = self.temp(ty);
        let target = self.new_block();
        self.terminate(Terminator::Call {
            func,
            args,
            dst,
            target,
            site,
            unwind: None,
            catch: None,
        });
        self.switch_to(target);
        dst
    }
}
