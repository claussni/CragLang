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

//! Intrinsics of the prelude: the operations on strings, numbers,
//! collections and the rest that code does inline or through one
//! runtime function.

use super::*;

impl<'a, 'db> Lower<'a, 'db> {
    /// The runtime call of an intrinsic, and its result's words; `ty` is
    /// the result's type.
    pub(super) fn intrinsic(
        &mut self,
        intrinsic: Intrinsic<'db>,
        args: &[Operand<'db>],
        ty: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        let int = Ty::builtin(self.db, Builtin::Int);
        match (intrinsic, args) {
            (Intrinsic::RefNew, [value]) => {
                let value_ty = self.cell_value_ty(ty)?;
                self.describe(ty)?;
                let words = self.ref_value(value, value_ty)?;
                let ptr = self.alloc(HEADER_SIZE + REF_CELL_SIZE as u32, self.index(ty));
                let zero = self.constant(0);
                let header = HEADER_SIZE as i32;
                self.push(Inst::Store {
                    src: zero,
                    addr: ptr,
                    offset: header,
                });
                for (k, src) in self.pad(words).into_iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: header + 8 + 8 * k as i32,
                    });
                }
                Ok(vec![ptr])
            }
            (Intrinsic::RefRead, [cell]) => {
                let cell = self.cell_addr(cell)?;
                let out = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::RefRead, vec![cell, out])])
            }
            (Intrinsic::RefDone, []) => {
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::RefDone,
                    args: Vec::new(),
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::RefCommit, [cell, version, value]) => {
                let cell_ty = self.operand_ty(cell, ty);
                let value_ty = self.cell_value_ty(cell_ty)?;
                let list = self.cell_list(value_ty)?;
                let cell = self.cell_addr(cell)?;
                let version = word(&self.operand(version, int)?)?;
                let words = self.ref_value(value, value_ty)?;
                let [w0, w1] = self.pad(words);
                Ok(vec![self.runtime(
                    RuntimeFn::RefCommit,
                    vec![cell, version, list, w0, w1],
                )])
            }
            (Intrinsic::ExtNew, [value]) => {
                let value_ty = self.cell_value_ty(ty)?;
                self.describe(ty)?;
                let words = self.operand(value, value_ty)?;
                let ptr = self.alloc(HEADER_SIZE + 24, self.index(ty));
                let lock = self.runtime(RuntimeFn::ExtNew, Vec::new());
                let header = HEADER_SIZE as i32;
                self.push(Inst::Store {
                    src: lock,
                    addr: ptr,
                    offset: header,
                });
                for (k, src) in self.pad(words).into_iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: header + 8 + 8 * k as i32,
                    });
                }
                Ok(vec![ptr])
            }
            (Intrinsic::ExtLock | Intrinsic::ExtUnlock, [cell]) => {
                let ptr = self.box_of(cell)?;
                let lock = self.load(ptr, HEADER_SIZE as i32);
                let (func, region) = match intrinsic {
                    Intrinsic::ExtLock => (RuntimeFn::ExtLock, RuntimeFn::EnterNoCancel),
                    _ => (RuntimeFn::ExtUnlock, RuntimeFn::ExitNoCancel),
                };
                // The lock is where a cancelled task stops; the closure
                // runs where cancellation waits.
                self.push(Inst::CallRuntime {
                    func,
                    args: vec![lock],
                    dsts: Vec::new(),
                });
                self.push(Inst::CallRuntime {
                    func: region,
                    args: Vec::new(),
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::ExtValue, [cell]) => {
                let ptr = self.box_of(cell)?;
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                let at = HEADER_SIZE as i32 + 8;
                Ok((0..words)
                    .map(|k| self.load(ptr, at + 8 * k as i32))
                    .collect())
            }
            (Intrinsic::ExtStore, [cell, value]) => {
                let cell_ty = self.operand_ty(cell, ty);
                let Some((Builtin::Ext, &[value_ty])) = cell_ty.as_builtin(self.db) else {
                    return Err("cells of this type");
                };
                let value_layout = layout(self.db, self.program, value_ty);
                let words = value_layout.ok_or("values of this type")?.words();
                let ptr = self.box_of(cell)?;
                let new = self.operand(value, value_ty)?;
                let at = HEADER_SIZE as i32 + 8;
                let old: Vec<VReg> = (0..words)
                    .map(|k| self.load(ptr, at + 8 * k as i32))
                    .collect();
                for (k, &src) in new.iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: at + 8 * k as i32,
                    });
                }
                self.count_words(value_layout, value_ty, &old, Self::release)?;
                Ok(Vec::new())
            }
            (Intrinsic::LazyNew, [code]) => {
                let Some((Builtin::Lazy, &[value_ty])) = ty.as_builtin(self.db) else {
                    return Err("lazy values of this type");
                };
                self.describe(ty)?;
                let code_ty = self.operand_ty(code, ty);
                let [code, env] = self.operand(code, code_ty)?[..] else {
                    return Err("lazy values of this type");
                };
                let list = self.cell_list(value_ty)?;
                let cell = self.runtime(RuntimeFn::LazyNew, vec![list]);
                let ptr = self.alloc(HEADER_SIZE + 24, self.index(ty));
                let header = HEADER_SIZE as i32;
                for (k, src) in [cell, code, env].into_iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: ptr,
                        offset: header + 8 * k as i32,
                    });
                }
                Ok(vec![ptr])
            }
            (Intrinsic::LazyGet, [lazy]) => {
                let ptr = self.box_of(lazy)?;
                let cell = self.load(ptr, HEADER_SIZE as i32);
                let out = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::LazyGet, vec![cell, out])])
            }
            (Intrinsic::LazyValue, []) => {
                let out = self.scratch();
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                Ok((0..words).map(|k| self.load(out, 8 * k as i32)).collect())
            }
            (Intrinsic::LazyCode, [lazy]) => {
                let ptr = self.box_of(lazy)?;
                let header = HEADER_SIZE as i32;
                Ok(vec![
                    self.load(ptr, header + 8),
                    self.load(ptr, header + 16),
                ])
            }
            (Intrinsic::LazySet, [lazy, value]) => {
                let value_ty = self.operand_ty(value, ty);
                let value_layout = layout(self.db, self.program, value_ty);
                let ptr = self.box_of(lazy)?;
                let cell = self.load(ptr, HEADER_SIZE as i32);
                let words = self.operand(value, value_ty)?;
                // The cell takes references of its own; the reader keeps
                // the value.
                self.count_words(value_layout, value_ty, &words, Self::retain)?;
                let [w0, w1] = self.pad(words);
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::LazySet,
                    args: vec![cell, w0, w1],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::LazyTrap, []) => {
                let out = self.scratch();
                let kind = self.load(out, 0);
                let position = self.constant(NO_POSITION as i64);
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::Trap,
                    args: vec![kind, position],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::StreamNew { value }, [capacity]) => {
                let capacity = word(&self.operand(capacity, int)?)?;
                let list = self.cell_list(value)?;
                let ends = self.runtime2(RuntimeFn::StreamNew, vec![capacity, list]);
                // The source waits in the scratch words for `StreamPeer`.
                let out = self.scratch();
                self.push(Inst::Store {
                    src: ends[1],
                    addr: out,
                    offset: 0,
                });
                self.handle_box(ty, ends[0])
            }
            (Intrinsic::StreamPeer, []) => {
                let out = self.scratch();
                let source = self.load(out, 0);
                self.handle_box(ty, source)
            }
            (Intrinsic::StreamPut { wait }, [end, value]) => {
                let value_ty = self.operand_ty(value, ty);
                let value_layout = layout(self.db, self.program, value_ty);
                let end = self.handle_of(end)?;
                let words = self.operand(value, value_ty)?;
                // The value's references go with it once it is sent; those
                // taken for it are given back otherwise.
                self.count_words(value_layout, value_ty, &words, Self::retain)?;
                let [w0, w1] = self.pad(words.clone());
                let func = if wait {
                    RuntimeFn::StreamPut
                } else {
                    RuntimeFn::StreamTryPut
                };
                let status = self.runtime(func, vec![end, w0, w1]);
                let (unsent, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: status,
                        then: unsent,
                        otherwise: done,
                    },
                    Some(unsent),
                );
                self.count_words(value_layout, value_ty, &words, Self::release)?;
                self.end(Term::Jump(done), Some(done));
                Ok(vec![status])
            }
            (Intrinsic::StreamNext, [end]) => {
                let end = self.handle_of(end)?;
                let out = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::StreamNext, vec![end, out])])
            }
            (Intrinsic::StreamValue, []) => {
                let out = self.scratch();
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                Ok((0..words).map(|k| self.load(out, 8 * k as i32)).collect())
            }
            (
                Intrinsic::StreamClose
                | Intrinsic::HubSeal
                | Intrinsic::HubSink
                | Intrinsic::HubSource,
                [handle],
            ) => {
                let handle = self.handle_of(handle)?;
                let func = match intrinsic {
                    Intrinsic::StreamClose => RuntimeFn::StreamClose,
                    Intrinsic::HubSeal => RuntimeFn::HubSeal,
                    Intrinsic::HubSink => RuntimeFn::HubSink,
                    _ => RuntimeFn::HubSource,
                };
                if matches!(intrinsic, Intrinsic::StreamClose | Intrinsic::HubSeal) {
                    self.push(Inst::CallRuntime {
                        func,
                        args: vec![handle],
                        dsts: Vec::new(),
                    });
                    return Ok(Vec::new());
                }
                let end = self.runtime(func, vec![handle]);
                self.handle_box(ty, end)
            }
            (Intrinsic::HubNew { value }, [capacity, kind]) => {
                let capacity = word(&self.operand(capacity, int)?)?;
                let kind = word(&self.operand(kind, int)?)?;
                let list = self.cell_list(value)?;
                let hub = self.runtime(RuntimeFn::HubNew, vec![capacity, list, kind]);
                self.handle_box(ty, hub)
            }
            (Intrinsic::HubRelease, [hub, n]) => {
                let hub = self.handle_of(hub)?;
                let n = word(&self.operand(n, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::HubRelease,
                    args: vec![hub, n],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::IoListen | Intrinsic::IoAccept | Intrinsic::IoSocket, args) => {
                let (func, args) = match (intrinsic, args) {
                    (Intrinsic::IoListen, [port]) => {
                        (RuntimeFn::IoListen, vec![word(&self.operand(port, int)?)?])
                    }
                    (Intrinsic::IoAccept, [socket]) => {
                        (RuntimeFn::IoAccept, vec![self.handle_of(socket)?])
                    }
                    (Intrinsic::IoSocket, []) => (RuntimeFn::IoSocket, Vec::new()),
                    _ => return Err("this operation of the runtime"),
                };
                let out = self.runtime2(func, args);
                Ok(vec![self.fd_or_error(out[0], out[1])])
            }
            (Intrinsic::IoOwn, [fd]) => {
                let fd = word(&self.operand(fd, int)?)?;
                self.handle_box(ty, fd)
            }
            (Intrinsic::IoPort, [socket]) => {
                let fd = self.handle_of(socket)?;
                Ok(vec![self.runtime(RuntimeFn::IoPort, vec![fd])])
            }
            (Intrinsic::IoConnect, [socket, port]) => {
                let fd = self.handle_of(socket)?;
                let port = word(&self.operand(port, int)?)?;
                let out = self.runtime2(RuntimeFn::IoConnectLocal, vec![fd, port]);
                Ok(vec![out[1]])
            }
            (Intrinsic::IoRead, [socket, max]) => {
                let fd = self.handle_of(socket)?;
                let max = word(&self.operand(max, int)?)?;
                let buffer = self.runtime(RuntimeFn::IoBuffer, vec![max]);
                let header = self.constant(i64::from(HEADER_SIZE));
                let data = self.bin(LirBin::Add, buffer, header);
                let out = self.runtime2(RuntimeFn::IoRead, vec![fd, data, max]);
                let (n, errno) = (out[0], out[1]);
                // An end or an error keeps no bytes.
                let zero = self.constant(0);
                let failed = self.cmp(Cond::Ne, errno, zero);
                let count = self.reg();
                self.push(Inst::Select {
                    dst: count,
                    cond: failed,
                    a: zero,
                    b: n,
                });
                let bytes = self.runtime2(RuntimeFn::IoBytes, vec![buffer, count]);
                let scratch = self.scratch();
                for (k, &src) in bytes.iter().enumerate() {
                    self.push(Inst::Store {
                        src,
                        addr: scratch,
                        offset: 8 * k as i32,
                    });
                }
                Ok(vec![self.fd_or_error(n, errno)])
            }
            (Intrinsic::IoReadBytes, []) => {
                let scratch = self.scratch();
                Ok(vec![self.load(scratch, 0), self.load(scratch, 8)])
            }
            (Intrinsic::IoWrite, [socket, bytes, left]) => {
                let fd = self.handle_of(socket)?;
                let bytes_ty = self.operand_ty(bytes, ty);
                let [w0, w1] = self.operand(bytes, bytes_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let left = word(&self.operand(left, int)?)?;
                let out = self.runtime2(RuntimeFn::IoWriteBytes, vec![fd, w0, w1, left]);
                Ok(vec![self.fd_or_error(out[0], out[1])])
            }
            (Intrinsic::IoPrint, [text, newline]) => {
                let text_ty = self.operand_ty(text, ty);
                let [w0, w1] = self.operand(text, text_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let newline = word(&self.operand(newline, int)?)?;
                Ok(vec![
                    self.runtime(RuntimeFn::IoPrint, vec![w0, w1, newline]),
                ])
            }
            (Intrinsic::IoFault | Intrinsic::TrapWith(_), []) => {
                let kind = match intrinsic {
                    Intrinsic::TrapWith(kind) => self.constant(i64::from(kind)),
                    _ => self.constant(AbiTrap::Fault as i64),
                };
                let position = self.constant(crag_abi::NO_POSITION as i64);
                // `rt_trap` does not return.
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::Trap,
                    args: vec![kind, position],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::IoReadFile, [path]) => {
                let path_ty = self.operand_ty(path, ty);
                let [w0, w1] = self.operand(path, path_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                // The bytes wait in the scratch words for `IoReadBytes`.
                let scratch = self.scratch();
                Ok(vec![
                    self.runtime(RuntimeFn::IoReadFile, vec![w0, w1, scratch]),
                ])
            }
            (Intrinsic::IoSocketAny, []) => {
                let out = self.runtime2(RuntimeFn::IoSocketAny, Vec::new());
                Ok(vec![self.fd_or_error(out[0], out[1])])
            }
            (Intrinsic::IoConnectHost, [socket, host, port]) => {
                let fd = self.handle_of(socket)?;
                let host_ty = self.operand_ty(host, ty);
                let [w0, w1] = self.operand(host, host_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let port = word(&self.operand(port, int)?)?;
                let out = self.runtime2(RuntimeFn::IoConnectHost, vec![fd, w0, w1, port]);
                Ok(vec![out[1]])
            }
            (Intrinsic::TextUtf8, [bytes]) => {
                let bytes_ty = self.operand_ty(bytes, ty);
                let [w0, w1] = self.operand(bytes, bytes_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                Ok(vec![self.runtime(RuntimeFn::TextUtf8, vec![w0, w1])])
            }
            (Intrinsic::TextCast, [text]) => {
                let bytes = Ty::builtin(self.db, Builtin::Bytes);
                self.concat(std::slice::from_ref(text), bytes)
            }
            (Intrinsic::TextMeasure(op), [text]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let op = self.constant(i64::from(op));
                Ok(vec![self.runtime(RuntimeFn::TextMeasure, vec![op, w0, w1])])
            }
            (Intrinsic::TextAt(op), [text, at]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let at = word(&self.operand(at, int)?)?;
                let op = self.constant(i64::from(op));
                Ok(vec![self.runtime(RuntimeFn::TextAt, vec![op, w0, w1, at])])
            }
            (Intrinsic::TextFind(op), [text, part, from @ ..]) => {
                let [a0, a1] = self.text_words(text, ty)?;
                let [b0, b1] = self.text_words(part, ty)?;
                let op = self.constant(i64::from(op));
                let packed = match from {
                    [from] => {
                        let from = word(&self.operand(from, int)?)?;
                        let three = self.constant(3);
                        let shifted = self.bin(LirBin::Shl, from, three);
                        self.bin(LirBin::Or, shifted, op)
                    }
                    _ => op,
                };
                Ok(vec![self.runtime(
                    RuntimeFn::TextFind,
                    vec![a0, a1, b0, b1, packed],
                )])
            }
            (Intrinsic::TextMap(op), [text]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let op = self.constant(i64::from(op));
                Ok(self.runtime2(RuntimeFn::TextMap, vec![op, w0, w1]).to_vec())
            }
            (Intrinsic::TextSlice, [text, from, to]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let from = word(&self.operand(from, int)?)?;
                let to = word(&self.operand(to, int)?)?;
                Ok(self
                    .runtime2(RuntimeFn::TextSlice, vec![w0, w1, from, to])
                    .to_vec())
            }
            (Intrinsic::CodePointOp(op), [c]) => {
                let c_ty = self.operand_ty(c, ty);
                let c = word(&self.operand(c, c_ty)?)?;
                let op = self.constant(i64::from(op));
                Ok(vec![self.runtime(RuntimeFn::CodePointOp, vec![op, c])])
            }
            (Intrinsic::TextParse(op), [text, base @ ..]) => {
                let [w0, w1] = self.text_words(text, ty)?;
                let base = match base {
                    [base] => word(&self.operand(base, int)?)?,
                    _ => self.constant(10),
                };
                let op = self.constant(i64::from(op));
                let out = self.runtime2(RuntimeFn::TextParse, vec![op, w0, w1, base]);
                // The value waits in the scratch words for `TextParsed`.
                let scratch = self.scratch();
                self.push(Inst::Store {
                    src: out[0],
                    addr: scratch,
                    offset: 0,
                });
                Ok(vec![out[1]])
            }
            (Intrinsic::CCall(item), args) => self.c_call(item, args),
            (Intrinsic::COut(index), []) => {
                let buffer = self.c_buffer(index + 1);
                Ok(vec![self.load(buffer, 8 * index as i32)])
            }
            (Intrinsic::CClass, []) => {
                let scratch = self.scratch();
                Ok(vec![self.load(scratch, 0)])
            }
            (Intrinsic::CStrOf { nul }, [address]) => {
                let address = word(&self.operand(address, int)?)?;
                let nul = self.constant(i64::from(nul));
                Ok(self
                    .runtime2(RuntimeFn::CStrOf, vec![address, nul])
                    .to_vec())
            }
            (Intrinsic::TextParsed, []) => {
                let scratch = self.scratch();
                Ok(vec![self.load(scratch, 0)])
            }
            (Intrinsic::Word, [x]) => {
                let x_ty = self.operand_ty(x, ty);
                Ok(vec![word(&self.operand(x, x_ty)?)?])
            }
            (Intrinsic::ValueOp { op, ty: value_ty }, [a, rest @ ..]) => {
                let handle = self.value_shapes(value_ty)?;
                let a = self.operand(a, value_ty)?;
                let [a0, a1] = self.pad(a);
                let [b0, b1] = match rest {
                    [b] => {
                        let b = self.operand(b, value_ty)?;
                        self.pad(b)
                    }
                    _ => [a0, a1],
                };
                let eight = self.constant(8);
                let shifted = self.bin(LirBin::Shl, handle, eight);
                let op = self.constant(i64::from(op));
                let packed = self.bin(LirBin::Or, shifted, op);
                Ok(vec![
                    self.runtime(RuntimeFn::ValueOp, vec![packed, a0, a1, b0, b1]),
                ])
            }
            (Intrinsic::ValueShow { ty: value_ty }, [x]) => {
                let handle = self.value_shapes(value_ty)?;
                let x = self.operand(x, value_ty)?;
                let [w0, w1] = self.pad(x);
                Ok(self
                    .runtime2(RuntimeFn::ValueShow, vec![handle, w0, w1])
                    .to_vec())
            }
            (Intrinsic::TestFailure, [message, at]) => {
                let [w0, w1] = self.text_words(message, ty)?;
                let at = word(&self.operand(at, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::TestRecord,
                    args: vec![w0, w1, at],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::Site(expr), []) => {
                let at = self.position(expr).map_or(NO_POSITION as i64, i64::from);
                Ok(vec![self.constant(at)])
            }
            (Intrinsic::BytesRead, [bytes, packed, at]) => {
                let [w0, w1] = self.text_words(bytes, ty)?;
                let packed = word(&self.operand(packed, int)?)?;
                let at = word(&self.operand(at, int)?)?;
                let out = self.runtime2(RuntimeFn::BytesRead, vec![packed, w0, w1, at]);
                // The value waits in the scratch words for `TextParsed`.
                let scratch = self.scratch();
                self.push(Inst::Store {
                    src: out[0],
                    addr: scratch,
                    offset: 0,
                });
                Ok(vec![out[1]])
            }
            (Intrinsic::BytesWrite, [bytes, packed, at, value]) => {
                let [w0, w1] = self.text_words(bytes, ty)?;
                let packed = word(&self.operand(packed, int)?)?;
                let at = word(&self.operand(at, int)?)?;
                let value = word(&self.operand(value, int)?)?;
                let args = vec![packed, w0, w1, at, value];
                Ok(self.runtime2(RuntimeFn::BytesWrite, args).to_vec())
            }
            (Intrinsic::BytesOfList, [list]) => {
                let list_ty = self.operand_ty(list, ty);
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                Ok(self.runtime2(RuntimeFn::BytesOfList, vec![list]).to_vec())
            }
            (Intrinsic::EnvArgs, []) => {
                let list = self.empty(ty, LIST_SIZE)?;
                Ok(vec![self.runtime(RuntimeFn::EnvArgs, vec![list])])
            }
            (Intrinsic::EnvVar, [name]) => {
                let [w0, w1] = self.text_words(name, ty)?;
                // The value waits in the scratch words for `IoReadBytes`.
                let scratch = self.scratch();
                Ok(vec![self.runtime(RuntimeFn::EnvVar, vec![w0, w1, scratch])])
            }
            (Intrinsic::EnvVars, []) => {
                let map = self.empty(ty, MAP_SIZE)?;
                Ok(vec![self.runtime(RuntimeFn::EnvVars, vec![map])])
            }
            (Intrinsic::EnvPlatform, [which]) => {
                let which = word(&self.operand(which, int)?)?;
                Ok(vec![self.runtime(RuntimeFn::EnvPlatform, vec![which])])
            }
            // The tree's hash and bytes lie first in an `Expr`'s
            // environment (`crag_mir::TREE_HASH`), borrowed from it.
            (Intrinsic::ExprTreeHash | Intrinsic::ExprTree, [e]) => {
                let e_ty = self.operand_ty(e, ty);
                let [_, env] = self.operand(e, e_ty)?[..] else {
                    return Err("values of this type");
                };
                let at = match intrinsic {
                    Intrinsic::ExprTreeHash => HEADER_SIZE as i32,
                    _ => HEADER_SIZE as i32 + 16,
                };
                let bytes = vec![self.load(env, at), self.load(env, at + 8)];
                if let Intrinsic::ExprTreeHash = intrinsic {
                    self.count_words(Some(Layout::Pair), ty, &bytes, Self::retain)?;
                    return Ok(bytes);
                }
                self.describe_reachable(ty)?;
                let shapes = self.value_shapes(ty)?;
                let mut args = vec![shapes];
                args.extend(bytes);
                Ok(vec![self.runtime(RuntimeFn::ValueDecode, args)])
            }
            // The policy and the environment wait in the scratch words,
            // where the result or the reason comes back.
            (Intrinsic::TransportRun, [e, input, accept, steps, memory]) => {
                let e_ty = self.operand_ty(e, ty);
                let [_, env] = self.operand(e, e_ty)?[..] else {
                    return Err("values of this type");
                };
                let f = match e_ty.as_builtin(self.db) {
                    Some((Builtin::Expr, &[f])) => f,
                    _ => return Err("values of this type"),
                };
                let expected = crate::tree::type_value(self.db, self.program, f)
                    .and_then(|v| {
                        crate::tree::encode_transport(self.db, self.program, "FnType", &v)
                    })
                    .map_err(|_| "code of this type as received code")?;
                let [x0, x1] = self.text_literal(&expected)?[..] else {
                    return Err("code of this type as received code");
                };
                let input_ty = self.operand_ty(input, ty);
                let words = self.operand(input, input_ty)?;
                if words.len() > 2 {
                    return Err("inputs of this type to received code");
                }
                let [i0, i1] = self.pad(words);
                let scratch = self.scratch();
                for (k, op) in [accept, steps, memory].into_iter().enumerate() {
                    let src = word(&self.operand(op, int)?)?;
                    self.push(Inst::Store {
                        src,
                        addr: scratch,
                        offset: 8 * k as i32,
                    });
                }
                self.push(Inst::Store {
                    src: env,
                    addr: scratch,
                    offset: 24,
                });
                Ok(vec![self.runtime(
                    RuntimeFn::TransportRun,
                    vec![scratch, x0, x1, i0, i1],
                )])
            }
            (Intrinsic::TransportResult, [_]) => {
                let n = self.layout_of(ty)?.words();
                let scratch = self.scratch();
                Ok((0..n).map(|k| self.load(scratch, 8 * k as i32)).collect())
            }
            // The bytes, or why not, wait in the scratch words.
            (Intrinsic::TransportEncode, [e, stamp]) => {
                let e_ty = self.operand_ty(e, ty);
                let [_, env] = self.operand(e, e_ty)?[..] else {
                    return Err("values of this type");
                };
                let stamp = word(&self.operand(stamp, int)?)?;
                let scratch = self.scratch();
                Ok(vec![self.runtime(
                    RuntimeFn::TransportEncode,
                    vec![scratch, env, stamp],
                )])
            }
            // The policy waits in the scratch words, where the `Expr` or
            // the reason comes back.
            (Intrinsic::TransportDecode { value }, [bytes, accept, steps, memory]) => {
                let f = match value.as_builtin(self.db) {
                    Some((Builtin::Expr, &[f])) => f,
                    _ => return Err("decoding values of this type"),
                };
                let expected = crate::tree::type_value(self.db, self.program, f)
                    .and_then(|v| {
                        crate::tree::encode_transport(self.db, self.program, "FnType", &v)
                    })
                    .map_err(|_| "code of this type as received code")?;
                let [x0, x1] = self.text_literal(&expected)?[..] else {
                    return Err("code of this type as received code");
                };
                let [b0, b1] = self.text_words(bytes, ty)?;
                let scratch = self.scratch();
                for (k, op) in [accept, steps, memory].into_iter().enumerate() {
                    let src = word(&self.operand(op, int)?)?;
                    self.push(Inst::Store {
                        src,
                        addr: scratch,
                        offset: 8 * k as i32,
                    });
                }
                Ok(vec![self.runtime(
                    RuntimeFn::TransportDecode,
                    vec![scratch, x0, x1, b0, b1],
                )])
            }
            (Intrinsic::BudgetOp, [op, side, index]) => {
                let op = word(&self.operand(op, int)?)?;
                let side = word(&self.operand(side, int)?)?;
                let index = word(&self.operand(index, int)?)?;
                let scratch = self.scratch();
                Ok(vec![self.runtime(
                    RuntimeFn::BudgetOp,
                    vec![scratch, op, side, index],
                )])
            }
            (Intrinsic::CollCount, [c]) => {
                let c_ty = self.operand_ty(c, ty);
                let ptr = word(&self.operand(c, c_ty)?)?;
                Ok(vec![self.load(ptr, LEN_OFFSET)])
            }
            (Intrinsic::ListSet, [list, at, value]) => {
                let list_ty = self.operand_ty(list, ty);
                let element = element_of(self.db, list_ty)?;
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                let at = word(&self.operand(at, int)?)?;
                let words = self.element_value(value, element)?;
                let [w0, w1] = self.pass_element(words);
                Ok(vec![
                    self.runtime(RuntimeFn::ListSet, vec![list, at, w0, w1]),
                ])
            }
            (Intrinsic::ListConcat, [a, b]) => {
                let list_ty = self.operand_ty(a, ty);
                self.describe(list_ty)?;
                let a = word(&self.operand(a, list_ty)?)?;
                let b = word(&self.operand(b, list_ty)?)?;
                Ok(vec![self.runtime(RuntimeFn::ListConcat, vec![a, b])])
            }
            (Intrinsic::ListSlice, [list, front, back]) => {
                let list_ty = self.operand_ty(list, ty);
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                let front = word(&self.operand(front, int)?)?;
                let back = word(&self.operand(back, int)?)?;
                Ok(vec![
                    self.runtime(RuntimeFn::ListSlice, vec![list, front, back]),
                ])
            }
            (Intrinsic::MapInsert | Intrinsic::SetInsert, [map, key, value @ ..]) => {
                let map_ty = self.operand_ty(map, ty);
                let (k, v) = match map_ty.as_builtin(self.db) {
                    Some((Builtin::Map, &[k, v])) => (k, Some(v)),
                    Some((Builtin::Set, &[k])) => (k, None),
                    _ => return Err("collections of this type"),
                };
                self.describe(map_ty)?;
                let map = word(&self.operand(map, map_ty)?)?;
                let [k0, k1] = self.key(key, k)?;
                let [v0, v1] = match (value, v) {
                    ([value], Some(v)) => {
                        let value = self.element_value(value, v)?;
                        self.pass_element(value)
                    }
                    _ => self.pad(Vec::new()),
                };
                Ok(vec![
                    self.runtime(RuntimeFn::MapInsert, vec![map, k0, k1, v0, v1]),
                ])
            }
            (Intrinsic::MapRemove | Intrinsic::SetContains, [map, key]) => {
                let map_ty = self.operand_ty(map, ty);
                let k = match map_ty.as_builtin(self.db) {
                    Some((Builtin::Map | Builtin::Set, args)) => args[0],
                    _ => return Err("collections of this type"),
                };
                self.describe(map_ty)?;
                let map = word(&self.operand(map, map_ty)?)?;
                let [k0, k1] = self.key(key, k)?;
                if intrinsic == Intrinsic::MapRemove {
                    return Ok(vec![self.runtime(RuntimeFn::MapRemove, vec![map, k0, k1])]);
                }
                let at = self.runtime(RuntimeFn::MapGet, vec![map, k0, k1]);
                let zero = self.constant(0);
                Ok(vec![self.cmp(Cond::Ne, at, zero)])
            }
            (Intrinsic::MapKeys | Intrinsic::MapValues, [map]) => {
                let map_ty = self.operand_ty(map, ty);
                self.describe(map_ty)?;
                let map = word(&self.operand(map, map_ty)?)?;
                let list = self.empty(ty, LIST_SIZE)?;
                let values = self.constant(i64::from(intrinsic == Intrinsic::MapValues));
                Ok(vec![
                    self.runtime(RuntimeFn::MapList, vec![map, list, values]),
                ])
            }
            (Intrinsic::ListAppend, [list, value]) => {
                let list_ty = self.operand_ty(list, ty);
                let element = element_of(self.db, list_ty)?;
                self.describe(list_ty)?;
                let list = word(&self.operand(list, list_ty)?)?;
                let words = self.element_value(value, element)?;
                let [w0, w1] = self.pass_element(words);
                Ok(vec![self.runtime(RuntimeFn::ListPush, vec![list, w0, w1])])
            }
            (Intrinsic::SignalMark, []) => {
                Ok(vec![self.runtime(RuntimeFn::SignalMark, Vec::new())])
            }
            (Intrinsic::SignalReset, [mark, ..]) => {
                let mark = word(&self.operand(mark, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::SignalReset,
                    args: vec![mark],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::SignalOn, [handler, base]) => {
                let handler_ty = self.operand_ty(handler, ty);
                let TyKind::Fn { params, .. } = handler_ty.kind(self.db) else {
                    return Err("signal handlers of this type");
                };
                let signal = params[0];
                let words = layout(self.db, self.program, signal)
                    .ok_or("signal handlers of this type")?
                    .words();
                if words > 1 {
                    return Err("signal handlers of this type");
                }
                let (types, parents) = signal_types(self.db, self.program, signal);
                let bytes: Vec<u8> = types.iter().flat_map(|t| t.to_le_bytes()).collect();
                let table = self.static_data(bytes);
                let [code, env] = self.operand(handler, handler_ty)?[..] else {
                    return Err("signal handlers of this type");
                };
                let packed = (types.len() as i64) << 32 | i64::from(parents) << 8 | words as i64;
                let packed = self.constant(packed);
                let base = word(&self.operand(base, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::SignalOn,
                    args: vec![code, env, table, packed, base],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::SignalEmit { qualifier }, [signal]) => {
                let signal_ty = self.operand_ty(signal, ty);
                let signal_layout = layout(self.db, self.program, signal_ty);
                let boxed = match signal_layout {
                    Some(Layout::Box) => true,
                    Some(Layout::Zero | Layout::Tag) => false,
                    _ => return Err("signals of this type"),
                };
                let words = self.operand(signal, signal_ty)?;
                let info = self.signal_info(signal_ty, boxed);
                let list = self.cell_list(signal_ty)?;
                let [w0, w1] = self.pad(words.clone());
                let qualifier = self.constant(i64::from(qualifier));
                let held = self.runtime(RuntimeFn::SignalEmit, vec![qualifier, list, w0, w1, info]);
                let (deliver, done) = (self.new_block(), self.new_block());
                self.end(
                    Term::Branch {
                        cond: held,
                        then: deliver,
                        otherwise: done,
                    },
                    Some(deliver),
                );
                let trapped = self.deliver(w0, info);
                self.count_words(signal_layout, signal_ty, &words, Self::release)?;
                self.end(Term::Jump(done), Some(trapped));
                self.count_words(signal_layout, signal_ty, &words, Self::release)?;
                self.pass_trap(done);
                Ok(Vec::new())
            }
            (Intrinsic::SignalDrain, []) => {
                let (head, take, done) = (self.new_block(), self.new_block(), self.new_block());
                self.end(Term::Jump(head), Some(head));
                let out = self.scratch();
                let list = self.runtime(RuntimeFn::SignalNext, vec![out]);
                let none = self.constant(SIGNAL_NONE as i64);
                let more = self.cmp(Cond::Ne, list, none);
                self.end(
                    Term::Branch {
                        cond: more,
                        then: take,
                        otherwise: done,
                    },
                    Some(take),
                );
                let w0 = self.load(out, 0);
                let info = self.load(out, 16);
                let trapped = self.deliver(w0, info);
                self.end(Term::Jump(head), Some(trapped));
                self.pass_trap(done);
                Ok(Vec::new())
            }
            (Intrinsic::ScopeNew, [limit]) => {
                let limit = word(&self.operand(limit, int)?)?;
                Ok(vec![self.runtime(RuntimeFn::ScopeNew, vec![limit])])
            }
            (Intrinsic::ScopeStart, [scope, task, exempt]) => {
                let task_ty = self.operand_ty(task, int);
                let TyKind::Fn { result, .. } = task_ty.kind(self.db) else {
                    return Err("this operation of the runtime");
                };
                let results = layout(self.db, self.program, *result)
                    .ok_or("values of this type")?
                    .words();
                let scope = word(&self.operand(scope, int)?)?;
                let [code, env] = self.operand(task, task_ty)?[..] else {
                    return Err("this operation of the runtime");
                };
                let exempt = word(&self.operand(exempt, int)?)?;
                let shift = self.constant(START_EXEMPT.trailing_zeros().into());
                let exempt = self.bin(LirBin::Shl, exempt, shift);
                let results = self.constant(results as i64);
                let flags = self.bin(LirBin::Or, exempt, results);
                self.runtime(RuntimeFn::ScopeStart, vec![scope, code, env, flags]);
                Ok(Vec::new())
            }
            (Intrinsic::ScopeNext, [scope]) => {
                let scope = word(&self.operand(scope, int)?)?;
                let next = self.runtime2(RuntimeFn::ScopeNext, vec![scope]);
                let (index, status) = (next[0], next[1]);
                let done = self.constant(SCOPE_DONE as i64);
                let is_done = self.cmp(Cond::Eq, index, done);
                let two = self.constant(2);
                let shifted = self.bin(LirBin::Shl, index, two);
                let packed = self.bin(LirBin::Or, shifted, status);
                let none = self.constant(-1);
                let out = self.reg();
                self.push(Inst::Select {
                    dst: out,
                    cond: is_done,
                    a: none,
                    b: packed,
                });
                Ok(vec![out])
            }
            (Intrinsic::ScopeResult, [scope, index]) => {
                let scope = word(&self.operand(scope, int)?)?;
                let index = word(&self.operand(index, int)?)?;
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                let out = self.runtime2(RuntimeFn::ScopeResult, vec![scope, index]);
                Ok(out[..words].to_vec())
            }
            (Intrinsic::ScopeCancel | Intrinsic::ScopeEnd, [scope]) => {
                let scope = word(&self.operand(scope, int)?)?;
                let func = match intrinsic {
                    Intrinsic::ScopeCancel => RuntimeFn::ScopeCancel,
                    _ => RuntimeFn::ScopeEnd,
                };
                self.push(Inst::CallRuntime {
                    func,
                    args: vec![scope],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::TxBegin, []) => Ok(vec![self.runtime(RuntimeFn::TxBegin, Vec::new())]),
            (Intrinsic::TxDepth, []) => Ok(vec![self.runtime(RuntimeFn::TxDepth, Vec::new())]),
            (Intrinsic::TxUnwind, [depth]) => {
                let depth = word(&self.operand(depth, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::TxUnwind,
                    args: vec![depth],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::TrapCaught(which), []) => {
                let which = self.constant(i64::from(which));
                Ok(vec![self.runtime(RuntimeFn::TrapCaught, vec![which])])
            }
            (Intrinsic::TrapCaughtText(which), []) => {
                let which = self.constant(i64::from(which));
                Ok(self.runtime2(RuntimeFn::TrapCaughtText, vec![which]))
            }
            (Intrinsic::TxCommit, []) => Ok(vec![self.runtime(RuntimeFn::TxCommit, Vec::new())]),
            (Intrinsic::TxAbort | Intrinsic::TxRetry | Intrinsic::TxThrow, []) => {
                let func = match intrinsic {
                    Intrinsic::TxAbort => RuntimeFn::TxAbort,
                    Intrinsic::TxRetry => RuntimeFn::TxRetry,
                    _ => RuntimeFn::TxThrow,
                };
                self.push(Inst::CallRuntime {
                    func,
                    args: Vec::new(),
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            (Intrinsic::TxConflicted | Intrinsic::SidePtr | Intrinsic::SideEnd, []) => {
                let offset = match intrinsic {
                    Intrinsic::TxConflicted => TX_CONFLICT_OFFSET,
                    Intrinsic::SidePtr => SIDE_PTR_OFFSET,
                    _ => SIDE_END_OFFSET,
                };
                let ctx = self.reg();
                self.push(Inst::Context { dst: ctx });
                Ok(vec![self.load(ctx, offset)])
            }
            (Intrinsic::SideReset, [ptr, end]) => {
                let ptr = word(&self.operand(ptr, int)?)?;
                let end = word(&self.operand(end, int)?)?;
                let ctx = self.reg();
                self.push(Inst::Context { dst: ctx });
                for (src, offset) in [(ptr, SIDE_PTR_OFFSET), (end, SIDE_END_OFFSET)] {
                    self.push(Inst::Store {
                        src,
                        addr: ctx,
                        offset,
                    });
                }
                Ok(Vec::new())
            }
            (Intrinsic::RefApply { op, ty: builtin }, [cell, k]) => {
                let op = match op {
                    BinOp::Add => REF_ADD,
                    BinOp::Sub => REF_SUB,
                    BinOp::Mul => REF_MUL,
                    _ => return Err("this operation of the runtime"),
                };
                let (bits, unsigned) = match builtin {
                    Builtin::Int => (64, false),
                    Builtin::Int8 => (8, false),
                    Builtin::Int16 => (16, false),
                    Builtin::Int32 => (32, false),
                    Builtin::UInt8 => (8, true),
                    Builtin::UInt16 => (16, true),
                    Builtin::UInt32 => (32, true),
                    Builtin::UInt64 => (64, true),
                    _ => return Err("this operation of the runtime"),
                };
                let width = if unsigned { bits | REF_UNSIGNED } else { bits };
                let k_ty = Ty::builtin(self.db, builtin);
                let k = word(&self.operand(k, k_ty)?)?;
                let list = self.cell_list(k_ty)?;
                let cell = self.cell_addr(cell)?;
                let op = self.constant(op as i64);
                let width = self.constant(width as i64);
                Ok(vec![self.runtime(
                    RuntimeFn::RefApply,
                    vec![cell, op, width, k, list],
                )])
            }
            (Intrinsic::RefSwap, [cell, value]) => {
                let list = self.cell_list(ty)?;
                let cell = self.cell_addr(cell)?;
                let words = self.ref_value(value, ty)?;
                let [w0, w1] = self.pad(words);
                let old = self.runtime2(RuntimeFn::RefSwap, vec![cell, list, w0, w1]);
                // The old value stored flat, with references of its own,
                // goes into a box that takes them.
                if let Some((_, slots)) = ref_storage(self.db, self.program, ty) {
                    let f = form(self.db, self.program, ty).ok_or("records of this type")?;
                    let out = self.scratch();
                    for (k, &src) in old.iter().enumerate() {
                        self.push(Inst::Store {
                            src,
                            addr: out,
                            offset: 8 * k as i32,
                        });
                    }
                    let regs = self.load_stored(out, &slots, f.words());
                    return self.boxed(ty, &f, &regs);
                }
                let words = layout(self.db, self.program, ty)
                    .ok_or("values of this type")?
                    .words();
                Ok(old[..words].to_vec())
            }
            (Intrinsic::Sleep, [nanos]) => {
                let nanos = word(&self.operand(nanos, int)?)?;
                self.push(Inst::CallRuntime {
                    func: RuntimeFn::Sleep,
                    args: vec![nanos],
                    dsts: Vec::new(),
                });
                Ok(Vec::new())
            }
            _ => Err("this operation of the runtime"),
        }
    }

    /// 1 when two strings or bytes values hold the same bytes, else 0.
    /// Equal words are equal values, and a value of at most 15 bytes is
    /// always inline, so only two buffers of the same length need the
    /// runtime to compare.
    pub(super) fn text_equals(&mut self, a: &[VReg], b: &[VReg]) -> Result<VReg, Unsupported> {
        let ([a0, a1], [b0, b1]) = (a, b) else {
            return Err("this conversion");
        };
        let (a0, a1, b0, b1) = (*a0, *a1, *b0, *b1);
        let out = self.reg();
        let same0 = self.cmp(Cond::Eq, a0, b0);
        let same1 = self.cmp(Cond::Eq, a1, b1);
        let same = self.bin(LirBin::And, same0, same1);
        let one = self.constant(1);
        let either = self.bin(LirBin::Or, a0, b0);
        let inline = self.bin(LirBin::And, either, one);
        let mask = self.constant(0xffff_ffff);
        let a_len = self.bin(LirBin::And, a1, mask);
        let b_len = self.bin(LirBin::And, b1, mask);
        let unequal = self.cmp(Cond::Ne, a_len, b_len);
        let known = self.bin(LirBin::Or, same, inline);
        let known = self.bin(LirBin::Or, known, unequal);
        let (fast, slow, done) = (self.new_block(), self.new_block(), self.new_block());
        self.end(
            Term::Branch {
                cond: known,
                then: fast,
                otherwise: slow,
            },
            Some(fast),
        );
        self.push(Inst::Move {
            dst: out,
            src: same,
        });
        self.end(Term::Jump(done), Some(slow));
        let equal = self.runtime(RuntimeFn::TextEquals, vec![a0, a1, b0, b1]);
        self.push(Inst::Move {
            dst: out,
            src: equal,
        });
        self.end(Term::Jump(done), Some(done));
        Ok(out)
    }

    /// Strings joined, each part borrowed: a string, bytes joined into
    /// bytes, a number written as text, or any other value as `show`
    /// writes it by its structure. The result has a reference of its own.
    pub(super) fn concat(
        &mut self,
        parts: &[Operand<'db>],
        result: Ty<'db>,
    ) -> Result<Vec<VReg>, Unsupported> {
        // Bytes join as they are into bytes, but are shown in a string.
        let raw_bytes = matches!(result.as_builtin(self.db), Some((Builtin::Bytes, _)));
        let db = self.db;
        let str_ty = Ty::builtin(db, Builtin::Str);
        // The text so far, and whether this code owns a reference to it.
        let mut text: Option<(Vec<VReg>, bool)> = None;
        for part in parts {
            let ty = self.operand_ty(part, str_ty);
            let words = self.operand(part, ty)?;
            let number = ty.as_builtin(db).and_then(|(b, _)| crate::shape::number(b));
            let (words, owned) = match (ty.as_builtin(db), number) {
                (Some((Builtin::Str, _)), _) => (words, false),
                (Some((Builtin::Bytes, _)), _) if raw_bytes => (words, false),
                (_, Some(number)) => {
                    let code = self.constant(number.code() as i64);
                    (
                        self.runtime2(RuntimeFn::TextShow, vec![word(&words)?, code]),
                        true,
                    )
                }
                // Any other value as `show` writes it by its structure.
                _ => {
                    let handle = self.value_shapes(ty)?;
                    let [w0, w1] = self.pad(words);
                    (
                        self.runtime2(RuntimeFn::ValueShow, vec![handle, w0, w1])
                            .to_vec(),
                        true,
                    )
                }
            };
            text = Some(match text {
                None => (words, owned),
                Some((so_far, owned_so_far)) => {
                    let mut args = so_far.clone();
                    args.extend(&words);
                    let joined = self.runtime2(RuntimeFn::TextConcat, args);
                    if owned_so_far {
                        self.count_text(&so_far, Self::release);
                    }
                    if owned {
                        self.count_text(&words, Self::release);
                    }
                    (joined, true)
                }
            });
        }
        let Some((words, owned)) = text else {
            return self.text_literal(b"");
        };
        if !owned {
            self.count_text(&words, Self::retain);
        }
        Ok(words)
    }

    /// Retains or releases the buffer of a string's words, if it has one.
    fn count_text(&mut self, words: &[VReg], op: fn(&mut Self, VReg)) {
        let str_ty = Ty::builtin(self.db, Builtin::Str);
        self.count_words(Some(Layout::Pair), str_ty, words, op)
            .expect("a string is counted");
    }

    /// Calls a runtime function with two results.
    pub(super) fn runtime2(&mut self, func: RuntimeFn, args: Vec<VReg>) -> Vec<VReg> {
        let dsts = vec![self.reg(), self.reg()];
        self.push(Inst::CallRuntime {
            func,
            args,
            dsts: dsts.clone(),
        });
        dsts
    }
}
