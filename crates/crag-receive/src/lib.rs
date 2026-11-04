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

//! Receiving code (Implementation Plan §11.10.8 and §11.10.9,
//! Specification §18.7): the receiver of a program checks the tree of an
//! `Expr` again with the compiler's own front end, compiles what it
//! accepts in the metered tier, against the program's own type indices
//! and module-level values, and hands it to the runtime to run under the
//! policy's limits next to the program's data.
//!
//! The receiver rebuilds the program from its [`Bundle`], in a database of
//! its own, once per process. Its metered code is one store for the whole
//! process: a function of the program is compiled once, whichever trees
//! reach it, and stays loaded, so callers share it without knowing. The
//! store's functions are compiled against the program, the received
//! module's against the program with that module; both number types and
//! instances alike, so their code calls each other. Each value the
//! program's code computes keeps its one cell: received code reads and
//! fills the program's.
//!
//! Receiving counts against the policy's limits before anything runs
//! (§18.7): each node of the tree and each MIR statement of the code it
//! reaches costs a step, the program's functions included, and that code's
//! bytes cost memory, whether or not the store holds it already, so whether
//! code is accepted depends on the tree, the policy and the program alone.
//! The count stops as soon as the steps are used up, before the code is
//! compiled. What is left of the limits is the run's.
//!
//! The front end recurses deeply, so the receiver works on a thread of its
//! own with a large stack; `run` waits for it.
//!
//! A callee accepted although its body hash differs from the sender's is
//! listed with the code, as `Checked::mismatched` lists it, also when the
//! limits then refuse the code, so that `run` signals it (§18.7).
//!
//! Every tree is checked in one received module, whose source the next
//! tree replaces (`Slot`), so the database holds what one tree needs and
//! not what every tree did. Code the store loaded stays, by instance,
//! until the store holds more than its bound.
//!
//! The bound is on the bytes of code the store holds, [`BOUND`] or
//! `CRAG_RECEIVED_CODE`. Once they exceed it, the next tree first unloads
//! all code the store may unload, which it compiles again when a tree
//! reaches it. It keeps code a run holds (`Received::hold`), until the run
//! stopped, and code a value may reach after its run: the code of the
//! program's module-level values, which their cells may keep functions
//! of, and all code of a tree whose result may hold a function. With it
//! stays all code that code reaches through its relocations, so nothing
//! loaded calls code unloaded. The bound is soft: the store unloads only
//! before a tree, and keeps what it must.

extern crate crag_db as salsa;

mod bundle;
mod check;

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io;
use std::sync::{Arc, Mutex, OnceLock, PoisonError, mpsc};

use crag_abi::{CodeObject, FuncId, RelocTarget, RuntimeFn, Shapes, TypeDescriptor};
use crag_backend::tree::decode_transport;
use crag_backend::{code, func_id, shapes};
use crag_codegen::{CodegenSettings, OptLevel, Target, compile_entry_stub, target_for};
use crag_db::RootDatabase;
use crag_hir::{ItemKind, Owner, Program, item_tree};
use crag_loader::{CodeArena, LoadError, SymbolTable, load, load_group, unload};
use crag_mir::{Entry, InstanceKey, MirBody, Tier, mir};
use crag_runtime::transport::{self, Received, Refused, Request};
use crag_runtime::{CodeMap, Scheduler, Types};

pub use bundle::Bundle;
pub use check::{Accept, Checked, RECEIVED, ROOT, Rejection, Slot, check_received};

/// The bytes of address space the store reserves for code.
const ARENA: usize = 1 << 30;

/// The bytes of code past which the store unloads what it may, unless
/// `CRAG_RECEIVED_CODE` gives another bound.
pub const BOUND: u64 = 32 << 20;

/// The bound on the store's code, from `CRAG_RECEIVED_CODE` or [`BOUND`].
fn bound() -> u64 {
    std::env::var("CRAG_RECEIVED_CODE")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(BOUND)
}

/// The stack of the receiver's thread.
const STACK: usize = 256 << 20;

/// The receiver of a program, which the runtime asks to receive code.
pub struct Receiver {
    jobs: Mutex<mpsc::Sender<Job>>,
}

/// A request the receiver's thread works on, with where its answer goes.
struct Job {
    tree: Vec<u8>,
    expected: Vec<u8>,
    accept: Accept,
    steps: u64,
    memory: u64,
    types: TypesRef,
    answer: mpsc::Sender<Result<Received, Refused>>,
}

/// The program's descriptors, which the caller holds while it waits.
struct TypesRef(*const Types);

// SAFETY: the caller of `receive` waits for the answer, and keeps the
// descriptors alive until then; they are only read.
unsafe impl Send for TypesRef {}

impl Receiver {
    /// The receiver of the program the bundle holds, whose module-level
    /// values the program keeps in the cells at these addresses, by
    /// `module.name`.
    pub fn new(mut bundle: Bundle, cells: HashMap<String, usize>) -> io::Result<Receiver> {
        // The types the program lacks are numbered in a range of this
        // receiver's own, past the program's.
        if bundle.indices.base > transport::FRESH_SPAN {
            return Err(io::Error::other(
                "a program of too many types to receive code",
            ));
        }
        bundle.indices.base = transport::fresh_types();
        let (jobs, queue) = mpsc::channel::<Job>();
        std::thread::Builder::new()
            .name("crag-receiver".into())
            .stack_size(STACK)
            .spawn(move || {
                let mut store = match Store::new(&bundle, cells) {
                    Ok(store) => store,
                    Err(e) => {
                        for job in queue {
                            let why = format!("no memory for received code: {e}");
                            let _ = job.answer.send(Err(Refused::IllTyped(why)));
                        }
                        return;
                    }
                };
                for job in queue {
                    // SAFETY: as `TypesRef` says.
                    let types = unsafe { &*job.types.0 };
                    let answer = store.receive(&job, types);
                    let _ = job.answer.send(answer);
                }
            })?;
        Ok(Receiver {
            jobs: Mutex::new(jobs),
        })
    }

    /// Makes this the receiver of the program the scheduler runs, which
    /// `std.transport.run` asks.
    pub fn install(self, scheduler: &Scheduler) {
        scheduler.set_receiver(Arc::new(self));
    }
}

impl transport::Receive for Receiver {
    fn receive(&self, request: &Request<'_>) -> Result<Received, Refused> {
        let (answer, answered) = mpsc::channel();
        let job = Job {
            tree: request.tree.to_vec(),
            expected: request.expected.to_vec(),
            accept: match request.accept {
                transport::Accept::Exact => Accept::Exact,
                transport::Accept::SameMajor => Accept::SameMajor,
                transport::Accept::Signature => Accept::Signature,
            },
            steps: request.steps,
            memory: request.memory,
            types: TypesRef(request.types),
            answer,
        };
        let failed = || Refused::IllTyped("the receiver of code failed".into());
        if self.jobs.lock().unwrap().send(job).is_err() {
            return Err(failed());
        }
        answered.recv().unwrap_or_else(|_| Err(failed()))
    }
}

/// Code the receiver accepted, and what receiving it cost.
struct Accepted {
    stub: usize,
    entry: usize,
    input: (Shapes, u32),
    input_words: u32,
    result_words: u32,
    steps: u64,
    memory: u64,
    mismatched: Vec<transport::Mismatch>,
    /// The functions the code reaches, which a run holds.
    reached: Arc<[FuncId]>,
}

/// The runs that hold each function of the store.
type Held = Arc<Mutex<HashMap<FuncId, usize>>>;

/// A run's hold on the functions its code reaches, until it is dropped.
struct Hold {
    held: Held,
    reached: Arc<[FuncId]>,
}

impl Hold {
    fn new(held: &Held, reached: &Arc<[FuncId]>) -> Hold {
        let mut counts = held.lock().unwrap_or_else(PoisonError::into_inner);
        for func in reached.iter() {
            *counts.entry(*func).or_default() += 1;
        }
        Hold {
            held: held.clone(),
            reached: reached.clone(),
        }
    }
}

impl Drop for Hold {
    fn drop(&mut self) {
        let mut counts = self.held.lock().unwrap_or_else(PoisonError::into_inner);
        for func in self.reached.iter() {
            if let Some(n) = counts.get_mut(func) {
                *n -= 1;
                if *n == 0 {
                    counts.remove(func);
                }
            }
        }
    }
}

/// The receiver's program and its store of metered code.
struct Store {
    db: RootDatabase,
    program: Program,
    /// The received module every tree is checked in.
    slot: Slot,
    arena: CodeArena,
    symbols: SymbolTable,
    /// The bytes of each function's code in the store, and of all.
    sizes: HashMap<FuncId, u64>,
    loaded: u64,
    /// The bytes past which the store unloads what it may.
    bound: u64,
    /// The functions each function's code refers to.
    refers: HashMap<FuncId, Vec<FuncId>>,
    /// The functions a value may reach after their run, which stay.
    pinned: HashSet<FuncId>,
    /// The functions runs hold.
    held: Held,
    /// What the overlay describes: each function's entry and object, and
    /// the descriptors the program has none for.
    objects: Vec<(FuncId, usize, CodeObject)>,
    types: BTreeMap<u32, TypeDescriptor>,
    stubs: HashMap<(u32, u32), usize>,
    /// The code accepted so far, by the hash of its tree, the expected
    /// type and the policy's `Accept`.
    accepted: HashMap<([u8; 32], Vec<u8>, u8), Accepted>,
    /// The program's cells, by `module.name`.
    cells: HashMap<String, usize>,
}

/// The host's target, for the stubs.
fn host() -> &'static Target {
    static HOST: OnceLock<Target> = OnceLock::new();
    HOST.get_or_init(|| target_for("x86_64-unknown-linux-gnu").expect("the host is supported"))
}

impl Store {
    fn new(bundle: &Bundle, cells: HashMap<String, usize>) -> io::Result<Store> {
        let (mut db, program) = bundle.open();
        let slot = Slot::new(&mut db, program);
        let arena = CodeArena::new(ARENA)?;
        let mut symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            symbols.define_runtime(func, crag_runtime::runtime_fn_addr(func));
        }
        Ok(Store {
            db,
            program,
            slot,
            arena,
            symbols,
            sizes: HashMap::new(),
            loaded: 0,
            bound: bound(),
            refers: HashMap::new(),
            pinned: HashSet::new(),
            held: Held::default(),
            objects: Vec::new(),
            types: BTreeMap::new(),
            stubs: HashMap::new(),
            accepted: HashMap::new(),
            cells,
        })
    }

    /// Receives the code of a job: what it accepted before, or the tree
    /// checked, counted, compiled and published.
    fn receive(&mut self, job: &Job, types: &Types) -> Result<Received, Refused> {
        let key = (
            *blake3::hash(&job.tree).as_bytes(),
            job.expected.clone(),
            job.accept as u8,
        );
        if !self.accepted.contains_key(&key) {
            let accepted = self.accept(job, types)?;
            self.accepted.insert(key.clone(), accepted);
        }
        let accepted = &self.accepted[&key];
        let mismatched = accepted.mismatched.clone();
        if accepted.steps > job.steps {
            return Err(Refused::StepLimit(mismatched));
        }
        if accepted.memory > job.memory {
            return Err(Refused::MemoryLimit(mismatched));
        }
        Ok(Received {
            stub: accepted.stub,
            entry: accepted.entry,
            input: accepted.input.clone(),
            input_words: accepted.input_words,
            result_words: accepted.result_words,
            steps: job.steps - accepted.steps,
            memory: job.memory - accepted.memory,
            mismatched,
            hold: Box::new(Hold::new(&self.held, &accepted.reached)),
        })
    }

    /// Unloads the functions no run holds and no value may reach, with
    /// the code accepted that reaches them.
    fn evict(&mut self) {
        let mut keep: HashSet<FuncId> = self.pinned.clone();
        keep.extend(
            self.held
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .keys()
                .copied(),
        );
        let mut pending: Vec<FuncId> = keep.iter().copied().collect();
        while let Some(func) = pending.pop() {
            for callee in self.refers.get(&func).into_iter().flatten() {
                if keep.insert(*callee) {
                    pending.push(*callee);
                }
            }
        }
        let gone: HashSet<FuncId> = self
            .sizes
            .keys()
            .filter(|f| !keep.contains(f))
            .copied()
            .collect();
        if gone.is_empty() {
            return;
        }
        for func in &gone {
            if let Some(entry) = self.symbols.function(*func) {
                // SAFETY: no run holds the code, so no frame of it is on a
                // stack, and no value reaches it. All code that refers to
                // it goes with it: what stays is closed under `refers`.
                let _ = unsafe { unload(&mut self.arena, &mut self.symbols, entry) };
            }
            self.loaded -= self.sizes.remove(func).unwrap_or(0);
            self.refers.remove(func);
        }
        self.objects.retain(|(func, ..)| !gone.contains(func));
        self.accepted
            .retain(|_, a| !a.reached.iter().any(|f| gone.contains(f)));
    }

    fn accept(&mut self, job: &Job, types: &Types) -> Result<Accepted, Refused> {
        let ill = |why: String| Refused::IllTyped(why);
        let base = self.program;
        let expected = decode_transport(&self.db, base, "FnType", &job.expected)
            .map_err(|e| ill(format!("a malformed expected type: {e}")))?;
        // Each node of the tree costs a step, before the front end sees it.
        let tree = crag_backend::tree::decode_tree(&self.db, base, &job.tree)
            .map_err(|e| ill(format!("a malformed tree: {e}")))?;
        let mut steps = nodes(&tree);
        if steps > job.steps {
            return Err(Refused::StepLimit(Vec::new()));
        }
        if self.loaded > self.bound {
            self.evict();
        }
        let checked = check_received(
            &mut self.db,
            &mut self.slot,
            &job.tree,
            &expected,
            job.accept,
        )
        .map_err(|r| match r {
            Rejection::Unresolved(m) => Refused::Unresolved(m),
            Rejection::IllTyped(m) => Refused::IllTyped(m),
            Rejection::Impure(m) => Refused::Impure(m),
        })?;
        let mismatched = checked.mismatched.clone();
        let db: &RootDatabase = &self.db;
        let received = checked.program;
        let item = item_tree(db, checked.module)
            .items
            .iter()
            .find(|i| {
                *i.id.kind(db) == ItemKind::Function && *i.id.name(db).text(db) == checked.root
            })
            .map(|i| i.id)
            .ok_or_else(|| ill("no root".into()))?;
        let root = InstanceKey::body(db, Owner::Item(item))
            .with_entry(db, Entry::Closure(checked.closure));
        // The program its code is compiled against: the received module's
        // own with that module, the store's without.
        let program_of = |instance: InstanceKey<'_>| match instance.owner(db).module(db) {
            m if m == checked.module => received,
            _ => base,
        };

        // Each statement of what the code reaches costs a step, until the
        // steps are used up.
        let mut reached = Vec::new();
        let mut seen = HashSet::new();
        let mut pending = vec![root];
        while let Some(instance) = pending.pop() {
            if !seen.insert(instance) {
                continue;
            }
            let program = program_of(instance);
            let Some(body) = mir(db, program, instance, Tier::Metered) else {
                continue;
            };
            steps += statements(body);
            if steps > job.steps {
                return Err(Refused::StepLimit(mismatched.clone()));
            }
            reached.push((instance, program));
            pending.extend(body.callees().into_iter().rev());
            pending.extend(body.inlined.iter().rev().map(|call| call.func));
        }

        // Compile what the store lacks; all of it costs memory.
        let mut fresh = Vec::new();
        let mut memory = 0u64;
        for &(instance, program) in &reached {
            let func = func_id(instance);
            if let Some(&size) = self.sizes.get(&func) {
                memory += size;
                continue;
            }
            let compiled = match code(db, program, instance, Tier::Metered) {
                Some(Ok(compiled)) => compiled,
                Some(Err(e)) => return Err(ill(format!("its code does not compile: {e}"))),
                None => return Err(ill("it reaches what has no body".into())),
            };
            memory += compiled.object.code.len() as u64;
            fresh.push((instance, compiled));
        }
        if memory > job.memory {
            return Err(Refused::MemoryLimit(mismatched.clone()));
        }

        // The descriptors must agree with the program's; those it lacks
        // join the overlay.
        let mut added = BTreeMap::new();
        for (_, compiled) in &fresh {
            for (index, descriptor) in &compiled.types {
                let known = types
                    .get_own(*index)
                    .or_else(|| transport::received_type(*index))
                    .or_else(|| added.get(index));
                match known {
                    Some(d) if d != descriptor => {
                        return Err(ill(format!(
                            "its code describes type {index} unlike the program's"
                        )));
                    }
                    Some(_) => {}
                    None => {
                        added.insert(*index, descriptor.clone());
                    }
                }
            }
        }

        // A value the program computes keeps the program's cell, and the
        // functions its value may hold stay.
        for (instance, compiled) in &fresh {
            if let (Owner::Item(item), Entry::Body) = (*instance.owner(db), instance.entry(db))
                && item.kind(db).is_value()
            {
                let name = format!("{}.{}", item.module(db).path(db), item.name(db).text(db));
                if let Some(&addr) = self.cells.get(&name) {
                    self.symbols.cells_mut().share(compiled.slot, addr);
                }
                self.pinned.insert(compiled.func);
            }
        }

        let group: Vec<_> = fresh.iter().map(|(_, c)| (c.slot, &c.object)).collect();
        let entries =
            load_group(&mut self.arena, &mut self.symbols, &group).map_err(|e| match e {
                LoadError::ArenaFull => Refused::MemoryLimit(mismatched.clone()),
                e => ill(format!("its code does not load: {e:?}")),
            })?;
        for ((_, compiled), entry) in fresh.iter().zip(&entries) {
            let size = compiled.object.code.len() as u64;
            self.sizes.insert(compiled.func, size);
            self.loaded += size;
            self.refers.insert(compiled.func, refers(&compiled.object));
            self.objects
                .push((compiled.func, entry.addr(), compiled.object.clone()));
        }
        self.types.extend(added);

        // The root closure takes its environment and the input.
        let Some(Ok(compiled)) = code(db, received, root, Tier::Metered) else {
            return Err(ill("the root closure does not compile".into()));
        };
        let body = mir(db, received, root, Tier::Metered)
            .as_ref()
            .ok_or_else(|| ill("the root closure has no body".into()))?;
        let input_ty = body
            .locals
            .get(1)
            .filter(|_| body.params == 2)
            .ok_or_else(|| ill("the root closure takes other than one input".into()))?
            .ty;
        let reached: Arc<[FuncId]> = reached.iter().map(|&(i, _)| func_id(i)).collect();
        // A result that may hold a function may keep any of the code.
        if crag_types::holds_function(db, received, body.result) {
            self.pinned.extend(reached.iter().copied());
        }
        let (input_shapes, input_root) = shapes(db, received, input_ty);
        let input_words = input_shapes.shapes[input_root as usize].words();
        if compiled.params != input_words + 1 || compiled.returns > 2 || input_words > 2 {
            return Err(ill("received code of this form cannot run yet".into()));
        }
        let entry = self
            .symbols
            .function(compiled.func)
            .ok_or_else(|| ill("the root closure is not loaded".into()))?
            .addr();
        let stub = stub(
            &mut self.arena,
            &self.symbols,
            &mut self.stubs,
            (compiled.params, compiled.returns),
        )?;
        self.publish();
        Ok(Accepted {
            stub,
            entry,
            input: (input_shapes, input_root),
            input_words,
            result_words: compiled.returns,
            steps,
            memory,
            mismatched,
            reached,
        })
    }

    /// Publishes the store's code and descriptors, before anything runs
    /// what was just loaded.
    fn publish(&self) {
        let mut code = CodeMap::new();
        for (func, entry, object) in &self.objects {
            code.add(*func, *entry, object);
        }
        let (start, end) = self.arena.range();
        transport::publish(start, end, code, self.types.clone());
    }
}

/// The entry stub for code of these parameter and result words, loaded
/// once.
fn stub(
    arena: &mut CodeArena,
    symbols: &SymbolTable,
    stubs: &mut HashMap<(u32, u32), usize>,
    words: (u32, u32),
) -> Result<usize, Refused> {
    if let Some(&stub) = stubs.get(&words) {
        return Ok(stub);
    }
    let settings = CodegenSettings {
        target: host().clone(),
        opt: OptLevel::None,
        metered: false,
        profile: None,
    };
    let failed = |why: String| Refused::IllTyped(format!("no entry for received code: {why}"));
    let object =
        compile_entry_stub(words.0, words.1, &settings).map_err(|e| failed(format!("{e:?}")))?;
    let stub = load(arena, symbols, &object)
        .map_err(|e| failed(format!("{e:?}")))?
        .addr();
    stubs.insert(words, stub);
    Ok(stub)
}

/// The functions a code object refers to: those it calls or takes the
/// address of, directly or through their slots, and those that compute
/// the cells it reads.
fn refers(object: &CodeObject) -> Vec<FuncId> {
    let mut seen = HashSet::new();
    object
        .relocs
        .iter()
        .filter_map(|r| match r.target {
            RelocTarget::Function(f) => Some(f),
            RelocTarget::Slot(k) | RelocTarget::Cell(k) => Some(k.func),
            _ => None,
        })
        .filter(|f| seen.insert(*f))
        .collect()
}

/// The nodes of a tree: its records and lists.
fn nodes(v: &crag_backend::tree::Value) -> u64 {
    use crag_backend::tree::Value;
    match v {
        Value::Record(_, fields) => 1 + fields.iter().map(|(_, v)| nodes(v)).sum::<u64>(),
        Value::List(items) => 1 + items.iter().map(nodes).sum::<u64>(),
        _ => 0,
    }
}

/// The statements of a body, each terminator one.
fn statements(body: &MirBody<'_>) -> u64 {
    body.blocks
        .iter()
        .map(|b| b.statements.len() as u64 + 1)
        .sum()
}
