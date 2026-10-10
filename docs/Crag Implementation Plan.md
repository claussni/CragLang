# Crag Implementation Plan

Oct 3, 2026 · @Ralf Claußnitzer

## Contents

- [1 Principles](#1-principles)
- [2 M0 — Spikes](#2-m0--spikes)
- [3 M1 — Thin vertical slice](#3-m1--thin-vertical-slice)
- [4 M2 — The type system](#4-m2--the-type-system)
- [5 M3 — REPL and compile-time evaluation](#5-m3--repl-and-compile-time-evaluation)
- [6 M4 — Concurrency](#6-m4--concurrency)
- [7 M5 — The IDE](#7-m5--the-ide)
- [8 M6 — Packages](#8-m6--packages)
- [9 M7 — Release and transport](#9-m7--release-and-transport)
- [10 Order considered](#10-order-considered)
- [11 Component guide for implementers](#11-component-guide-for-implementers)
  - [11.1 Terms used throughout](#111-terms-used-throughout)
  - [11.2 Reading the signatures](#112-reading-the-signatures)
  - [11.3 M0 components](#113-m0-components)
    - [11.3.1 Fiber runtime](#1131-fiber-runtime) · [11.3.2 Stack check and morestack](#1132-stack-check-and-morestack) · [11.3.3 Side stack](#1133-side-stack) · [11.3.4 Sentinel](#1134-sentinel) · [11.3.5 Cranelift facade](#1135-cranelift-facade) · [11.3.6 Code loader](#1136-code-loader) · [11.3.7 Salsa facade](#1137-salsa-facade) · [11.3.8 Artifact store](#1138-artifact-store) · [11.3.9 Stress harness](#1139-stress-harness)
  - [11.4 M1 components](#114-m1-components)
    - [11.4.1 Lexer](#1141-lexer) · [11.4.2 Parser and CST](#1142-parser-and-cst) · [11.4.3 Incremental reparse](#1143-incremental-reparse) · [11.4.4 Item tree](#1144-item-tree) · [11.4.5 Names and imports](#1145-names-and-imports) · [11.4.6 HIR lowering](#1146-hir-lowering) · [11.4.7 Core inference](#1147-core-inference) · [11.4.8 case checking](#1148-case-checking) · [11.4.9 MIR builder](#1149-mir-builder) · [11.4.10 Code generation](#11410-code-generation) · [11.4.11 Allocator](#11411-allocator) · [11.4.12 Reference counting](#11412-reference-counting) · [11.4.13 Collection primitives](#11413-collection-primitives) · [11.4.14 Traps and unwinder](#11414-traps-and-unwinder) · [11.4.15 Driver and diagnostics](#11415-driver-and-diagnostics)
  - [11.5 M2 components](#115-m2-components)
    - [11.5.1 Unions and narrowing](#1151-unions-and-narrowing) · [11.5.2 Error inference over recursive groups](#1152-error-inference-over-recursive-groups) · [11.5.3 Generics and forms](#1153-generics-and-forms) · [11.5.4 Overload resolution and UFCS](#1154-overload-resolution-and-ufcs) · [11.5.5 Union lifting](#1155-union-lifting) · [11.5.6 Recursive-group diagnostic](#1156-recursive-group-diagnostic) · [11.5.7 Effects](#1157-effects) · [11.5.8 Escape and bindings-only analysis](#1158-escape-and-bindings-only-analysis) · [11.5.9 Closure conversion](#1159-closure-conversion) · [11.5.10 Monomorphization](#11510-monomorphization) · [11.5.11 Tail calls](#11511-tail-calls)
  - [11.6 M3 components](#116-m3-components)
    - [11.6.1 Session manager](#1161-session-manager) · [11.6.2 REPL](#1162-repl) · [11.6.3 Code shipping](#1163-code-shipping) · [11.6.4 Slot tables](#1164-slot-tables) · [11.6.5 Value printing](#1165-value-printing) · [11.6.6 Metered tier](#1166-metered-tier) · [11.6.7 Compile-time evaluation](#1167-compile-time-evaluation) · [11.6.8 Solid value codec](#1168-solid-value-codec) · [11.6.9 embed handlers](#1169-embed-handlers)
  - [11.7 M4 components](#117-m4-components)
    - [11.7.1 Scheduler](#1171-scheduler) · [11.7.2 I/O poller and timers](#1172-io-poller-and-timers) · [11.7.3 Combinators and groups](#1173-combinators-and-groups) · [11.7.4 Cancellation checks](#1174-cancellation-checks) · [11.7.5 Streams and hubs](#1175-streams-and-hubs) · [11.7.6 Refs](#1176-refs) · [11.7.7 STM](#1177-stm) · [11.7.8 Commutative updates](#1178-commutative-updates) · [11.7.9 ext](#1179-ext) · [11.7.10 Signals](#11710-signals) · [11.7.11 Lazy cells](#11711-lazy-cells) · [11.7.12 Deferred teardown](#11712-deferred-teardown) · [11.7.13 Verification](#11713-verification)
  - [11.8 M5 components](#118-m5-components)
    - [11.8.1 Language server](#1181-language-server) · [11.8.2 Built-in editor](#1182-built-in-editor) · [11.8.3 Formatter](#1183-formatter) · [11.8.4 App image](#1184-app-image) · [11.8.5 Reload planner](#1185-reload-planner) · [11.8.6 Debugger](#1186-debugger)
  - [11.9 M6 components](#119-m6-components)
    - [11.9.1 Package manifest and resolver](#1191-package-manifest-and-resolver) · [11.9.2 api.crag generation](#1192-apicrag-generation) · [11.9.3 api.crag checker](#1193-apicrag-checker) · [11.9.4 Publishing checks](#1194-publishing-checks) · [11.9.5 Persisted store](#1195-persisted-store) · [11.9.6 File lock](#1196-file-lock)
  - [11.10 M7 components](#1110-m7-components)
    - [11.10.1 MIR optimizer](#11101-mir-optimizer) · [11.10.2 Optimizing tier](#11102-optimizing-tier) · [11.10.3 AOT object writer](#11103-aot-object-writer) · [11.10.4 Runtime archives](#11104-runtime-archives) · [11.10.5 Linking](#11105-linking) · [11.10.6 Reproducibility check](#11106-reproducibility-check) · [11.10.7 Transport codec](#11107-transport-codec) · [11.10.8 Runtime type check](#11108-runtime-type-check) · [11.10.9 Metered evaluation in release builds](#11109-metered-evaluation-in-release-builds)

This plan orders the work of building the Crag toolchain. The language is defined by The Crag Language Specification (Working Draft), and how the toolchain is built is recorded in its Compiler architecture tab. This document says only in what order the pieces get built and when each milestone counts as done.

&#91;embedded content: Toolchain layers · tools, host, compiler, images, runtime, platform\]

Every tool reaches the compiler through the one query engine in the host, and every image runs on the same runtime. The milestones below build these layers bottom-up along a thin vertical slice; each milestone's diagram shows the components at work, with the new ones highlighted.

## 1 Principles

- **Riskiest runtime parts first.** Stack copying, the side stack and guaranteed tail calls are proven before anything depends on them.
- **Incremental from day one.** Every compiler stage is a query in the incremental system from the start, because adding incrementality later is far harder than starting with it.
- **Thin vertical slices.** Each milestone ends with something that runs end to end, never with a finished stage that nothing uses yet.
- **Dogfooding from M3.** Once the REPL works, development of Crag code happens in it.
- **The standard library grows alongside**, written in Crag from M1 onward.

## 2 M0 — Spikes

&#91;embedded content: M0 components · two facades, a store skeleton, the fiber runtime\]

The runtime pieces carry every later milestone, so they are built and stress-tested first, in parallel with the two facades.

**Components and algorithms**

- **Fiber runtime.** Fiber records, a context switch in inline assembly (save the callee-saved registers, swap the stack pointer), stacks mapped with a guard page, and a minimal run loop on one worker.
- **Stack check and `morestack`.** Each function's entry block compares the stack pointer with the limit in the task context, after the prologue has allocated the frame; a margin below the limit makes that safe, and a function with a frame over the budget gets a wrapper that checks its size first. On failure, `morestack` runs on the system stack: it allocates a stack twice the size, copies the used part, rewrites the frame-pointer chain and frees the old stack.
- **Side stack.** A per-fiber bump region that never moves, pushed on entry and popped on return. It holds every address-taken value, so the machine stack holds no pointers into itself.
- **Sentinel.** Setting the limit to a sentinel forces the next check into the runtime; the spike uses it to pause and resume a fiber.
- **Cranelift facade.** A builder over a small subset of our lowered IR, Cranelift's tail calling convention with `return_call`, frame pointers kept, and stack maps at call sites.
- **Code loader.** Maps code objects into executable memory, applies relocations and keeps pages write-xor-execute.
- **Salsa facade.** Our own traits over inputs, tracked and interned queries, durability levels and the cancellation flag, so no Salsa type leaks into the compiler.
- **Artifact store skeleton.** Content-hash keys (BLAKE3), hash-named blobs on disk, and writes made atomic by rename.
- **Stress harness.** CI runs every fiber test with the smallest initial stack, so every call forces growth.

**Exit:** a hand-written MIR function runs on a fiber, grows its stack a thousand times, and tail-calls without stack growth.

## 3 M1 — Thin vertical slice

&#91;embedded content: M1 components · source to a running fiber\]

A small language subset runs through every layer, so each later milestone widens a working path instead of connecting stages for the first time.

**Components and algorithms**

- **Lexer.** Hand-written, keeping trivia and significant newlines in every token.
- **Parser and CST.** Recursive descent with Pratt parsing for operators, into a lossless green/red tree in the style of rowan. Error recovery is anchored at braces and statement newlines (§2.3).
- **Incremental reparse.** An edit relexes the changed span and reparses the smallest enclosing block.
- **Item tree.** A per-module skeleton query with item ids stable under body edits (module, name and kind).
- **Names and imports.** Module scopes, overload sets by name, and the collision and no-shadowing checks.
- **HIR lowering.** Desugaring into resolved bodies with interned ids.
- **Core inference.** Bidirectional checking over primitives, records, functions and simple unions; exhaustiveness and redundancy of `case` by the pattern-matrix algorithm (Maranget).
- **MIR builder.** A control-flow graph per instance; `case` compiled to decision trees; reference-count increments and decrements placed by liveness; overflow checks and drops made explicit.
- **Code generation.** MIR to CLIF through the facade, with safepoint, frame and line tables per code object.
- **Allocator.** Size classes with per-worker, page-local free lists in the style of mimalloc.
- **Reference counting.** Atomic increments and decrements, skipped for static values; release at zero.
- **Collection primitives.** Persistent lists as RRB trees, and maps and sets as hash array mapped tries (§12), updated in place when unique (§13.4). Sorted maps as persistent B-trees and arenas with generational handles (§13.2) follow with the standard library types that use them.
- **Traps and unwinder.** `rt_trap`, a frame walk over frame pointers and tables that releases live owned values, and trap reports with source positions.
- **Driver.** `crag run`, and `crag test` with test discovery and a runner; diagnostics rendered against source spans.

**Exit:** `crag run` and `crag test` work on a small multi-module program.

## 4 M2 — The type system

&#91;embedded content: M2 components · inference extensions, component fixpoint, instances\]

The type system fills the space between the M1 front end and the MIR builder, following Sections 7 and 8 of the Compiler architecture.

**Components and algorithms**

- **Unions.** Interned union types normalized by absorption after every join, subtyping checks, and flow-sensitive narrowing through `case`, `if` and `let … else`.
- **Error inference.** `callees(fn)` per function, strongly connected components by Tarjan's algorithm, and one monotone fixpoint per component for error unions; `pass` propagation.
- **Generics and forms.** Bounds checked once per generic body; form requirements become slots; the caller records slot fillings from what is visible where it instantiates.
- **Overload resolution and UFCS.** Candidate sets by name, applicability, the return-type filter, specificity ranking within a module, the declaration check for incomparable overloads and ambiguity errors across modules (§5.6.1).
- **Union lifting.** Explicit dispatch nodes in THIR, one arm per union member.
- **Recursive-group diagnostic.** Query cycles in success-type inference reported with every member missing a success type (§3.13.1).
- **Effects.** Effect sets with one entry per closure parameter, substituted at call sites; the `is Pure`, `atomic` and update-closure checks.
- **Escape analysis.** The Local, Scoped and Escaping lattice, parameter summaries in the component fixpoint, bindings-only checks and stream-end capture counts.
- **Closure conversion.** Environment records plus code pointers, placed inline, on the side stack or on the heap by escape level.
- **Monomorphization.** A worklist from the roots; instance keys of function, type arguments and slot fillings; `fields` unrolling, `typeInfo`, and `Immediate` and `Solid` per instance.
- **Tail calls.** Values released before the jump, and side-stack closures copied into the callee's frame (§5.6.3).

**Exit:** the specification's examples for Chapters 3 to 8 compile and run.

## 5 M3 — REPL and compile-time evaluation

&#91;embedded content: M3 components · REPL, scratch image, compile-time evaluation\]

The REPL and compile-time evaluation share the metered tier: both run code the host compiles, the first in the scratch image and the second in the host itself.

**Components and algorithms**

- **Session manager.** Starts and supervises the scratch image, speaks a length-prefixed message protocol over a local socket, and restarts the image after a crash.
- **REPL.** A line editor, multi-line input completed when the parser reports a complete form, `:rebind`, and session definitions treated as non-pub module functions.
- **Code shipping.** The host compiles instances; the scratch image loads the code objects and resolves relocations.
- **Slot tables.** One indirection slot per function, swapped atomically when a definition changes.
- **Value printing.** Results printed from type descriptors, so any value prints without generated code.
- **Metered tier.** Fuel decremented at prologues and loop back-edges, and a per-task memory budget checked by the allocator's slow path.
- **Compile-time evaluation.** `const_eval(site)` queries compile `is Pure` MIR in the host, run it under the step limit (§18.4), and store results as hashed Solid values, also in type positions for type functions.
- **Solid value codec.** Serialization of Solid values, so results can be hashed, cached and embedded in code objects.
- **embed handlers.** Handlers run through compile-time evaluation, with their source files as query inputs.

**Exit:** daily work happens in the REPL; dogfooding starts here.

## 6 M4 — Concurrency

&#91;embedded content: M4 components · scheduler and the concurrency primitives around it\]

Concurrency grows from the M0 fiber runtime into the full set of Chapters 9 to 11, following Sections 9 and 10 of the Compiler architecture.

**Components and algorithms**

- **Scheduler.** Per-worker run queues with work stealing (Chase–Lev deques), parking idle workers, and preemption through the sentinel.
- **I/O poller and timers.** epoll, kqueue and IOCP behind one interface, and a hierarchical timing wheel for `sleep` and `within`.
- **Combinators and groups.** Structured scopes, joins, `firstResult` with loser cancellation, `limit`, and vars captured by value at `start` (§10.2.1).
- **Cancellation checks.** The compiler-inserted checks, a per-task counter of regions where cancellation waits, and unwinding on the cancel status (§10.4).
- **Streams and hubs.** Bounded queues with suspending `put` and `next`, stream ends disposed so the other side reads `Abandoned`, and both hub kinds, `FanOut` and `Broadcast`.
- **Refs.** Version-word cells on the side stack, borrowed reads, and freeing of replaced values deferred until every worker passes a scheduling point.
- **STM.** TL2 with a global version clock, read and write logs on the side stack, savepoints for nested `atomic`, randomized backoff and a serial fallback.
- **Commutative updates.** Detection of `v ⊕ k` closures in MIR, lowered to a brief cell lock (§9.4).
- **ext.** A fiber-aware mutex.
- **Signals.** Per-attempt buffers delivered on commit, conflict or error (§9.5.1).
- **Lazy cells.** Once-cells with an atomic state word and a waiter list.
- **Deferred teardown.** A queue drained by a runtime fiber running Crag drop glue; `Immediate` drop glue and dispose handlers run at once.
- **Verification.** loom models of the scheduler, the STM and the cells, plus stress tests.

**Exit:** a concurrent server example runs under stress tests and a model checker for the scheduler.

## 7 M5 — The IDE

&#91;embedded content: M5 components · editing, reload and debugging over one session\]

Every tool here reads the same query results, so unsaved buffers, the REPL and the running app agree on what the code means (§20.2, §20.8).

**Components and algorithms**

- **Language server.** LSP over query snapshots, with request cancellation on edit, diagnostics pushed on change, completion, hover, go-to-definition, find references, and rename through the CST.
- **Built-in editor.** A rope text buffer whose unsaved contents are query inputs in the buffer view.
- **Formatter.** A pretty printer over the CST in the style of Wadler's algorithm, keeping comments.
- **App image.** The second image process, with app-view inputs and its own slot tables.
- **Reload planner.** Slot planning by signature identity, pausing through the sentinel, the live-root walk over safepoint tables, migration functions under a step limit, the atomic swap, the bounded wait for blocking frames, and retirement of old code (§20.2).
- **Debugger.** A DAP server; breakpoints patched as trap instructions at statement starts; stepping; variables read from safepoint tables; optimized functions sent back to baseline through their slots (§20.3).

**Exit:** a running server is edited with reloads and breakpoints, and external editors work without a plugin.

## 8 M6 — Packages

&#91;embedded content: M6 components · packages, API checks, persisted cache\]

Packages need stable public APIs and a cache that outlives one session, so both arrive together.

**Components and algorithms**

- **Package manifest and resolver.** Selection of the highest required version per package and major (§14.5.1), with no solver and no lock file; package sources fetched into the content-hash store and verified against the SBOM.
- **api.crag generation.** The public surface of a package: signatures, inferred errors, effects and parameter escape levels.
- **api.crag checker.** A diff of two api.crag files classifying each change as compatible or breaking (§20.5), and the version bump it requires.
- **Publishing checks.** Tests, the API diff and reproducible package contents, checked before upload.
- **Persisted store.** Item trees, inferred signatures, MIR and code objects saved by content hash, loaded on a warm start, and garbage-collected by reachability from current projects.
- **File lock.** Shell commands and a running session share the store under a file lock (§20.6).

**Exit:** a package is published, and a second session and the shell commands reuse the persisted cache.

## 9 M7 — Release and transport

&#91;embedded content: M7 components · optimization, release linking, code transport\]

With Cranelift as the only backend, speed comes mostly from MIR optimization; release builds add static linking and reproducibility, and transport adds a checked path for received code.

**Components and algorithms**

- **MIR optimizer.** An inliner with a size-based cost model, Perceus-style reference-count elision with borrow inference, reuse of dead cells, in-place persistent updates (§13.4) and specialization of small closures.
- **Optimizing tier.** Call and loop counters in baseline code, recompilation of hot functions at Cranelift's speed setting, and a swap through their slots.
- **AOT object writer.** Cranelift object output with direct calls and the single static string blob (§20.7).
- **Runtime archives.** The runtime prebuilt as a static archive for each target, itself built reproducibly.
- **Linking.** A bundled lld with a deterministic symbol order and no timestamps, for every supported target.
- **Reproducibility check.** The same release built on two hosts, with the output hashes compared in CI.
- **Transport codec.** Encoding and decoding of code values and their Solid captures (§18.7).
- **Runtime type check.** The front-end crates linked into the release binary to check received code again, only when the program uses `std.transport`.
- **Metered evaluation in release builds.** The metered tier linked in on the same condition, with the platform's JIT permissions handled.

**Exit:** a release build is reproducible across hosts and cross-compiles to every supported target.

## 10 Order considered

Swapping M3 and M4 was considered: concurrency carries more runtime risk, while the REPL gives a tool for testing everything after it. The REPL comes first, because the M0 spike already covers the riskiest part of concurrency.

## 11 Component guide for implementers

This section explains every component and algorithm named in the milestones, for an implementer who knows systems programming (memory, threads, atomics, system calls, linking) but has not built a compiler and has not necessarily used Rust. Each component starts with a short paragraph on what it must achieve and the solution chosen, then lists its data structures and its functions. Names are proposals. Function signatures are written in Rust syntax, explained briefly under "Reading the signatures" below. Links point to descriptions of data structures and algorithms that go beyond the usual textbook set. Where a component's design is recorded in the Compiler architecture tab of the specification, the guide summarizes it and the tab stays the reference.

### 11.1 Terms used throughout

- **Query.** A function whose result the compiler caches and recomputes only when one of its inputs changed. The compiler is a network of queries, from `parse(file)` to `code(instance, tier)`.
- **Incremental computation, early cutoff.** When an input changes, dependent queries are re-run; if a re-run produces the same result as before, the queries depending on it are not re-run. This "early cutoff" keeps edits cheap. See the [Salsa book](https://salsa-rs.github.io/salsa/) for the model.
- **Durability.** A hint on how often an input changes (the standard library rarely, an open buffer constantly), so the engine can skip checking stable parts of the graph.
- **CST (concrete syntax tree).** A tree of the source text that keeps every character, including whitespace and comments, so tools can map any position back to text.
- **HIR, THIR, MIR.** Successive internal forms of a function body: resolved and desugared (HIR), with every expression typed (THIR), and as a control-flow graph of simple operations ready for code generation (MIR).
- **Control-flow graph (CFG).** A function as basic blocks, straight-line sequences of operations, connected by jumps and branches.
- **Instance, monomorphization.** A generic function compiled separately for each combination of concrete type arguments it is used with; each such copy is an instance.
- **Fixpoint.** Repeating a computation until its result stops changing; used where facts about functions depend on each other through recursion.
- **SCC (strongly connected component).** A maximal group of functions that can all reach each other through calls, such as a set of mutually recursive functions.
- **Interning.** Storing each distinct value (a name, a type) once and referring to it by a small integer id, so comparisons are integer comparisons.
- **Code object.** The machine code of one instance plus its relocations and metadata tables.
- **Safepoint, stack map.** A point in generated code where the runtime may inspect the stack, and the table that says which stack slots hold live values there.
- **Fiber.** A user-level thread: its own stack and saved registers, switched by the runtime rather than by the operating system.
- **Tail call.** A call that is the last action of a function; it reuses the caller's frame, so a loop written as recursion runs in constant stack space.
- **Slot table.** An array of function pointers that development code calls through, so a function can be replaced while the program runs.

### 11.2 Reading the signatures

The function lists use Rust syntax. The few notations they need:

- `fn name(x: T) -> R` — a function taking `x` of type `T` and returning `R`; no `->` means it returns nothing.
- `-> !` — the function never returns (it jumps elsewhere or ends the thread).
- `&T` and `&mut T` — a borrowed pointer to a `T` for reading, or for reading and writing; the caller keeps ownership.
- `*mut T`, `*const T` — raw pointers with no checking, as in C.
- `Box<T>` — an owned heap allocation; `Arc<T>` — a shared, atomically reference-counted pointer, used for query results; `Vec<T>` — a growable array; `&[T]` — a borrowed view of part of an array; `&str` — a borrowed UTF-8 string.
- `Option<T>` — either `Some(value)` or `None`; `Result<T, E>` — either `Ok(value)` or `Err(error)`; `io::Result<T>` — a `Result` whose error is an operating-system I/O error.
- `fn f<T: Trait>(x: T)` — a generic function over any type `T` with the named capability; `impl Trait` in an argument means the same; `&dyn Trait` — a pointer to some value with that capability, chosen at run time (the database is passed as `&dyn Db`).
- `unsafe fn` — the caller must uphold rules the compiler cannot check, typically about raw memory.
- `extern "C" fn` — uses the C calling convention, so generated code or C can call it.
- `#[test]` — marks a test function.
- `Range<usize>` — a half-open range `start..end`; `Duration`, `Instant` — a length of time and a point in time; `Path`, `PathBuf` — a borrowed and an owned file path.
- `u8`, `u32`, `u64`, `usize` — unsigned integers of 8, 32, 64 and pointer-sized bits.

### 11.3 M0 components

#### 11.3.1 Fiber runtime

Crag tasks are cheap and numerous, so they cannot each be an operating-system thread. The runtime runs them as fibers: each has its own stack and saved registers, and switching between fibers is a function call that saves a handful of registers and swaps the stack pointer. Worker threads (one per core, later in M4) pick fibers to run. M0 builds one worker and the switch itself.

A suspended fiber is a stack and a saved stack pointer; its registers and the address to continue at lie on its own stack, pushed by the routine that suspended it. A fiber stack moves when it grows, so it holds only frames the runtime can relocate: generated code, the entry stub and the save areas of the runtime's assembly routines. Rust code never runs on a fiber stack; the assembly routines switch to the worker's system stack before calling into Rust.

**Data structures**

- `TaskContext` — what generated code receives as its implicit first argument: the stack limit first, then the worker, the saved stack pointer, the finished flag and the pending stop reasons. All fields are atomics, since other threads request stops.
- `Fiber` — the task context, the stack, the real limit, a state (runnable, running, paused, finished), and the arguments and results, which live on the heap so pointers to them survive growth.
- `StackMemory` — a region from `mmap` with an inaccessible guard page below it, so an unchecked overflow faults instead of corrupting memory.
- `Worker` — the thread running fibers: its saved system-stack pointer and a queue of runnable fibers. The thread's own stack is the system stack.

**Functions**

- `unsafe fn Fiber::new(stub: usize, func: usize, args: &[u64], config: FiberConfig) -> io::Result<Box<Fiber>>` — allocates a small stack and prepares the first frame so that switching to it calls the entry stub, which calls the Crag function.
- `unsafe extern "C" fn switch(save_sp: *mut usize, to_sp: usize)` — the context switch in assembly: push the callee-saved registers, store the stack pointer, load the other one, pop its registers, return.
- `fiber_start` (assembly) — where a new fiber begins. It calls the stub and, when that returns, marks the fiber finished and switches to the worker.
- `fn Worker::resume(&mut self, fiber: &mut Fiber) -> FiberState` — runs one fiber until it finishes or stops.
- `fn Worker::run(&mut self) -> Vec<Box<Fiber>>` — the loop that takes the next runnable fiber and resumes it; a preempted fiber goes to the back of the queue.

#### 11.3.2 Stack check and `morestack`

Fibers start with small stacks and grow them on demand by copying, as Go does ([Go's contiguous-stacks design](https://docs.google.com/document/d/1wAaf1rYoM4S4gtnPh0zOlGzWtrZFQ5suE8qr2sD8uWQ/pub)). Every Crag function begins with a check against the current limit; if it fails, the function calls `morestack`, which runs on the worker's system stack, allocates a larger stack, copies the used part and continues. Copying is safe only if nothing points into the old stack, which the side stack guarantees.

Cranelift writes the prologue itself and its built-in limit check can only trap, so the check is ordinary code at the start of the entry block and runs after the frame is allocated. To make that safe, the limit is not the end of the stack: the runtime keeps a margin of usable bytes below it. A caller that passed its check has its stack pointer at or above the limit, so a callee's frame of at most the frame budget lands inside the margin, and the rest of the margin is reserved for the call into the runtime. The facade reads the frame size of every function it compiles. A function over the budget is entered through a wrapper with a small frame, which checks that the whole frame fits and then tail-calls the body.

**Data structures**

- `stack_limit` in the task context — the first field, read by every check. A passed check means the stack pointer is at or above it.
- `STACK_MARGIN`, `FRAME_BUDGET` and `RUNTIME_RESERVE` in `crag-abi` — the usable bytes below the limit (1024), the largest frame a function may allocate before its check (512), and what an entry into the runtime may use before it switches stacks (512). The smallest stack is therefore larger than the margin.
- Frame-pointer chain — each frame stores the caller's frame pointer, forming a linked list through the stack that the runtime walks and rewrites.

**Functions**

- Margin check (generated code, entry block and loop back-edges) — `if sp < ctx.stack_limit { morestack(ctx, 0) }`.
- Sized check (generated code, wrapper of a function over the frame budget) — `if sp - frame_size < ctx.stack_limit { morestack(ctx, frame_size) }`, then a tail call to the body.
- `rt_morestack(ctx: *const TaskContext, needed: usize)` — an assembly routine that preserves every register, so the passing path of the check pays nothing for it. It saves all registers on the fiber stack, switches to the system stack and calls `morestack_slow`, then restores the registers from the save area, which may have moved, and returns into the same frame.
- `unsafe extern "C" fn morestack_slow(ctx, needed, sp) -> Resume` — takes pending stop requests, grows the stack if the check fails against the real limit, publishes the limit, and tells the assembly routine whether to continue the fiber or switch to the worker.
- `unsafe fn grow_stack(fiber: &mut Fiber, needed: usize, sp: usize) -> usize` — allocates at least twice the size, copies the used bytes to the top of the new stack, adds the address difference to every saved frame pointer in the chain, starting at the saved frame pointer in the register save area, and frees the old stack. Every link is checked to point up the stack and inside it.
- `unsafe fn shrink_stack(fiber: &mut Fiber)` — later: halves a mostly unused stack at a safe point.

#### 11.3.3 Side stack

Some stack values must have an address that other code holds: a closure that does not escape but is passed to a callee, or a large record passed by reference. If those lived on the machine stack, copying the stack would leave dangling pointers. They live instead on a per-fiber side stack that never moves; the machine stack then holds no pointers into itself.

**Data structures**

- `SideStack` — a list of chunks, each allocated once and never moved; a new chunk is added when one fills, so existing addresses never change. A push larger than a chunk gets a chunk of its own. Chunks left behind by calls that returned are kept and reused.
- `side_ptr` and `side_end` in the task context — the bump pointer and the end of the current chunk. A new fiber has both zero, so it allocates no chunk until its first push.

**Functions**

- Push (generated code) — `p = align_up(ctx.side_ptr, align); if p + size <= ctx.side_end { ctx.side_ptr = p + size } else { rt_side_grow(ctx, size, align); retry }`.
- Mark and pop (generated code) — a function that pushes saves both fields on entry and stores them back before it returns or tail-calls, which frees everything it pushed, whichever chunk it ended up in. An address on the side stack must therefore not be returned or passed to a tail call.
- `rt_side_grow(ctx: *const TaskContext, size: usize, align: usize)` — an assembly routine that preserves every register and runs on the system stack. It points the two fields at the next chunk with enough room, reusing or allocating one, and returns nothing; the generated code repeats the push.

#### 11.3.4 Sentinel

The runtime sometimes needs a running fiber to stop at its next safe point: to preempt it, pause it for the debugger, reload code or cancel it. Rather than adding checks, it reuses the stack check: it sets `stack_limit` to a value no stack pointer can pass, so the next prologue or loop check calls into the runtime, which sees the request, handles it and restores the real limit.

**Data structures**

- `SENTINEL` — the largest address, so the unsigned comparison of both checks fails for every stack pointer.
- `pending` flags in the task context — why the fiber was stopped (preempt, pause, reload, cancel).

**Functions**

- `fn request_stop(fiber: &Fiber, reason: StopReason)` — sets the flag, then writes `SENTINEL` to the limit with an atomic store. `StopHandle::request_stop` does the same from another thread.
- Inside `morestack_slow` — the pending flags are taken, the real limit is restored, and a paused or preempted fiber is left with a switch frame on its stack, so resuming it continues after the check. A request that arrives while the limit is being restored puts the sentinel back.

#### 11.3.5 Cranelift facade

[Cranelift](https://cranelift.dev/) is the code generator: it turns a low-level, machine-independent function description (CLIF) into machine code for x86-64, AArch64 and other targets. The facade is our own small interface over it, so the rest of the compiler never depends on Cranelift's types and could switch backends. M0 needs just enough of it to compile hand-written test functions with guaranteed tail calls.

**Data structures**

- `LirFunction` — our lowered form: virtual registers, blocks, calls marked as normal or tail, loads and stores, side-stack pushes, a poll for loop back-edges, and the list of tracked registers that hold owned values. Code generation adds the operations MIR needs (§11.4.10).
- `CodeObject` — machine code bytes, relocations (places to patch with addresses at load time), stack maps and frame information. Every call is a safepoint, the stack check's call included; a stack map gives, for the return address of one call, the stack slots that hold the live tracked values.

**Functions**

- `fn compile(lir: &LirFunction, settings: &CodegenSettings) -> Result<CodeObject, CodegenError>` — translates to CLIF using Cranelift's `tail` calling convention and `return_call` for tail calls, emits the stack check, keeps frame pointers, requests stack maps at calls, runs Cranelift, and adds the sized-check wrapper when the frame exceeds the budget.
- `fn compile_entry_stub(params: u32, returns: u32, settings: &CodegenSettings) -> Result<CodeObject, CodegenError>` — the C-callable stub through which the runtime enters Crag code.
- `fn target_for(triple: &str) -> Result<Target, UnknownTarget>` — picks the instruction set and settings.

#### 11.3.6 Code loader

Code objects must become runnable memory. The loader copies code into pages, resolves relocations against runtime functions and other code objects, and flips the pages from writable to executable, never both at once ([W^X](https://en.wikipedia.org/wiki/W%5EX)).

Protection applies to whole pages, so each load fills a region of fresh pages while they are writable and then makes them executable for good. A later load never reopens a region, so no thread finds code it is running made non-executable under it. Every load therefore uses at least one page, and code compiled together is loaded together.

**Data structures**

- `CodeArena` — one reserved address range, so all code stays within reach of relative branches, with pages committed on demand and a free list of returned page runs, so retired code can be reused later.
- `SymbolTable` — runtime functions and loaded functions to addresses.

**Functions**

- `fn load(arena: &mut CodeArena, symbols: &SymbolTable, code: &CodeObject) -> Result<CodeAddr, LoadError>` — allocate, copy, relocate, protect. For code nothing refers to by number, such as an entry stub.
- `fn load_group(arena: &mut CodeArena, symbols: &mut SymbolTable, group: &[(FuncId, &CodeObject)]) -> Result<Vec<CodeAddr>, LoadError>` — loads functions into one region and enters them in the symbol table. They may refer to each other, to themselves and to functions already loaded. Either all are loaded or none.
- `unsafe fn unload(arena: &mut CodeArena, symbols: &mut SymbolTable, entry: CodeAddr) -> Result<(), LoadError>` — removes one code object once no frame uses it; the pages return to the free list with the region's last object (used from M5).

#### 11.3.7 Salsa facade

[Salsa](https://github.com/salsa-rs/salsa) is the Rust library that provides incremental queries: it records which inputs each query read, invalidates results when inputs change, applies early cutoff and cancels running queries when an input changes. Its API changes between releases, so the compiler uses it only through a thin facade of our own.

Salsa defines queries through macros, so the facade cannot hide it behind plain traits. It re-exports the macros under its own name and owns the parts with real design content: the database type, snapshots and cancellation. Salsa's macros expand to paths starting with `::salsa`, so each crate that defines queries has the line `extern crate crag_db as salsa;` at its root and writes `crag_db::` everywhere else.

**Data structures**

- `RootDatabase` — the facade's handle on all inputs and cached results; snapshots of it can be read from other threads while the main one applies edits.
- `Db` — the trait queries take as `&dyn Db`.
- Input, tracked and interned definitions — the three kinds of Salsa item, declared with `#[crag_db::input]`, `#[crag_db::tracked]` and `#[crag_db::interned]`: inputs (file text), tracked results (a query's output), interned values (names, types). A query returns a reference to its cached result.

**Functions**

- Input setters (generated) — `file.set_text(&mut db).with_durability(Durability::HIGH).to(text)` changes an input, starting a new revision. It waits until every snapshot is dropped and asks the queries running on them to stop.
- `fn RootDatabase::snapshot(&self) -> Snapshot` — a consistent read view for the language server and for reload planning.
- `fn check_cancelled(db: &dyn Db)` — called in long loops, such as compile-time evaluation, to stop work made obsolete by an edit. It unwinds instead of returning.
- `fn catch_cancelled<T>(work: impl FnOnce() -> T) -> Result<T, Cancelled>` — where the unwinding ends; the caller drops its snapshot on `Err`.

#### 11.3.8 Artifact store

Results worth keeping across sessions are stored on disk, keyed by a hash of their content and inputs, so the same input never compiles twice and two processes can share results. M0 builds the skeleton: hashing, storing, loading.

**Data structures**

- Store directory — one file per artifact, named by its key in hex under a two-character subdirectory, plus a directory for files being written. A file holds the [BLAKE3](https://github.com/BLAKE3-team/BLAKE3) hash of the payload, then the payload.
- `ArtifactKey` — the hash of the inputs that determine an artifact. `Store::key(kind)` starts a `KeyBuilder` seeded with the compiler version and the artifact kind; each further input is hashed with its length, so the key depends on where inputs divide.

**Functions**

- `fn Store::open(dir, version) -> io::Result<Store>` — opens or creates the directory; `version` identifies the compiler build.
- `fn Store::put(&self, key: ArtifactKey, bytes: &[u8]) -> io::Result<()>` — writes to a temporary file and renames it into place, which is atomic, so readers never see half a file.
- `fn Store::get(&self, key: ArtifactKey) -> io::Result<Option<Vec<u8>>>` — checks the payload against its hash; a file a crash left incomplete counts as missing and is removed. The store never forces data to disk, since a lost artifact costs only a recompilation.

#### 11.3.9 Stress harness

Stack copying bugs hide until a stack happens to grow at the wrong moment. The harness makes growth happen at every call by starting fibers with the smallest possible stack, and runs every fiber test that way in CI.

In the tortured configuration the limit is set so that the check that just failed barely passes. Every later call fails its check again and moves the stack to a fresh mapping, so a stale pointer into the old stack faults at once.

**Functions**

- `fn run_tortured(test: impl FnOnce(FiberConfig))` — runs the test with the tortured configuration; the frame-pointer chain is verified during every move.
- `FiberConfig::default()` — tortured when the environment variable `CRAG_TORTURE` is set, so CI can stress every fiber test.

### 11.4 M1 components

#### 11.4.1 Lexer

The lexer cuts source text into tokens (names, numbers, strings, operators, braces). Crag uses newlines to end statements, and tools need every character, so the lexer keeps whitespace and comments as "trivia" attached to tokens instead of discarding them.

**Data structures**

- `Token` — kind, byte range in the file, and the trivia before it.
- `TokenKind` — an enumeration of every token type, including an `Error` kind for unrecognized input.

**Functions**

- `fn lex(text: &str) -> Vec<Token>` — a hand-written loop over bytes; string interpolation is lexed by tracking nesting depth inside `{ }`.
- `fn relex(text: &str, old: &[Token], edit: &TextEdit) -> Vec<Token>` — given the new text, relexes from the token before the edit until the token stream matches the old one again. The lexer's state (open brackets and interpolations, the last token kind) changes only by token kind, so replaying the old kinds recovers it at the restart point.

#### 11.4.2 Parser and CST

The parser builds a tree from tokens. It must never give up on broken input, because the editor parses while people type. The tree is lossless: concatenating its leaves gives back the exact source. The chosen layout is a "green/red" tree as in the [rowan](https://github.com/rust-analyzer/rowan) library ([red-green trees explained](https://ericlippert.com/2012/06/08/red-green-trees/)): immutable, shareable "green" nodes store only kinds and lengths, and lightweight "red" wrappers add parents and absolute positions on demand. Expressions with operators are parsed by [Pratt parsing](https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html), a compact technique where each operator has a binding power.

**Data structures**

- `GreenNode`, `GreenToken` — a node holds its kind, text length and children, a token its kind and text, so a green tree is a complete copy of the source; deduplicated so identical leaves and small subtrees share memory.
- `SyntaxNode` — the red view: a green node plus parent and offset.
- `SyntaxKind` — node kinds (`FnDecl`, `CallExpr`, `Block`, `Error`, …). Leaves are tokens or pieces of trivia.
- `ParseError` — message and range.

**Functions**

- `fn parse(text: &str, tokens: &[Token]) -> (GreenNode, Vec<ParseError>)` — recursive descent: one function per grammar rule, such as `fn_decl`, `block`, `statement`. Nesting deeper than a fixed limit is reported and skipped, so no input overflows the stack.
- `fn parse_expr(p: &mut Parser, min_binding_power: u8)` — the Pratt loop for operators and calls.
- `fn recover(p: &mut Parser, anchors: TokenSet)` — on an unexpected token, wraps tokens in an `Error` node until a closing brace or statement newline, then resumes (§2.3).

#### 11.4.3 Incremental reparse

Reparsing a whole file on every keystroke wastes time on large files. Most edits stay inside one block, so the parser reparses only the smallest enclosing block whose braces still balance, and splices the new subtree into the old tree.

**Functions**

- `fn reparse(old: &GreenNode, errors: &[ParseError], edit: &TextEdit) -> (GreenNode, Vec<ParseError>)` — finds the innermost block containing the edit, relexes and reparses its text, splices the new block into the old tree and keeps the errors outside it, shifted. A block qualifies when its braces still balance on their own, it does not turn into a closure, and the nesting limit stays out of reach; otherwise the next block out is tried, and without one the file is parsed in full. The result always equals a full parse.

#### 11.4.4 Item tree

Most queries need only the shape of a module: which functions, types and imports it declares and their signatures, not the bodies. The item tree holds exactly that. Because editing inside a function body leaves the item tree unchanged, early cutoff stops most invalidation right here.

**Data structures**

- `ItemTree` — per module: lists of functions, types, imports, `embed` declarations, each with its signature syntax. A signature is the declaration's green node without its body and without trivia, and the tree holds no positions: a declaration is found again by its index among the module's declarations. So edits to bodies, comments and layout leave the tree equal.
- `ItemId` — module plus name plus kind, stable across body edits, plus an ordinal among the items of the same name and kind, since overloads share a name.
- [Interned](https://en.wikipedia.org/wiki/String_interning) `Name` — identifiers stored once.

**Functions**

- `fn item_tree(db: &dyn Db, module: ModuleId) -> &ItemTree` — a query reading the module's CST, from `fn parse(db: &dyn Db, file: SourceFile) -> &Parse`. `SourceFile` (text) and `ModuleId` (path and file) are inputs.

#### 11.4.5 Names and imports

Every name in the program must be connected to the declaration it refers to. A module's scope holds its own items and the public items of the modules it imports, with the prelude imported into every module but itself; overloaded functions share a name, so a name can resolve to a set. This stage reports bad import paths, name collisions, import cycles and violations of the no-shadowing rule (§5.4, §6.9, §14.1–14.3, §19.3).

Imports are not passed on, so a scope is made from item trees alone: the module's own and those of the modules it imports. Only the types visible in an imported module are needed one step further, to tell which bare names in its `let` patterns bind. No scope query therefore depends on another, and an import cycle never becomes a query cycle. Modules are not names in a scope, since there are no module-qualified references (§14.2).

**Data structures**

- `Program` — an input: the modules of an application or a session, each `ModuleId` with its dotted path.
- `ModuleIndex` — modules by path, and the directories the paths imply.
- `ModuleScope` — name to `Resolution` (a type, a form, or a value and an overload set of functions), plus the errors found making it. Indistinguishable types merge; functions with the same name but an identical signature, and any other two items that meet, collide (§14.3).
- `ImportGraph` — which module imports which, with one `ImportCycle` reported for every group of modules that import each other.

**Functions**

- `fn module_scope(db: &dyn Db, program: Program, module: ModuleId) -> &ModuleScope` — a query over `imports` (the resolved import paths) and `scope_entries` (every candidate with its origin).
- `fn resolve_path(db: &dyn Db, index: &ModuleIndex, path: &[Name]) -> Result<PathTarget, PathError>` — a directory, a module, or an element of a module (§14.1).
- `fn import_graph(db: &dyn Db, program: Program) -> &ImportGraph` — Tarjan's algorithm over the resolved imports.
- `fn check_shadowing(db: &dyn Db, program: Program, module: ModuleId) -> &Vec<Redeclaration>` — the redeclarations HIR lowering finds in the module's bodies, which it checks while it resolves local names (§11.4.6).

#### 11.4.6 HIR lowering

The CST mirrors the text; later stages want something simpler. HIR lowering turns each body into a resolved, desugared tree: names become references to bindings or items, operators and prefixes become calls of their functions, named arguments form one field list on their call, `_` arguments become closures that evaluate their supplied arguments once, and `for`, `let … else` and patterns get explicit forms. Bodies belong to functions, module-level `let`s, tests and type declarations, whose field types and defaults are lowered like a body.

Lowering resolves local names itself, so it also checks the no-shadowing rule, that only a `var` is assigned, and that no closure writes a captured `var` (§5.2, §5.4, §6.4.1). Literals are decoded here: digits, escapes, doubled braces and the indentation of triple-quoted strings (§2.6).

**Data structures**

- `Owner` — what has a body: an `ItemId` of a function, value or type, or a `TestId` made of the module, the test's label and its place among the tests with that label.
- `Body` — arenas of `Expr`, `Pat`, `TypeRef` and `Binding` nodes indexed by small integers, plus the parameters, the result type and the root. It holds no positions.
- `BodySourceMap` — the CST range of every node, beside the body.

**Functions**

- `fn lower_body(db: &dyn Db, program: Program, owner: Owner) -> &LoweredBody` — a query: the body, its source map and its errors. It reruns on every edit of the file.
- `fn hir_body(db: &dyn Db, program: Program, owner: Owner) -> &Body` — the body alone, which stays equal when an edit only moves it, so it stops recomputation of inference.
- `Lowerer::expr`, `Lowerer::pattern` and `Lowerer::type_node` — one case per syntax kind.

#### 11.4.7 Core inference

Inference gives every expression a type and reports type errors. Crag infers locally, within one function, using bidirectional checking ([survey](https://arxiv.org/abs/1908.05839)): the checker either checks an expression against an expected type that flows down from the context, or synthesizes a type from the expression itself. Literals, closures, collection and record literals and generic tags such as `Empty` take their types from the context.

M1 covers primitives, records, functions and unions as written. Where branches meet, their types join into a union, absorbed as in §3.6.1. A call picks the one candidate that fits its arguments, filtered by the expected type and then by the default types of literals, so `1 + 2` is an `Int` addition; M2 ranks the rest by specificity (§11.5.4). Bodies of generic functions are checked with their type parameters as opaque types. What needs M2 or later was reported as not supported yet; narrowing, `pass` and calls of generic functions have since arrived (§11.5.1–11.5.3), and `?.`, conversions, refs, signals and handlers still are. A range is a `Range[T]` or `RangeFrom[T]` of the prelude; `T` fits `Discrete` when it is a built-in integer, `CodePoint`, `Fixed[S]`, or a type with a concrete `compare` and `next` in scope. A decimal literal end has the scale it is written with, and constant ends that decrease are an error.

Builtin types are declarations of the prelude with a builtin's name and number of type parameters and no body, such as `type Int` and `type List[T]` (§19.1). A named type's identity is the declaration that stands for all declarations merging with it (§3.3). The crate is `crag-types`.

**Data structures**

- `Ty` — interned type terms: builtins, named types by their identity, anonymous records, functions, unions, type parameters, and an error type that fits everything, so that one error is reported once.
- `TypeDef` and `Signature` — a type declaration's fields, parent or alias target, and a function's parameter and result types, lowered from the HIR.
- `InferenceResult` — a type for every expression, pattern, binding and written type, the callee of every call, the success type, the holes with their types, and the errors, each at a node of the body. The body's source map gives their ranges.

**Functions**

- `fn body_types(db: &dyn Db, program: Program, owner: Owner) -> &InferenceResult` — the query.
- `fn success_type(db: &dyn Db, program: Program, function: ItemId) -> Option<Ty>` — written, or inferred from the body; none for a recursive function without a written one. `fn value_type` does the same for module-level values. Both infer apart from `body_types` and resolve a cycle as none, so the body that started a cycle still gets its types (§11.5.6 names the group).
- `fn type_header`, `fn alias_target`, `fn type_parent` and `fn type_def` — a declaration as other types see it: its kind and parameters, an alias's target, its parent, and its lowered fields. References and subtyping read only the first three, so recursive types lower without a cycle.
- `Infer::check(expr, expected)` and `Infer::synth(expr)` — the two modes.
- `fn is_subtype(db: &dyn Db, program: Program, s: Ty, t: Ty) -> bool`, `fn join` and `fn normalize` — fitting (§3.13.3), and unions with absorption.
- `fn fields_of(db: &dyn Db, program: Program, ty: Ty) -> Option<Vec<(Name, Ty)>>` — a record's fields, its parent's first.
- `fn module_type_errors(db: &dyn Db, program: Program, module: ModuleId) -> Vec<(Owner, TypeError)>` — for the driver.

#### 11.4.8 `case` checking

Every `case` must cover all possible values (exhaustiveness), and no arm may be unreachable (redundancy). The standard method is the pattern-matrix algorithm from [Warnings for pattern matching](https://doi.org/10.1017/S0956796807006223): rows are arms, columns are positions in the value, and a recursive "usefulness" test answers both questions and produces an example of a missing case. The same test checks that the pattern of a `let` without `else` and of a `for` matches every value (§7.1.1).

The test splits the values of a column into constructors that each pattern covers whole or not at all. A type pattern splits a union into its members, and a member into the subtypes the column names and the rest of it: a record type can have subtypes no pattern names, so only the type itself, or a wildcard, covers that rest. Literals and ranges split a discrete type into intervals at their ends; literals of other types split it into their values and the rest. List patterns split a list by its length, up to the longest they name, and a constructor for all longer lists. A guarded arm is checked for redundancy but covers nothing. An unreachable alternative of an or-pattern is reported by itself, and an arm when all its alternatives are. Patterns that failed to type are not checked, so that one error is reported once. The checker lives in `crag-types` and runs during inference.

**Data structures**

- `Pattern` — a pattern as the test sees it: fields by name, literals as intervals or values, and bindings, which the test looks through and decision trees keep (§11.4.9).
- `PatternMatrix` — rows of patterns, one per unguarded arm or alternative.

**Functions**

- `fn is_useful(&self, matrix: &PatternMatrix, pattern: &Pattern, ty: Ty) -> bool` — the core recursion; exhaustiveness asks whether a wildcard row is useful.
- `fn missing_example(&self, matrix: &PatternMatrix, ty: Ty) -> Option<Witness>` — for the diagnostic, written as a pattern, such as `Int8.min..0` or `Point(x: 0, y: _)`.

#### 11.4.9 MIR builder

MIR is the form code generation consumes: a control-flow graph per instance, with every operation explicit. `case` becomes a decision tree that tests each position at most once ([Compiling pattern matching to good decision trees](https://doi.org/10.1145/1411304.1411311)). Reference-count increments and decrements are inserted from a [liveness analysis](https://en.wikipedia.org/wiki/Live-variable_analysis): a value is released right after its last use. Overflow checks and drops become explicit operations. For `Float` a run of operations shares one check of the sticky overflow flag, and division checks for a zero divisor first (Specification §3.1.4).

The builder evaluates each expression into an operand of the current block; `if`, `case`, `and`, `or` and `for` add blocks, and a `for` polls on its back-edge. A call in tail position whose result needs no conversion is a tail call. The operators of the prelude on numbers are operations rather than calls, and a negated literal is a constant, so `Int8.min` can be written. Where a value meets a type it fits but is not, such as a member passed for a union, an explicit conversion changes its representation. A body with type errors traps where it starts. What the builder does not lower yet, such as `lazy`, default arguments and calls of generic functions, traps where it is reached and is listed in the body. Closures and local functions came with closure conversion (§11.5.9).

Decision trees are built in `crag-types` from the pattern matrix of `case` checking, sharing its constructors. A node tests the first position the first row looks into. A position of several types is first switched on its runtime type, a finer type before the types it is part of; one of a single type is then tested against intervals, literals or list lengths, or, as a record, opened into its fields. A guarded leaf goes on to the rest of the tree when its guard fails. A `let` destructures with the tree of its one pattern, and a typed `let … else` tests the type first.

A counted local, one of a type whose values live on the heap, owns one reference while it is live. An operand gives that reference away, and a place only borrows it, so the reference is retained before every consuming use but the last and released after a last use that only borrows. Drops release what dies unused: a definition nothing reads, an unused parameter, and on each edge what the block holds that its successor does not need; an edge into a block with other predecessors is split. Every check traps in a block of its own, which releases what is live before the trap. The crate is `crag-mir`.

**Data structures**

- `MirBody` — the parameters, the typed locals, and basic blocks, each with statements and one terminator: jump, branch on a `Bool`, switch on the runtime type, call, tail call, return, or trap.
- `Local` — a typed local, not in SSA form; `Place` — a local or a path of steps into it: a field, an element, or the value as a member of its union.
- `Rvalue` — a use, a read of a place, a conversion, arithmetic with or without its check, the flags checks compute, comparisons, record, list and map construction, and the list and map operations patterns and loops need.
- `DecisionTree` — tests of a position's type, interval, literal or length, guards, and leaves naming the arm with the positions of its bindings.
- `InstanceKey` — the owner of a body and its type arguments, empty until monomorphization (§11.5.10); `Tier` — the baseline tier only, for now.

**Functions**

- `fn mir(db: &dyn Db, program: Program, instance: InstanceKey, tier: Tier) -> &Option<MirBody>` — the query: building, then the checks, then the reference counts. None for what has no body, such as a builtin of the prelude.
- `fn decision_tree(db: &dyn Db, program: Program, owner: Owner, subject: Ty, arms: &[(PatId, bool)]) -> Option<DecisionTree>` — the tree for patterns of a body, each with whether its arm is guarded; and `MirBuilder::lower_decision_tree`, which turns it into blocks.
- `fn compute_liveness(body: &MirBody) -> Liveness` — the counted locals live at the edges of each block, by backward dataflow.
- `fn insert_rc_ops(body: &mut MirBody, live: &Liveness)` and `fn insert_drops(body: &mut MirBody, live: &Liveness)`.
- `fn insert_overflow_checks(body: &mut MirBody)`.

#### 11.4.10 Code generation

Code generation translates MIR into the facade's `LirFunction` and has Cranelift compile it. Besides machine code, every code object carries the tables the runtime needs: safepoints with live values, frame layout and source lines.

Each local becomes as many registers as its layout has words (Compiler Architecture §11). Numbers are words: narrow integers stay sign- or zero-extended to 64 bits, and a `Float` is a word holding its bits. A box is a pointer to a 16-byte header, the count and then the type index, followed by the fields: the parent's at their own offsets, then the type's own by name. A union is a type index and a payload word, or the index alone when every member is a tag, so a `Bool` is the index of `True` or `False`. The index is that of the member the value belongs to, which may be a parent of the value's own type; a conversion to a wider union retags the members it absorbs. A type index is the interned type's own index for now. A type test compares the index; a test for a record type finer than the static one reads the box's header and compares it with the indices of the program's record types that fit. Overflow tests use Cranelift's overflow flags for 64-bit types and a range check of the exact result for narrower ones.

Boxes are allocated inline from the worker's heap (§11.4.11) and counted inline (§11.4.12); an empty list or map is allocated inline too, and the runtime grows it and finds its elements (§11.4.13). Checks trap through a call of a runtime function the unwinder provides (§11.4.14). The LIR gained what MIR needs: division, bit operations, shifts, unsigned and `Float` comparisons, `Float` arithmetic on the bits, overflow tests, selects, runtime calls and a trap terminator. What code generation does not handle yet, strings, bytes, module-level values and calls of the prelude's builtins, ends its block with a trap and is listed with the code; function values came with closure conversion (§11.5.9). Stack maps cover the registers holding boxes; line tables wait for MIR to carry positions, and code objects go to the artifact store with the persisted store (§11.9.5). The crate is `crag-backend`.

**Functions**

- `fn layout(db: &dyn Db, program: Program, ty: Ty) -> Option<Layout>` and `fn record_layout(db: &dyn Db, program: Program, ty: Ty) -> Option<(Vec<FieldSlot>, u32)>` — the words of a type, and the fields of a box at their offsets.
- `fn lower_to_lir(db: &dyn Db, program: Program, owner: Owner, mir: &MirBody) -> Lowered` — one case per MIR statement and terminator; the LIR, what it could not lower, and the instances it calls. The owner's source map gives the positions of traps.
- `fn code(db: &dyn Db, program: Program, instance: InstanceKey, tier: Tier) -> &Option<Result<Code, String>>` — the query: the code object, the `FuncId` it is loaded as, its words of parameters and results, and the instances to load with it.

#### 11.4.11 Allocator

Crag allocates many small, short-lived objects, often freed by a different thread than the one that allocated them. The allocator follows [mimalloc](https://github.com/microsoft/mimalloc): memory is split into pages of one size class each, every page has its own free lists, and frees from other threads go to a separate list that the owner collects later, so the common paths need no locks.

Segments are 4 MiB, aligned to their size, and split into pages of 64 KiB; the segment's first bytes describe its pages. There is a size class per word up to 64 bytes and four per doubling up to 8 KiB; `crag-abi` defines them, because generated code picks the class of a box at compile time. A box above 8 KiB gets a segment of its own, which its free unmaps. A page carves its free blocks from its unused end a few at a time, a page whose blocks are all freed goes back to its segment, and a segment without pages in use is unmapped unless it is the heap's last. Each worker owns a heap, and the task context points to it.

Generated code allocates a box inline: it pops the free list of the heap's current page for the class, counts the block as used and writes the header. The class of a heap without a free block has a shared empty page, so the inline path tests only the block it popped, and calls `rt_alloc` when it is null. `rt_alloc` switches to the system stack and runs the slow path there. A heap that is dropped unmaps the segments without live blocks and abandons the others; adopting abandoned segments comes with the scheduler (§11.7.1), and so does a cheaper search for a page with room than the walk over the class's pages done now.

**Data structures**

- `Heap` — per worker: for each size class, the page currently allocated from, and the pages in use.
- `Page` — one size class; a local free list, a thread-free list (atomic), a count of used blocks and the owning heap's id.
- `Segment` — a large aligned region holding pages, so a block's page is found by masking its address.

**Functions**

- `fn Heap::alloc(&mut self, size: usize) -> *mut u8` — the fast path that generated code also inlines: pop from the current page's free list.
- `fn Heap::alloc_slow(&mut self, class: usize) -> *mut u8` — collect the thread-free list, find or create a page.
- `unsafe fn Heap::free(&mut self, ptr: *mut u8)` — push to the local free list if this heap owns the page, else to the thread-free list.
- `unsafe extern "C" fn rt_alloc(ctx: *const TaskContext, size: u64, type_index: u64) -> *mut u8` — the inline path's miss: a box with its header.

#### 11.4.12 Reference counting

Crag frees memory by reference counting: every box has a count of references, and the box is freed when it reaches zero. Values can be shared across threads, so counts change with atomic instructions. A static value, such as a literal in the image, has a count with its top bit set and is never counted.

Generated code counts inline. A retain tests the count's sign and adds one atomically; a release tests the sign, subtracts one atomically, and calls `rt_release` when the count was one. For a union, both first test whether the index names a box. `rt_release` switches to the system stack and frees the box there, releasing its fields as the descriptor of its type lists them. A field whose count reaches zero goes on a list of boxes to free, linked through their dead count words, so freeing a long chain is a loop, needs no memory and cannot overflow a stack. The descriptors are data rather than generated drop glue: the runtime never calls back into Crag code (Compiler Architecture §2.1), and glue that runs Crag code at a drop comes with drop handlers and deferred teardown (Specification §13.5).

Code generation describes each record and collection type it allocates or reads: the code of an instance lists the descriptors of those types, and the image indexes them by type index. A worker holds the image's descriptors. A record or collection holding strings or bytes is not compiled yet, because their references are not counted. A function value's environment is counted like a box, and a null one is skipped (§11.5.9).

**Data structures**

- `TypeDescriptor` — in `crag-abi`: for a record the fields of a box that hold references, each a box pointer or a union with the indices that carry a box; for a list or map the layouts of what it holds (§11.4.13).
- `Types` — the image's descriptors, indexed by type index.

**Functions**

- `fn type_descriptor(db: &dyn Db, program: Program, ty: Ty) -> Option<TypeDescriptor>` — the counted fields of a record type, or the layouts of a collection type's elements.
- `unsafe extern "C" fn rt_release(ctx: *const TaskContext, ptr: *mut u8)` — the inline release's miss: frees the box and what only it held.
- `unsafe fn release_box(heap: &mut Heap, types: &Types, ptr: *mut u8)` — the loop `rt_release` runs.

#### 11.4.13 Collection primitives

Crag's lists, maps and grids are immutable and persistent: an "update" builds a new version that shares unchanged parts with the old one (§12, §13.4). The runtime provides the underlying structures, which grow with the standard library from M1 on: lists as [RRB trees](https://infoscience.epfl.ch/record/169879) (wide trees supporting fast indexing, appending, splitting and concatenation), maps and sets as [hash array mapped tries](https://en.wikipedia.org/wiki/Hash_array_mapped_trie), sorted maps as persistent B-trees, and arenas with [generational handles](https://github.com/fitzgen/generational-arena) for cyclic data (§13.2). When the compiler proves a version has no other user, updates happen in place.

A list is a box with its length, the height of its tree and the tree. Leaves hold up to 32 elements and inner nodes up to 32 children. A balanced node is indexed by the bits of the index; a relaxed one, made by slicing or joining, keeps the cumulative sizes of its children and is searched. Joining rebalances the nodes along the seam until they number at most two more than the fewest that hold their slots, the search step invariant of the paper, so relaxed trees stay shallow. A map is a box with its length and the root of a trie in the compressed form of [CHAMP](https://doi.org/10.1145/2814270.2814312): a node has one bitmap of the entries it holds inline and one of its children, and every child holds two entries or more, so a map's shape does not depend on the order of its updates. Below the depth where the 64-bit hash runs out, collision nodes list entries with equal hashes. A set is a map whose values have no words. Nodes are boxes with the collection's type index and their kind in the upper half of the index word. The descriptor of the type gives the layout of the elements, or of the keys and values, so the runtime counts what they hold and frees nodes like any other box.

An update takes the collection by value. It changes in place every node only the caller's reference reaches, and copies a shared one with references to what it holds (Compiler Architecture §11.3); a caller that keeps the old version retains it first. One function per update thus covers both cases, without `*_unique` variants, and the compiler's proof of uniqueness (§13.4) will later skip the check of the count.

Until generic instances exist (§11.5.10), the runtime hashes and compares keys by their words, so code generation accepts map and set keys that are equal exactly when their words are: integers, code points, `Fixed`, tags and unions of these. Generated code allocates an empty list or map inline and calls the runtime to append, find an element, slice, insert and look up; those functions run on the system stack, like `rt_alloc`. List, map and set literals, indexing, `for` over a list, list patterns with a rest, and map lookups as an `Option` compile; the MIR builder now also lowers a list literal that is a set. Setting an element, joining, removing a key and iterating a map are in the runtime and tested there, waiting for the standard library to call them. Empty collections are allocated, not static singletons, until images hold static data. Sorted maps and arenas come with the standard library types that use them.

**Data structures**

- `List` — the list's box: the header, the length, the height and the tree. `RrbNode` — a leaf of up to 32 elements, or an inner node of up to 32 children with, when relaxed, their cumulative sizes.
- `Map` — the map's box: the header, the length and the root. `HamtNode` — a bitmap node of entries and children, or a collision node of entries with equal hashes.
- `ElementLayout` — in `crag-abi`: the words of an element, key or value and the fields among them that hold references; `TypeDescriptor::List` and `TypeDescriptor::Map` carry them.
- Later: `BTreeNode`, with a fixed node size, and `Arena` — a flat store of slots, each with a generation number; a `Handle` is index plus generation.

**Functions**

- `unsafe fn list::push(heap: &mut Heap, types: &Types, list: *mut u8, value: &[u64]) -> *mut u8` and `list::set(…, i: usize, value: &[u64])` — take the list and the value.
- `unsafe fn list::get(types: &Types, list: *mut u8, i: usize) -> *mut u64` — the address of the element's words, borrowed; `list::slice(heap, types, list, front: usize, back: usize)` and `list::concat(heap, types, a, b)` — new lists, borrowing their arguments.
- `unsafe fn map::insert(heap: &mut Heap, types: &Types, map: *mut u8, key: &[u64], value: &[u64]) -> *mut u8` and `map::remove(heap, types, map, key)` — take the map.
- `unsafe fn map::get(types: &Types, map: *mut u8, key: &[u64]) -> *mut u64` — the value's words, or null; `map::iter(types, map) -> MapIter` — the entries in an unspecified order.
- `rt_list_push`, `rt_list_elem`, `rt_list_slice`, `rt_map_insert`, `rt_map_get` — what generated code calls (`crag_abi::RuntimeFn`).
- Later: `fn arena_insert(arena: &mut Arena, v: Value) -> Handle`, `fn arena_get(arena: &Arena, h: Handle) -> Option<&Value>`, `fn arena_remove(arena: &mut Arena, h: Handle)` — a stale generation traps or returns `Empty`.

#### 11.4.14 Traps and unwinder

A trap (overflow, failed `where` condition, out-of-range index) stops the current computation and transfers control to the nearest handler (§8.3). The runtime finds that handler by walking frames through the frame-pointer chain and, for each frame, releasing the values the safepoint table marks as live.

The frame that traps has already released what it holds: MIR traps in a block of its own that releases what is live (§11.4.9). Every frame below it is suspended at a call, and the stack map of that call lists the slots of the boxes the frame keeps across it. Each such box has a reference of its own, because a counted local owns one while it is live, and a part read out of a value is retained when it lives on. `rt_trap` switches to the system stack and walks the frame-pointer chain down to the fiber's first frame, whose saved frame pointer is zero. It finds each call's stack map by its return address and releases the boxes in its slots. Then it records the trap in the fiber and switches to the worker, and the fiber is `Trapped`. Code generation passes the byte offset of the expression that trapped in its module's source; the code map gives the function of each frame from its return address, and the driver turns both into a report (§11.4.15).

Crag has no trap handlers before signals and handlers (M2), so a trap always ends its task, and the handler table comes with them. Stack maps list only registers holding boxes, so a box inside a union a frame holds is not released when it unwinds: a leak until stack maps carry unions, never a double release. `Immediate` handlers wait for dispose handlers (Specification §13.3).

**Data structures**

- `CodeMap` — the runtime's safepoint table for the loaded code: the return address of each call with the slots of its boxes, and the range of each function's code, from the code objects' stack maps.
- `Trap` — why and where a fiber stopped: the kind, the source position, and the functions of the frames it unwound, the trapping one first.
- Later: `HandlerTable` — code ranges covered by trap handlers and their entry points.

**Functions**

- `unsafe extern "C" fn rt_trap(ctx: *const TaskContext, kind: u64, position: u64) -> !` — switches to the system stack, unwinds and ends the fiber.
- `unsafe fn unwind(worker: *mut Worker, ret: *const usize, fp: usize)` — walks the frames from the trapping one and releases what each holds.
- `fn CodeMap::add(&mut self, func: FuncId, entry: usize, object: &CodeObject)` and `fn CodeMap::function_at(&self, pc: usize) -> Option<FuncId>`; `fn Worker::set_code_map(&mut self, code: Arc<CodeMap>)`.
- `fn Fiber::trap(&self) -> Option<Trap>` — the trap of a fiber whose state is `Trapped`.

#### 11.4.15 Driver and diagnostics

The driver is the command-line entry: it sets up the database, feeds files in as inputs, asks for the queries it needs and runs the result. Diagnostics are printed against source ranges with the offending text underlined.

A project is a directory with a `package.crag`. M1 reads only its `package` and `main` lines; the full manifest comes with the resolver (§11.9.1). Every other `.crag` file below the root is a module named by the package and its path, so `geo/shape.crag` in package `demo` is `demo.geo.shape`. The prelude `std.core` lives in `std/core.crag` and is bundled with the tool (Specification §19.4). It declares the built-in types, `Option`, the orderings, the ranges, `ExitCode`, and the operator functions of the number types, which the MIR builder turns into operations.

Before anything runs, the driver collects the errors of every module: syntax errors, import and name errors, redeclarations, lowering errors and type errors. Each is printed with its file, line and column, the line, and the range underlined; any error stops the command with status 1. `crag run` compiles the instances `main` reaches by following each code object's calls, loads them with the runtime's functions, and runs `main` on a fiber. Its status is 0 for `()` or the code of an `ExitCode`. A trap is reported against the source with the functions of the frames it unwound, a run of one function told once, and the status is 70 (Specification §19.7.1). `crag test [filter]` runs every test whose label contains the filter in a fiber of its own; a test passes when its block completes and fails when it traps, until error values arrive (M2). The command works on the project in the current directory; usage errors exit with 2 (§20.6).

Until `std.test` exists, a test fails itself with `???`. With no I/O yet, a program shows what it computed only through its exit status. The trap report has no positions of the calls below the trapping frame until line tables (§11.4.10).

**Functions**

- `fn crag_run(project: &Path, out: &mut dyn Write) -> u8` — compiles the instances reachable from `main`, loads them, runs a fiber and returns the exit status.
- `fn crag_test(project: &Path, filter: Option<&str>, out: &mut dyn Write) -> TestReport` — discovers tests, compiles them, runs each in its own task and reports the results.
- `fn check(project: &Project) -> Vec<Diagnostic>` — every error of the project's modules.
- `fn render_diagnostic(d: &Diagnostic, file: &str, source: &str) -> String`, and `Image::report` for a trap.

### 11.5 M2 components

#### 11.5.1 Unions and narrowing

Crag types can be unions such as `Int | NotFound`. When two branches meet, their types are joined into a union, and a union that contains both a type and its parent keeps only the parent (absorption, §3.13.2). Inside a `case` arm, `if` or `let … else`, the type of a variable narrows to the members that branch allows; this is flow-sensitive typing, where a variable's type depends on where in the code it is read.

Inference keeps, where control is, the narrowed type of each binding a test narrowed. `x is T` splits it into what holds where the test does and where it does not: `x` narrows to `T` when `T` is one type that fits it, else to the members `T` overlaps, and to the members that do not fit `T` on the other side; a test that never holds is an error. The right operand of `and` sees what the left one established, that of `or` what it ruled out, and `not` swaps the two sides. A `case` on a binding narrows it in each arm to what the arm's pattern matches of the members no earlier unguarded arm covers, which the case checker decides member by member. The `else` part of `let … else` sees the binding narrowed to what the pattern misses, and the code after it to what it matches. Where paths meet, a binding stays narrowed to the union of what each path that gets there narrowed it to; a path of type `Never` does not get there, so after `if x is E { return … }` the rest of the block sees `x` without `E`. Only `let` bindings, `var`s and parameters read by name narrow. Assigning a `var` ends its narrowing, a loop body starts without the narrowings of the `var`s it assigns, and closures and local functions do not see those of `var`s at all.

A narrowed type is never a union of types finer than the members of the binding's type, because a union value is tagged with the member it belongs to. MIR reads a narrowed binding by converting it to the narrowed type.

**Data structures**

- `Ty::Union` — an interned, sorted set of member types, always normalized by absorption (§11.4.7).
- `Flow` — the narrowed type of each binding at the current point of inference, if a test narrowed it.

**Functions**

- `fn join` and `fn normalize` — union plus absorption, already part of core inference (§11.4.7).
- `Infer::condition(expr) -> (Flow, Flow)` — checks a condition and returns the narrowings where it holds and where it does not.
- `Infer::refine(subject, target) -> Option<Ty>` and `Infer::rest(subject, target) -> Ty` — the two sides of a type test.
- `Infer::merge(flows) -> Flow` — the narrowings where paths meet.
- `Body::assigned_in(expr) -> Vec<BindingId>` — the `var`s a loop body assigns.

#### 11.5.2 Error inference over recursive groups

A function's error union is inferred from the errors its body produces and the errors of the functions it calls. Mutually recursive functions depend on each other, so the compiler finds groups of them as strongly connected components with [Tarjan's algorithm](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm), and solves each group by starting from empty unions and repeating until nothing grows. Because unions only grow and the set of declared error types is finite, this always ends.

An error type is one that fits the prelude's `distinct type Error`. A function's own frame is open when its written type names no error: the values its body gives, by its last expression, `return` and `pass`, are split into their error members, which are collected, and the rest, which must fit the written type. Its result is the written type joined with the collected errors. A written type that names an error is the whole result, checked as written. Closures and local functions check their values as written. A function without a written type has the type its body gives, errors included.

The graph is that of the functions each body names, in calls, as values and as the candidates of method calls and fields, every overload included, because inference compares them all (§3.13.1); it needs no inference, so finding a group never depends on the group's types. While a group is solved, each member's body is inferred with the errors found so far, and a call of a member gives its written success type and those errors. A member of a recursive group without a written success type gives none, which the call reports. Calls outside the group read `result_type`, which takes a group's errors from its solution.

`pass` as the body of a `case` arm gives the values no earlier arm handled, those the arm matches, to the caller as `return` does (§8.2); MIR converts the subject to them and returns it. `pass` anywhere else is an error. The `check` prefix `?` does not propagate: it replaces the error members with `Empty` (§8.4); it is a generic prelude function typed with `Oks` (§11.5.3).

**Data structures**

- `callees(fn)` — for each function, the functions its body names.
- `Group` — the members of a function's component, in a fixed order, and whether they depend on themselves.

**Functions**

- `fn callees(db: &dyn Db, program: Program, function: ItemId) -> &Vec<ItemId>` — a query over the HIR body.
- `fn group_of(db: &dyn Db, program: Program, function: ItemId) -> &Group` — Tarjan's algorithm over `callees`, from the function to its component.
- `fn group_errors(db: &dyn Db, program: Program, root: ItemId) -> &Vec<(ItemId, Ty)>` — the fixpoint loop for the group whose first member is `root`; effects (§11.5.7) and escape levels (§11.5.8) will join it.
- `fn result_type(db: &dyn Db, program: Program, function: ItemId) -> Option<Ty>` — what a call gives: the written success type and the group's errors, or the inferred type.
- `fn infer_in_group(db, program, owner, group: &[(ItemId, Ty)]) -> InferenceResult` — inference with the errors of the group so far.
- `fn error_members` and `fn success_members` — the two parts of a union.

#### 11.5.3 Generics and forms

A generic function is checked once against its bounds, not once per use. Inside it, a type parameter is opaque: one bounded by a named type fits that type and has its fields, and one bounded by a form can be passed to the form's functions. A form used as a parameter type stands for a type parameter of its own after the written ones (§4.3). The forms of a function's bounds, with the forms they require in their `where` clause or stand for, give the function its slots: each of their functions with the bound's type arguments, in a fixed order. HIR adds the slots' names to the names a generic body sees, and a call in the body may resolve to a slot like to a function. A union of forms holds when one of them does; which one is known only per type argument, so it gives no slots (§4.7).

A call of a generic function infers the type arguments: first from the arguments that have their own type, then from the expected type, then from the arguments that take their type from the context, a closure getting the parameter types known so far and giving its result. Type arguments written in brackets replace the inference. Each type argument must fit its named bound, and each slot must be filled by a function visible where the call is written that accepts the slot's parameters and gives its result. In a generic caller a slot may be filled by one of the caller's own slots, and a generic function may fill a slot with type arguments inferred from the slot's parameters, to a fixed depth. The most specific filling wins, by the ranking of §11.5.4. The call records the instance, the function with its type arguments and slot fillings, which monomorphization compiles (§11.5.10); until then MIR reports calls of instances and slots as not supported. Generic functions may be used as values when the expected type or type arguments in brackets fix them.

`Oks[X]` and `Errs[X]` are builtin type functions over error unions (§8.1). Applied to a type without type parameters they become the members that are not errors, or those that are; applied to a type parameter they stay until substitution. With them the prelude declares the type mapping functions `discard`, `check` and `expect` and their prefixes `~`, `?` and `!!` as generic functions without bodies (§8.4). Inference checks their two rules: `check` and `expect` need a value with errors, and `check` a value whose successes do not contain `Empty`.

Generic local functions, bounds on the type parameters of types and functions of forms that have type parameters of their own are reported as not supported yet.

**Data structures**

- `Requirement` — in HIR, a bound in brackets or an entry of a `where` clause; `FormDecl` and `SlotDecl` — a form's functions or the forms it stands for; `ItemKind::Slot` — a form's function as an item, outside the module's scope.
- `FormBound` — a form applied to types. `Bounds` — what a generic function's type parameters must fit: named types, forms with what they require, and unions of forms. `FormDef` — what a form requires and its functions.
- `Slot` — one function of a bound's form, with its parameter and result types.
- `Instance` — a generic function with its type arguments and one `Filling` per slot: a declared function's instance or a slot of the caller.
- `FitError` — a type argument outside its bound, a slot with no filling or with several, or a union of forms of which none holds.

**Functions**

- `fn bounds(db: &dyn Db, program: Program, function: ItemId) -> &Bounds`, `fn form_def(db, program, form: ItemId) -> &FormDef` and `fn slots(db, program, function: ItemId) -> &Vec<Slot>`.
- `fn param_bound(db, program, owner: ItemId, index: u32) -> Option<Ty>` — the named bound subtyping and field access use for a type parameter.
- `fn instantiate(db, program, function: ItemId, args: &[Ty], at: CallSite) -> Result<Instance, FitError>` — checks the bounds and fills the slots where the call is written.
- `fn bind(db, program, owner: ItemId, pattern: Ty, found: Ty, args: &mut [Option<Ty>])` — infers type arguments by matching a parameter type against an argument type.
- `fn type_function(db, program, f: Builtin, x: Ty) -> Ty` — evaluates `Oks` and `Errs`.

#### 11.5.4 Overload resolution and UFCS

Several functions may share a name, and `x.f(y)` may call any function `f` whose first parameter fits `x` (uniform function call syntax); HIR lists them all as the candidates of the call, with the slots of a generic body's bounds (§11.5.3). Resolution keeps the candidates whose parameters accept the arguments and, for a generic candidate whose type arguments the typed arguments fix, whose bounds hold. It filters them by a written success type and then by the expected type, and picks the most specific among the candidates of one module. If candidates of more than one module are left, the call is an error. Of the most specific candidates, those the literals fit with their default types stay, so `1 + 2` is still an `Int` addition; more than one left is ambiguous. Slot fillings are chosen the same way, a slot of the caller counting as a candidate of the caller's module.

Candidate A is more specific than B when every call A accepts, B also accepts, but not the reverse; the return type never ranks. Per parameter, A's type is at least as specific as B's when B's type, its type parameters taken as unknowns, has an instance A's type fits. Where each is an instance of the other, a concrete type beats a type parameter, and of two type parameters the one with the larger requirement set wins: its named bound fits the other's, it has every form of the other's, and a union of forms is implied by each of its members. A wins when it is at least as specific on every parameter both take an argument for and more specific on one. Inside one module a call never meets an ambiguity of bounds: two overloads with the same parameter shape and incomparable bounds are rejected at the later declaration unless their combined overload exists, and the error names the signature to add (§5.6.1).

**Data structures**

- `Specificity` — more, less, equal or incomparable.
- `Ranked` — a candidate as ranking sees it: the function whose type parameters its types name, its module, and the type of the parameter each argument goes to.

**Functions**

- `fn compare_param(db: &dyn Db, program: Program, a: (ItemId, Ty), b: (ItemId, Ty)) -> Specificity` — per parameter, by instances and then by requirement sets.
- `fn most_specific(db, program, candidates: &[Ranked]) -> Result<Vec<usize>, Vec<ModuleId>>` — the candidates no other is more specific than, or the modules when there are several.
- `fn overload_errors(db, program, module: ModuleId) -> &Vec<(ItemId, TypeError)>` — at declaration: overloads with the same parameter shape and incomparable bounds that lack their combined overload, with the missing signature.
- `Infer::resolve` — collects the candidates, keeps the applicable ones, filters by the success and expected types, ranks, and checks the chosen one's arguments.

#### 11.5.5 Union lifting

When no candidate accepts a call's arguments but one accepts each combination of the members of its union arguments, the call is split into one call per combination (union lifting, §4.6.1). The arguments split are the unions no candidate takes whole at their position; if that leaves a combination without a function, every union argument is split. Each combination is resolved like a call of its own (§11.5.4), and the call gives the union of their results. A combination without a function, or with several, is an error once another combination resolves; when none does, the call reports its own error. The arguments typed by the context are typed once, so their parameter must be the same for every combination. A generic candidate takes its type arguments from the members, and a lifted call building a record is not supported yet.

An overloaded name used as a value whose expected function type has union parameters is lifted the same way, so `shapes.map(area)` works: a function name passed where the parameter's type chooses or instantiates it waits for that type, like a closure (§11.5.3).

The call records a `Dispatch`. MIR evaluates the arguments once and switches on the tag of each split argument in turn; each arm converts the arguments to their members and calls its function, which may be a primitive operation, and the result is converted to the union. Arms that call instances or slots wait for monomorphization (§11.5.10). A lifted function value gets code of its own that dispatches so (§11.5.9).

**Data structures**

- `Dispatch` — the split arguments, the members of each, and one `DispatchArm` per combination, the last argument's member varying fastest; `Callee::Dispatch` records it for a call or a function value.
- `DispatchArm` — the callee of one combination, a function, an instance or a slot, and its result.

**Functions**

- `Infer::select` — resolution without reporting: the chosen candidate, none, several, or candidates of several modules.
- `Infer::split` — the arguments split and the candidate chosen for each combination, or the error of the first combination that does not resolve.
- `Infer::lift` and `Infer::lift_value` — a lifted call and a lifted function value.
- `MirBuilder::dispatch` — the switches and calls in MIR.

#### 11.5.6 Recursive-group diagnostic

Recursive functions must state their success type, including functions linked through overloads the return-type filter compares (§3.13.1). Each member of a recursive group states it, even where one written type would break the cycle. The groups are those of error inference (§11.5.2): the strongly connected components of the functions each body names, every overload included, so a group never depends on inference. Each group with members missing a success type gets one diagnostic, in the first of them: it names the group and the members missing one, at the first call in that member's body that links it to the group. Calls of those members give the error type without an error of their own; a call that meets a cycle outside a recursive group, through a module-level value, still reports the function.

A name that is a local binding, such as a parameter called `f`, names no function, so it adds no edge to the graph.

**Functions**

- `fn recursion_errors(db: &dyn Db, program: Program, module: ModuleId) -> &Vec<(ItemId, TypeError)>` — the diagnostic of each group whose first member missing a success type is in the module.
- `fn linking_call(body, members) -> Option<ExprId>` — the first call of a member in a body, or its first use as a value.

#### 11.5.7 Effects

Effects record what a function may do beyond computing: `io`, resolving refs (`ref`), emitting signals (`signal`). A function taking a closure has the closure's effects too, so its effect set contains an entry "the effects of parameter `f`" that each call site replaces with the effects of the closure actually passed (§3.14); a generic function has an entry per slot, which the call's slot fillings replace. Effects are solved in the same group fixpoint as errors. The `is Pure`, `atomic` and update-closure rules are checked against the result.

The effects of a body come from a walk over it once inference has resolved its calls. Calling a C function is `io`, an `ext` access is `io` as well, a ref's access functions are `ref`, and `emit` is `signal`; the prelude's other functions without bodies call the functions passed to them. A call gives the callee's effects with its entries replaced: a closure argument by its body's effects, a parameter of the caller by the caller's entry, a declared function by its effects, and a value of a plain function type, such as a field, by every effect. Closures, local functions and `lazy` expressions do not run where they are written, so they count where they are called; reading a `Lazy` waits for lazy cells (§11.7.11).

The restricted contexts are checked in the same walk. An `is Pure` function has no effects of its own but may call its closure parameters; a call of it must give it functions without effects. A closure or declared function without effects has a Pure type, so it fits a parameter marked `is Pure`, and one with effects does not. An `atomic` block and a ref's `update` closure do no `io`, which includes `ext` accesses; an `update` closure resolves no ref but its own; an `ext` closure accesses no other `ext`. The rules of M4 for suspending operations in atomic blocks wait for streams and tasks (§11.7.5).

To make the rules checkable, inference now types `ref` and `ext` bindings as `Ref[T]` and `Ext[T]`, whose access functions the prelude declares as generic functions without bodies, `atomic` blocks, whose value is the block's or the error that aborts it, and `emit` of a `Signal`. MIR still reports them as not supported until M4 (§11.7.6–§11.7.10).

**Data structures**

- `EffectSet` — bits for `io`, `ref`, `signal` and, within `io`, `ext` accesses, plus the indices of the closure parameters and slots it takes on.
- `GroupMember` — a member of a group's solution: its errors and its effects.
- `Restriction` — `is Pure`, `atomic` or `update`, in the errors that name it.

**Functions**

- `fn function_effects(db: &dyn Db, program: Program, function: ItemId) -> EffectSet` — of a body from its group's solution, or of a function without a body by `intrinsic_effects`.
- `EffectSet::substitute(params, slots)` — at a call site; `EffectSet::closed` — for a function used as a value, whose entries stand for any effect.
- `Walker::walk_body(pure)` — the effects of a body and the errors of its restricted contexts; `Walker::closure` — the effects of one closure, which give its type its Pure marker.

#### 11.5.8 Escape and bindings-only analysis

The compiler must know whether a value can outlive the frame that created it: refs and other bindings-only values must never do so (§3.12), and values that never escape can live on the stack or side stack. Each value gets one of three levels: Local (used only in this frame), Scoped (captured by a task that ends before the scope) or Escaping (returned, stored or passed somewhere unknown). Callees are summarized per parameter, and summaries are solved in the group fixpoint (Section 8 of the architecture).

The analysis walks a body once inference has resolved its calls, and gives each binding and each frame, a closure, a `lazy` expression or a local function's body, a level that grows from Local until nothing changes. A value is Escaping where it is returned, also from a closure, whose caller is unknown, placed in a record, collection or construction, held by a `ref` or `ext` cell, emitted, or passed to a closure parameter, a field or a slot. An argument of a declared function goes at the level its summary gives the parameter; a `let` passes on the level of its binding, and a `case` subject the levels of the arms' bindings. A use in a frame that does not declare the binding captures it, so the binding is at least at that frame's level. A summary is the level of each parameter. A C function may keep any argument; the prelude's operations call the functions they are passed and keep only what their result's type parameters can hold, and an access function keeps the value it places in its cell.

Bindings-only values are the `ref` and `ext` cells, values of the types `Ref[T]` and `Ext[T]`, and the closures, `lazy` values and local functions that capture one, directly or through another. Where one goes out itself it is an error; a capture is reported at the closure that carries it. An escaping closure that captures a `var` is an error at the closure (§6.4.1). Nothing gives Scoped yet: the combinators and groups whose tasks capture values, and the rules for groups, hubs and stream ends with their capture counts, come with M4 (§11.7.3, §11.7.5).

**Data structures**

- `EscapeLevel` — Local, Scoped or Escaping, ordered.
- `Escapes` — the levels of a body's parameters, its summary, and of its frames, with the bindings each frame captures, which closure conversion places and puts into environments (§11.5.9).
- `BindingsOnly` — a ref, an `ext` cell, a closure or a `lazy` value, in the error that names it.

**Functions**

- `fn param_escapes(db: &dyn Db, program: Program, function: ItemId) -> &Vec<EscapeLevel>` — the summary, from the group's solution or by `intrinsic_escapes` for a function without a body.
- `EscapeWalker::walk_body` — the levels of a body, the errors of its bindings-only values and its escaping closures that capture `var`s.

#### 11.5.9 Closure conversion

A closure is code plus the values it captured. Conversion turns each closure into an environment record of the captured values and a function, its code, that takes the environment as its first argument. A function value is two words: the address of the code and the environment, a box or null when nothing is captured (Compiler Architecture §11). Calling one passes its environment, then the arguments, to its code, through the address.

The code of a closure is an instance of the body that holds it, keyed by the closure's expression. It takes the environment and the closure's parameters, matching those written as patterns, and reads each captured value out of the environment into the binding's own local, so the body is built like any other. Escape analysis gives the bindings each closure captures, its inner closures' included, so a nested closure finds what it captures among its parent's locals. A local function is a closure with a name: its code binds that name to itself with the environment it was called with, so it calls itself without capturing itself and without a cycle of counts. A declared function used as a value, a primitive operation of the prelude included, gets code of its own at the expression that names it, which takes an empty environment and calls the function; a lifted value's code splits its arguments as a lifted call does (§11.5.5).

Where the environment lives follows from the closure's escape level. A Local or Scoped closure's environment goes on the side stack, where it is freed when its frame returns; its header has the static count, so counting it does nothing, and it borrows what it captures, which liveness keeps alive as long as the closure and every copy of it are. An Escaping closure's environment is a box on the heap that holds a reference to each captured value and is released like any box, so a closure stored in a record or a list is counted with it. A closure made inside a loop also goes on the heap, because the side stack would grow by one environment per iteration until the function returns. A trap releases the environments the frames hold; the unwinder skips null ones and the static count those on the side stack.

Until tail calls copy side-stack closures into the callee's frame (§11.5.11), a call in tail position is a plain call in a function that has put an environment on the side stack, since the tail call would free it. A closure that captures a `var` is not lowered yet: it must read the variable as it is when the closure runs, so the variable has to move to the side stack (Compiler Architecture §8). Inlining a closure into a known callee, which needs no environment at all, comes with the MIR optimizer (§11.10.1). A function value that converts to a function type with other parameter or result types, which needs code that converts the values, is not compiled yet; one that is Pure fits a function type that is not, as it is.

**Data structures**

- `Entry` — which code of an owner an instance is: its body, a closure's code by the closure's expression, or a declared function's code as a value by the expression that names it. Every entry but the body takes an environment first.
- `ClosurePlacement` — SideStack or Heap.
- `Rvalue::Closure` — a function value: its code, its environment's type, a record whose fields are named by position, and the captured values; `Rvalue::FnValue` — one of its code with an environment it has, which is how a local function names itself.
- `Terminator::CallValue` and `Terminator::TailCallValue` — calls of a function value.
- `Liveness::holds` — the locals each local borrows through the side-stack closures it may hold.
- `Layout::Closure` — the two words of a function value; `Inst::FuncAddr`, `Inst::CallIndirect` and `Term::TailCallIndirect` in the LIR.

**Functions**

- `fn place(level: EscapeLevel, in_loop: bool) -> ClosurePlacement`.
- `MirBuilder::closure_value(frame, ty, own)` — the closure's environment and value where it is made; `MirBuilder::closure_entry(frame)` and `MirBuilder::function_entry(expr)` — the parameters and start of a closure's code and of a function's code as a value.

#### 11.5.10 Monomorphization

Each generic function is compiled separately for each set of type arguments and slot fillings it is used with. A worklist starts from the roots (`main`, tests, REPL input), and every instance reached adds the instances it calls. At this point `fields` loops are unrolled per concrete record, `typeInfo` becomes a constant, and properties such as `Immediate` and `Solid` are decided per instance.

**Data structures**

- `InstanceKey` — function, type arguments, slot fillings; interned.
- `Worklist` — instances still to visit, plus a set of those already seen.

**Functions**

- `fn collect_instances(db: &dyn Db, roots: &[InstanceKey]) -> Vec<InstanceKey>`.
- `fn substitute_body(db: &dyn Db, thir: &Thir, key: InstanceKey) -> Thir` — replaces type parameters and slots.
- `fn is_immediate(db: &dyn Db, ty: TypeId) -> bool` and `fn is_solid(db: &dyn Db, ty: TypeId) -> bool` — per concrete type.

#### 11.5.11 Tail calls

A call in tail position must not grow the stack (§5.6.3). Before the jump, the caller releases the values it still owns, and closures it placed on its side stack that it passes to the callee are copied into the callee's side-stack frame, because the caller's side-stack frame is popped.

**Functions**

- `fn lower_tail_call(b: &mut MirBuilder, call: ExprId)` — releases, copies side-stack arguments, pops the side-stack mark, emits Cranelift's `return_call`. Until it does, a function that puts a closure's environment on the side stack makes no tail calls (§11.5.9).

### 11.6 M3 components

#### 11.6.1 Session manager

The host process runs the compiler; user code runs in separate image processes, so a crash or an infinite loop in user code never takes the compiler down (§20.1). The session manager starts the images, talks to them over a local socket and restarts an image that dies.

**Data structures**

- `ImageHandle` — process id, socket, kind (scratch, later app), state.
- `Message` — a length-prefixed, versioned message: load code, evaluate, print value, pause, reload, debugger requests, and replies.

**Functions**

- `fn spawn_image(kind: ImageKind) -> io::Result<ImageHandle>`.
- `fn send(image: &mut ImageHandle, msg: &Message) -> io::Result<()>` and `fn receive(image: &mut ImageHandle) -> io::Result<Message>`.
- `fn on_image_exit(session: &mut Session, image: ImageId, status: ExitStatus)` — reports the reason and starts a fresh image.

#### 11.6.2 REPL

The REPL reads input, compiles it and shows the result. Each input becomes a definition in a session module, treated like a non-pub module function, so the same queries that serve files serve the REPL; `:rebind` replaces a definition and invalidates what depends on it.

**Data structures**

- `SessionModule` — an in-memory module holding the session's definitions as query inputs.
- `LineEditor` — history, editing keys, completion via the language queries.

**Functions**

- `fn read_input(editor: &mut LineEditor) -> Option<String>` — keeps reading lines until the parser reports a complete form; `None` at end of input.
- `fn eval_input(session: &mut Session, text: &str) -> Result<EvalOutput, Vec<Diagnostic>>` — adds a definition or expression to the session module, compiles the new instances, ships them, asks the scratch image to run them.
- `fn rebind(session: &mut Session, name: &str, text: &str) -> Result<(), Vec<Diagnostic>>` and `fn run_command(session: &mut Session, command: &str)` — for `:` commands.

#### 11.6.3 Code shipping

The host compiles; the image only loads. The host sends code objects with their relocations, and the image's loader places them and patches their addresses. Only instances the image does not already have are sent, identified by their content hash.

**Functions**

- `fn ship(image: &mut ImageHandle, code: &[Arc<CodeObject>]) -> io::Result<()>` — on the host side; skips objects the image already has.
- `fn load_shipped(loader: &mut Loader, code: Vec<CodeObject>) -> Result<(), LoadError>` — in the image: the M0 loader plus registration in the slot table.

#### 11.6.4 Slot tables

In development images, calls between functions go through a table of function pointers, one slot per function. Replacing a definition writes a new pointer into its slot, and every later call reaches the new code; frames already running finish on the old code.

**Data structures**

- `SlotTable` — an array of code addresses, indexed by slot number.
- `SlotIndex` — assigned per function and signature by the host, stable for the session.

**Functions**

- `fn slot_set(table: &SlotTable, index: SlotIndex, addr: CodeAddr)` — an atomic store.
- Generated call sequence — load the slot, call through it.

#### 11.6.5 Value printing

The REPL prints any value without generated code: the runtime walks the value guided by its type descriptor, the same metadata the codec and debugger use.

**Data structures**

- `TypeDescriptor` — per concrete type: kind, size, field names and offsets, union member tags, element type of collections.

**Functions**

- `unsafe fn print_value(value: *const u8, ty: &TypeDescriptor, limits: PrintLimits) -> String` — recursive, with depth and length limits for large values.

#### 11.6.6 Metered tier

Code run at compile time, and code received from elsewhere (§18.7), must not run forever or exhaust memory. The metered tier is the baseline tier plus a fuel counter in the task context, decremented at each function entry and loop back-edge, and a memory budget checked when allocation takes the slow path. Running out of either traps.

**Data structures**

- `fuel` and `memory_budget` in the task context.

**Functions**

- Generated fuel check — subtract the cost of the block from `ctx.fuel`, call `rt_trap(TrapKind::OutOfSteps, pos)` if it goes negative.
- `fn charge_allocation(ctx: &mut TaskContext, size: usize) -> Result<(), OutOfMemory>` — in the allocator's slow path.

#### 11.6.7 Compile-time evaluation

Constants, conditions with known inputs, `embed` handlers and type functions are evaluated while compiling (§18.3–18.4). The host compiles the needed `is Pure` code in the metered tier and runs it in its own process, which is safe because pure code does no I/O and the step limit bounds it. Each result is a Solid value, hashed and cached as a query result.

**Data structures**

- `ConstValue` — a Solid value in serialized form, plus its hash.
- `EvalSite` — where evaluation was requested: a constant, a type position, an `embed`.

**Functions**

- `fn const_eval(db: &dyn Db, site: EvalSite) -> Result<ConstValue, EvalError>` — the query: collect instances, compile metered, run under the step limit, serialize the result.
- `fn type_function(db: &dyn Db, call: TypeCallId) -> Result<TypeId, EvalError>` — evaluation in a type position, returning a compile-time `Type` value.
- `fn poll_cancel(db: &dyn Db) -> Result<(), Cancelled>` — called with each fuel refill so an edit can cancel a long evaluation.

#### 11.6.8 Solid value codec

Compile-time results must be stored, hashed and embedded into code objects, and later the transport sends values between processes. The codec turns Solid values (immutable, with no refs or handles) into bytes and back, deterministically, so equal values give equal bytes and equal hashes.

**Functions**

- `unsafe fn encode(value: *const u8, ty: &TypeDescriptor, out: &mut Vec<u8>)` — canonical: sorted map keys, fixed integer widths.
- `fn decode(bytes: &[u8], ty: &TypeDescriptor, heap: &mut Heap) -> Result<Value, DecodeError>`.
- `fn embed_constant(code: &mut CodeObject, value: &ConstValue) -> DataOffset` — places the bytes in the code object's static data.

#### 11.6.9 embed handlers

`embed` runs a handler at compile time over a source file, such as parsing a data file into a constant. The file's content becomes a query input, so editing the file reruns only the affected evaluations.

**Functions**

- `fn embed_source(db: &dyn Db, path: EmbedPath) -> Arc<[u8]>` — an input query, watched for changes.
- `fn run_embed(db: &dyn Db, site: EmbedSite) -> Result<ConstValue, EvalError>` — `const_eval` with the file contents as argument.

### 11.7 M4 components

#### 11.7.1 Scheduler

The scheduler spreads fibers over one worker thread per core and keeps all cores busy. Each worker has its own queue; an idle worker steals work from another's queue (work stealing). The queue is a [Chase–Lev deque](https://dl.acm.org/doi/10.1145/1073970.1073974): the owner pushes and pops at one end without locks, thieves take from the other end with an atomic compare-and-swap. Workers with nothing to do park on the operating system until woken.

**Data structures**

- `RunQueue` — a Chase–Lev deque of runnable fibers per worker.
- `GlobalQueue` — a locked queue for fibers woken from outside any worker, such as by I/O.
- `Parker` — per worker: sleep and wake on a futex or condition variable.

**Functions**

- `fn spawn(worker: &Worker, fiber: Box<Fiber>)` — push to the current worker's deque.
- `fn schedule(worker: &mut Worker) -> Box<Fiber>` — pick the next fiber: own deque, then the global queue, then steal, then park.
- `fn suspend(ctx: &mut TaskContext, reason: WaitReason)` and `fn wake(fiber: FiberRef)` — the building blocks every waiting operation uses.
- `fn preempt_tick(workers: &[Worker])` — a timer that requests a stop on fibers running too long (through the sentinel).

#### 11.7.2 I/O poller and timers

I/O must never block a worker thread. Sockets and files are set non-blocking; an operation that would block registers interest with the operating system's readiness interface (epoll on Linux, kqueue on BSD and macOS, IOCP on Windows) and suspends the fiber. Timers for `sleep` and `within` live in a [hierarchical timing wheel](https://blog.acolyer.org/2015/11/23/hashed-and-hierarchical-timing-wheels/), which inserts and cancels in constant time.

**Data structures**

- `Poller` — the operating-system handle plus a map from registration to waiting fiber.
- `TimerWheel` — levels of slot arrays, each level coarser than the one below.

**Functions**

- `fn register(poller: &Poller, fd: RawFd, interest: Interest, fiber: FiberRef) -> io::Result<()>` and `fn poll(poller: &Poller, timeout: Option<Duration>) -> Vec<FiberRef>`.
- `fn timer_add(wheel: &mut TimerWheel, deadline: Instant, fiber: FiberRef) -> TimerId`, `fn timer_cancel(wheel: &mut TimerWheel, id: TimerId)`, `fn timer_advance(wheel: &mut TimerWheel, now: Instant) -> Vec<FiberRef>`.
- `fn io_read(ctx: &mut TaskContext, fd: RawFd, buf: &mut [u8]) -> io::Result<usize>`, and likewise `io_write`, `io_accept`, `io_connect` — try the operation, register and suspend on "would block", retry when woken.

#### 11.7.3 Combinators and groups

Crag's concurrency is structured: tasks are started by combinators (`all`, `firstResult`, …) or groups, and never outlive the scope that started them (Chapter 10). The implementation is a scope object that counts its children, collects their results and waits until all have finished; cancellation of a scope reaches every child.

**Data structures**

- `Scope` — parent fiber, list of child fibers, results slots, the first failure, a limit on running children.
- `Group` — a scope whose body keeps running while it starts tasks.

**Functions**

- `fn scope_start(scope: &Scope, closure: ClosureRef) -> FiberRef` — vars are captured by value at start for groups (§10.2.1).
- `fn scope_join(ctx: &mut TaskContext, scope: &Scope) -> Result<Vec<Value>, Failure>` — suspends until every child finished.
- `fn first_result(ctx: &mut TaskContext, scope: &Scope) -> Result<Value, Failure>` — takes the first success and cancels the rest.
- `fn scope_cancel(scope: &Scope)` — cancels children recursively.

#### 11.7.4 Cancellation checks

A cancelled task must stop soon, even if it never waits (§10.4). Cancellation sets a flag and the sentinel, so the next compiler-inserted check in a call or loop unwinds the task. Inside regions where stopping is not allowed (atomic blocks, update and `ext` closures, foreign calls, drop and dispose handlers) a counter defers it until the region ends.

**Data structures**

- `cancel_requested` and `no_cancel_depth` in the task context.

**Functions**

- `fn cancel(fiber: FiberRef)` — sets the flag and the sentinel, wakes the fiber if it is waiting.
- `fn enter_no_cancel(ctx: &mut TaskContext)` and `fn exit_no_cancel(ctx: &mut TaskContext)` — generated around deferring regions; the exit checks for a pending cancellation.
- `unsafe fn unwind_cancelled(fiber: &mut Fiber) -> !` — the unwinder of M1, running `Immediate` drops and disposing stream ends.

#### 11.7.5 Streams and hubs

A stream connects one producer to one consumer with a bounded buffer: `put` suspends when it is full, `next` when it is empty (§10.5). When one end is dropped, the other side sees `Abandoned`. A hub is a shared channel whose producers and consumers join and leave at runtime (§10.6). It comes in two kinds that differ only in distribution: `FanOut` hands each value to exactly one consumer, whichever asks first, and `Broadcast` delivers each value to every consumer through one buffer per consumer, so `put` waits for the slowest. Consumers read `Closed` once the hub is sealed and every producer has closed.

**Data structures**

- `StreamChannel` — a ring buffer, the waiting producer or consumer, and flags for each end's disposal.
- `Hub` — the kind (fan-out or broadcast), the capacity, the count of open producer ends, the sealed flag, and the queue: one shared ring buffer with a list of waiting consumers for fan-out, or one ring buffer per consumer for broadcast.

**Functions**

- `fn stream_new(capacity: usize) -> (Sender, Receiver)`.
- `fn put(ctx: &mut TaskContext, tx: &Sender, v: Value) -> Result<(), Abandoned>` and `fn next(ctx: &mut TaskContext, rx: &Receiver) -> StreamItem` — `StreamItem` is a value, `Done` or `Abandoned`.
- `fn dispose_end(end: StreamEnd)` — wakes the other side.
- `fn hub_new(kind: HubKind, capacity: usize) -> Hub`.
- `fn hub_sink(hub: &Hub) -> Sender` and `fn hub_source(hub: &Hub) -> Receiver` — join as a producer or a consumer. A broadcast consumer receives values from its join point on. Closing an end leaves the hub without ending it.
- `fn hub_put(ctx: &mut TaskContext, hub: &Hub, v: Value)` — fan-out: enqueue for the first consumer that asks; broadcast: copy into every consumer's buffer, suspending while any is full. The non-suspending `tryPut` reports `Full` instead.
- `fn hub_seal(hub: &Hub)` — admits no further producers.
- `fn hub_release(hub: &Hub, n: usize)` — fan-out only: makes `n` waiting consumers read `Closed`, which is how workers are scaled down.

#### 11.7.6 Refs

A ref is a mutable cell shared by tasks. It holds a version word (whose lowest bit doubles as a lock) and a value word. Readers read without locking and without touching the reference count; a value replaced by a write is not freed at once but handed to deferred teardown, which frees it only after every worker has passed a scheduling point, so no reader still holds it. This is a form of [epoch-based reclamation](https://docs.rs/crossbeam-epoch).

**Data structures**

- `RefCell` — `version` (atomic, lock in the low bit) and `value` (atomic pointer or immediate).
- `Epoch` — a global counter plus each worker's last observed value.

**Functions**

- `fn ref_read(cell: &RefCell) -> (u64, Value)` — version and value; retries while the lock bit is set.
- `fn ref_update(ctx: &mut TaskContext, cell: &RefCell, f: ClosureRef) -> Result<(), Value>` — read, run the closure, lock if the version is unchanged, write, release with a new version; otherwise rerun; an error value from the closure is returned and nothing is written (§9.3).
- `fn retire(worker: &mut Worker, old: Value)` and `fn advance_epoch(epoch: &Epoch)`.

#### 11.7.7 STM

`atomic` blocks change several refs at once, all or nothing. The chosen software transactional memory is [TL2](https://doi.org/10.1007/11861201_14): a global version clock is read when an attempt starts; each read checks that the cell has not changed since; writes are kept in a log; at commit the written cells are locked in address order, the clock is incremented, the reads are checked again and the writes applied. A conflict reruns the block; after repeated reruns the block runs alone under a global lock so it cannot starve.

**Data structures**

- `GlobalClock` — an atomic counter.
- `TxLog` — on the side stack: the read set (cell, version) and the write set (cell, new value), with savepoints for nested blocks.
- `SerialLock` — the fallback lock.

**Functions**

- `fn tx_begin(ctx: &mut TaskContext) -> TxLog`, `fn tx_read(log: &mut TxLog, cell: &RefCell) -> Result<Value, Conflict>`, `fn tx_write(log: &mut TxLog, cell: &RefCell, v: Value)`.
- `fn tx_commit(log: &mut TxLog) -> Result<(), Conflict>`.
- `fn tx_savepoint(log: &TxLog) -> Savepoint` and `fn tx_rollback_to(log: &mut TxLog, sp: Savepoint)` — for an inner `atomic` that ends in an error.
- `fn backoff(attempt: u32)` — randomized exponential delay.

#### 11.7.8 Commutative updates

Updates such as `counter.update { v -> v + 1 }` give the same result in any order, so they need not rerun when another task wrote first (§9.4). The compiler recognizes closures shaped like `v ⊕ k` and lowers them to a short critical section on the cell's lock bit.

**Functions**

- `fn detect_commutative(closure: &MirBody) -> Option<(CommOp, Operand)>` — a MIR pattern match.
- `fn ref_apply_locked(cell: &RefCell, op: CommOp, k: Value) -> Result<(), Trap>` — lock, apply with the overflow check, write, unlock with a new version.

#### 11.7.9 ext

`ext` wraps state that cannot be retried, such as foreign handles (§9.6). It is a mutex that suspends a waiting fiber instead of blocking its thread.

**Data structures**

- `FiberMutex` — a locked flag and a queue of waiting fibers.

**Functions**

- `fn ext_lock(ctx: &mut TaskContext, m: &FiberMutex)` and `fn ext_unlock(m: &FiberMutex)` — unlock hands the lock to the next waiter.

#### 11.7.10 Signals

Signals defer effects out of atomic blocks and update closures (Chapter 11). Emissions during an attempt are buffered; on commit the unqualified and `ok` ones are delivered, on a conflict the `retry` ones, on an error the `fail` ones (§9.5.1).

**Data structures**

- `SignalBuffer` — per attempt, emissions in order with their qualifier.

**Functions**

- `fn emit(buf: &mut SignalBuffer, signal: Value, qualifier: Qualifier)` and `fn deliver(ctx: &mut TaskContext, buf: SignalBuffer, outcome: Outcome)`.

#### 11.7.11 Lazy cells

A `lazy` value is computed at most once, by whichever task first needs it; others wait for it.

**Data structures**

- `LazyCell` — an atomic state word (unstarted, running, done), the value and a list of waiting fibers.

**Functions**

- `fn lazy_force(ctx: &mut TaskContext, cell: &LazyCell) -> Value` — the first caller runs the computation; others suspend until it is done.

#### 11.7.12 Deferred teardown

Dropping a large structure must not stall a task (§13.5). Above a size threshold, the release is queued and a runtime fiber frees it gradually, running `Deferred` dispose handlers on the way. `Immediate` values are never queued.

**Data structures**

- `TeardownQueue` — a multi-producer queue of values to release.

**Functions**

- `fn queue_teardown(q: &TeardownQueue, v: Value)` and `fn teardown_fiber(q: &TeardownQueue) -> !` — the latter frees in small batches and yields between them.

#### 11.7.13 Verification

Concurrency bugs depend on rare interleavings. [loom](https://github.com/tokio-rs/loom) runs a concurrent Rust test under every relevant interleaving of its atomic operations, which suits the deques, cells, STM commit and lazy cells. Stress tests then run the whole runtime under load.

**Functions**

- `#[test] fn loom_model_deque()`, `loom_model_ref_cell()`, `loom_model_tx_commit()`, `loom_model_lazy()` — one loom model per primitive.
- `fn stress_server(seed: u64, duration: Duration)` — runs the server example with random delays injected at suspension points.

### 11.8 M5 components

#### 11.8.1 Language server

Editors talk to language tools through the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) (LSP), JSON messages over standard input and output. Crag's server answers from the same queries the compiler uses, on a read-only snapshot, so answers stay consistent while edits arrive; an edit cancels requests made obsolete by it.

**Data structures**

- `DocumentStore` — open documents with their versions, fed into the database as buffer-view inputs.
- `RequestTable` — requests in flight with their cancellation tokens.

**Functions**

- `fn did_change(server: &mut Server, doc: DocumentUri, edits: Vec<TextEdit>)` — updates the input and triggers fresh diagnostics.
- `fn publish_diagnostics(server: &Server, doc: DocumentUri)`.
- `fn completion(snap: &Snapshot, pos: FilePosition) -> Vec<CompletionItem>`, `fn hover(snap: &Snapshot, pos: FilePosition) -> Option<Hover>`, `fn goto_definition(snap: &Snapshot, pos: FilePosition) -> Vec<Location>`, `fn find_references(snap: &Snapshot, pos: FilePosition) -> Vec<Location>`, `fn rename(snap: &Snapshot, pos: FilePosition, new_name: &str) -> Result<WorkspaceEdit, RenameError>` — each maps the position to a CST node, then asks name resolution or inference.

#### 11.8.2 Built-in editor

The editor keeps text in a [rope](<https://en.wikipedia.org/wiki/Rope_(data_structure)>), a balanced tree of string chunks, so inserting into a large file costs time proportional to the logarithm of its size. Unsaved contents are query inputs in the buffer view, so the REPL can try a function before it is saved (§20.2).

**Data structures**

- `Rope` — balanced tree of text chunks with byte and line counts in each node.
- `Buffer` — rope, file path, undo history, cursor positions.

**Functions**

- `fn insert(buf: &mut Buffer, offset: usize, text: &str)`, `fn delete(buf: &mut Buffer, range: Range<usize>)`, `fn line_to_offset(buf: &Buffer, line: u32) -> usize`.
- `fn push_to_queries(buf: &Buffer, db: &mut Database)` — after a short pause in typing.

#### 11.8.3 Formatter

`fmt` prints a file in the canonical layout, keeping comments. It walks the CST and builds a document of text pieces and possible line breaks, then lays it out to fit the line width with [Wadler's pretty-printing algorithm](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf), which chooses for each group whether it fits on one line or must break.

**Data structures**

- `Doc` — text, line break, indent, group, concatenation.

**Functions**

- `fn to_doc(node: &SyntaxNode) -> Doc` — one rule per syntax kind.
- `fn layout(doc: &Doc, width: usize) -> String`.

#### 11.8.4 App image

The app image is the running program during development (§20.1). It is like the scratch image but runs from the app view of the code, the state of the last successful reload, and is the target of reloads and the debugger.

**Data structures**

- `AppView` — the set of file versions the app runs, held as a separate input set keyed by view.

**Functions**

- `fn start_app(session: &mut Session, entry: FunctionId) -> io::Result<ImageId>` and `fn stop_app(session: &mut Session)` — through the session manager.

#### 11.8.5 Reload planner

A hot reload replaces code in the running app as one transaction (§20.2). It decides which slots get new code and which functions need new slots, pauses every task at a safepoint, checks the values that are still alive against the new types, runs migrations, swaps everything at once and resumes. If any check fails, nothing changes.

**Data structures**

- `ReloadPlan` — slots to overwrite, new slots, refs needing migration, type descriptors to install.
- `LiveRoots` — ref cells, `ext` bindings, session bindings and live frame values found by walking stacks.
- `BlockingFrame` — an old-code frame that still uses a migrated ref, with its task and source line.

**Functions**

- `fn plan_reload(db: &dyn Db, old: ViewId, new: ViewId) -> Result<ReloadPlan, Vec<Diagnostic>>` — compares signatures by type identity.
- `fn pause_all(image: &mut ImageHandle) -> PauseToken` — the sentinel on every task; foreign calls count as paused.
- `fn walk_roots(image: &ImageHandle) -> LiveRoots` — stacks via safepoint tables, plus static cells.
- `fn wait_for_blocking(image: &mut ImageHandle, frames: &[BlockingFrame], timeout: Duration) -> Result<(), Vec<BlockingFrame>>` — the bounded wait for frames to return or tail-call.
- `fn run_migrations(image: &mut ImageHandle, plan: &ReloadPlan) -> Result<(), MigrationError>` — metered pure code in the app.
- `fn commit(image: &mut ImageHandle, plan: ReloadPlan)`, `fn resume_all(token: PauseToken)`, `fn retire_old_code(image: &mut ImageHandle)` — the last once nothing uses the old code.

#### 11.8.6 Debugger

The debugger speaks the [Debug Adapter Protocol](https://microsoft.github.io/debug-adapter-protocol/) (DAP), so any editor supporting it can drive Crag. Breakpoints are trap instructions patched into code at statement starts taken from the line table, so they hit even in frames already running. Variables are read using the safepoint tables; an optimized function with a breakpoint is swapped back to baseline through its slot (§20.3).

**Data structures**

- `Breakpoint` — source line, the code addresses it maps to, the original bytes that were patched.
- `PausedTask` — its fiber and a decoded list of frames.

**Functions**

- `fn set_breakpoint(dbg: &mut Debugger, file: FileId, line: u32) -> Result<BreakpointId, NoCodeAtLine>` and `fn clear_breakpoint(dbg: &mut Debugger, id: BreakpointId)`.
- `fn on_trap_instruction(dbg: &mut Debugger, fiber: FiberRef, addr: CodeAddr)` — identifies the breakpoint and pauses the task.
- `fn stack_trace(task: &PausedTask) -> Vec<FrameInfo>`, `fn variables(frame: &FrameInfo) -> Vec<Variable>`, `fn step_over(task: &mut PausedTask)`, `fn step_into(task: &mut PausedTask)`, `fn step_out(task: &mut PausedTask)`, `fn resume(task: PausedTask)`.

### 11.9 M6 components

#### 11.9.1 Package manifest and resolver

Every manifest states each dependency as one exact version, and different majors of a package may coexist through transitive dependencies (§14.5). Within each major, the application settles on the highest version any manifest requires (§14.5.1). Each pair of package and major is therefore selected on its own, and no constraint solving is needed: the resolver walks the manifests from the application outward and keeps the maximum version seen per pair, as in Go's [minimal version selection](https://research.swtch.com/vgo-mvs). Raising a selection can bring in that version's own imports, so the walk repeats until nothing changes; it ends because selections only rise and the registries hold finitely many versions. The result follows from the manifests alone, so there is no lock file. The SBOM records the content hash of every resolved package, and the build refuses a package whose hash differs from the committed SBOM.

Selection itself cannot fail; resolution fails only when a manifest imports two majors of one package, a package or version is missing, a name resolves in more than one registry without `from` (§20.4), or a newly imported version is yanked.

**Data structures**

- `Manifest` — package name and version, runtime version, exports, the entry module, and imports, each with its exact version, an optional `from` source and the `dev` flag (§14.5.1).
- `Resolution` — for each package and major, the selected version and its content hash, plus the dependency graph that `deps` shows.
- `Sbom` — the committed content hashes of every resolved package (§16.7).

**Functions**

- `fn parse_manifest(text: &str) -> Result<Manifest, Vec<Diagnostic>>`.
- `fn resolve(root: &Manifest, registries: &[Registry]) -> Result<Resolution, ResolveError>` — the worklist over manifests; `ResolveError` names the manifest and import that caused it.
- `fn verify_sbom(resolution: &Resolution, sbom: &Sbom) -> Result<(), Vec<HashMismatch>>` — a mismatch stops the build until the SBOM is regenerated on purpose.
- `fn fetch(store: &Store, package: &PackageId, version: &Version) -> Result<ArtifactKey, FetchError>` — downloads into the content-hash store and verifies the hash.

#### 11.9.2 api.crag generation

A package's public surface is written to `api.crag`: every pub declaration with its signature and the parts the compiler inferred, namely errors, effects and parameter escape levels (§20.5). It is generated from the same queries as the compiler, so it always matches the code.

**Functions**

- `fn public_api(db: &dyn Db, package: PackageId) -> Arc<ApiFile>` — a query over the item trees and outward signatures.
- `fn write_api(api: &ApiFile) -> String` — in a canonical order, so diffs are meaningful.

#### 11.9.3 api.crag checker

Publishing compares the new `api.crag` with the last published one and classifies every change: adding a function is compatible; removing one, gaining an error or effect, or a parameter becoming Escaping is breaking (§20.5). The required version bump follows.

**Functions**

- `fn diff_api(old: &ApiFile, new: &ApiFile) -> Vec<ApiChange>`.
- `fn classify(change: &ApiChange) -> Compatibility` and `fn required_bump(changes: &[ApiChange]) -> Bump` — `Compatibility` is compatible or breaking; `Bump` is major, minor or patch.

#### 11.9.4 Publishing checks

Before upload, the tool runs the tests, checks the version against the API diff and verifies that the package contents are reproducible from the sources.

**Functions**

- `fn check_publish(db: &dyn Db, package: PackageId) -> Vec<Problem>` and `fn upload(package: &PackageArchive, registry: &Registry) -> Result<(), UploadError>`.

#### 11.9.5 Persisted store

The M0 store now holds real results: item trees, outward signatures, MIR and code objects, keyed by the hash of what produced them. A new session loads them instead of recomputing (warm start). Old entries are removed by a garbage collection that keeps whatever current projects still reach.

**Data structures**

- `StoreIndex` — for each artifact kind, input hash to artifact hash; plus last-use times.

**Functions**

- `fn persist<T: Persistable>(store: &Store, query: QueryKind, key: ArtifactKey, result: &T) -> io::Result<()>` and `fn restore<T: Persistable>(store: &Store, query: QueryKind, key: ArtifactKey) -> io::Result<Option<T>>` — called by the facade around expensive queries.
- `fn collect_garbage(store: &Store, live_projects: &[ProjectRoot]) -> io::Result<GcReport>`.

#### 11.9.6 File lock

Shell commands such as `crag build` may run while a session is open, and both write the store (§20.6). An advisory file lock on the store directory serializes writers; readers need no lock because every write is an atomic rename.

**Functions**

- `fn lock_store(store: &Store, mode: LockMode) -> io::Result<StoreGuard>` — shared or exclusive; the lock is released when the guard is dropped.

### 11.10 M7 components

#### 11.10.1 MIR optimizer

Cranelift optimizes individual functions only lightly, so the language-specific work happens on MIR. Inlining copies small callees into callers, which removes call overhead and exposes further simplifications. Reference counting is reduced following [Perceus](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/): parameters that a function only reads are passed "borrowed" without count changes, and when a value dies just as a same-sized one is built, its memory is reused in place. Persistent updates on values the compiler proves unique happen in place (§13.4).

**Data structures**

- `InlineCost` — an estimate of a function's size and of its benefit at a call site.
- `BorrowSignature` — per function and parameter: owned or borrowed.

**Functions**

- `fn inline_call(body: &mut MirBody, site: CallSite, callee: &MirBody)` and `fn should_inline(callee: &MirBody, site: CallSite) -> bool`.
- `fn infer_borrows(db: &dyn Db, function: InstanceKey) -> Arc<BorrowSignature>` — a fixpoint over the call graph.
- `fn elide_rc(body: &mut MirBody, borrows: &BorrowTable)` — cancels increment and decrement pairs and applies borrow signatures.
- `fn insert_reuse(body: &mut MirBody)` — pairs a dying value with an allocation of the same size.
- `fn specialize_closure_calls(body: &mut MirBody)` — calls a known small closure directly.

#### 11.10.2 Optimizing tier

Baseline code counts calls and loop iterations per function. When a counter crosses a threshold, the host recompiles that function with full MIR optimization and Cranelift's speed setting, and swaps it in through its slot; frames already running finish on the baseline code.

**Data structures**

- `ProfileCounters` — per function: call count and back-edge count, read by the host periodically.

**Functions**

- `fn collect_profile(image: &mut ImageHandle) -> Vec<(InstanceKey, ProfileCounters)>` — the hot functions since the last read.
- `fn recompile_optimized(db: &dyn Db, instance: InstanceKey) -> Arc<CodeObject>` and `fn swap_slot(image: &mut ImageHandle, instance: InstanceKey, code: Arc<CodeObject>) -> io::Result<()>`.

#### 11.10.3 AOT object writer

Release builds compile ahead of time into an object file for the target: direct calls instead of slots, all string literals in one static blob (§20.7), and no development metadata beyond what traps and dispose need.

**Functions**

- `fn emit_object(db: &dyn Db, instances: &[InstanceKey], target: &Target) -> Result<Vec<u8>, CodegenError>` — Cranelift's object output with symbols named deterministically.
- `fn build_string_blob(literals: &[&str]) -> (Vec<u8>, Vec<u32>)` — the blob and each literal's offset.

#### 11.10.4 Runtime archives

The runtime is written in Rust and must be linked into every release binary. It is prebuilt once per supported target as a static library archive and shipped with the toolchain, so users need no Rust toolchain to cross-compile.

**Functions**

- `fn runtime_archive(target: &Target, features: RuntimeFeatures) -> PathBuf` — picks the archive matching the target and the features the program uses.

#### 11.10.5 Linking

The object file and the runtime archive are combined into an executable by [lld](https://lld.llvm.org/), the LLVM linker, bundled with the toolchain because it can link for every target from any host. Inputs are passed in a fixed order and options that embed times or paths are turned off, so the output depends only on the inputs.

**Functions**

- `fn link(objects: &[PathBuf], archives: &[PathBuf], target: &Target, out: &Path) -> Result<(), LinkError>` — builds the lld command line deterministically.

#### 11.10.6 Reproducibility check

A release must be bit-for-bit identical when built from the same sources on another machine ([reproducible builds](https://reproducible-builds.org/)). CI builds every release on two different hosts and compares the hashes; any difference fails the build.

**Functions**

- `fn build_twice_and_compare(project: &Path, hosts: [&Host; 2]) -> Result<(), DiffReport>`.

#### 11.10.7 Transport codec

Code transport sends code values between programs (§18.7). The codec extends the Solid value codec with code: a portable form of the received functions (their typed IR, not machine code) plus their Solid captures.

**Functions**

- `fn encode_code(code: &CodeValue, out: &mut Vec<u8>)` and `fn decode_code(bytes: &[u8]) -> Result<UntrustedCode, DecodeError>`.

#### 11.10.8 Runtime type check

Received code is untrusted, so the receiving program checks it again with the same front-end crates the compiler uses: names resolve against what the program exposes, types and effects match the declared policy. These crates are linked into a release binary only when it uses `std.transport`.

**Functions**

- `fn check_received(code: UntrustedCode, policy: &Policy) -> Result<CheckedCode, Rejection>`.

#### 11.10.9 Metered evaluation in release builds

Checked code runs in the metered tier with fuel and a memory budget, compiled by Cranelift inside the release binary. Generating code at run time needs memory that becomes executable: macOS requires an entitlement for it, and iOS forbids it, which rules out transport there.

**Functions**

- `fn run_metered(ctx: &mut TaskContext, code: &CheckedCode, fuel: u64, memory_budget: usize) -> Result<Value, MeterError>` — `MeterError` is out of steps or out of memory.
- `fn jit_memory(size: usize) -> io::Result<JitPages>` — platform-specific allocation of executable memory.
