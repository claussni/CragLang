# Crag Compiler Architecture — Working Draft

This document records how the toolchain described in Chapter 20 is built. It is not normative: the language is defined by the specification, and an implementation may differ wherever this document and the specification disagree. Section 2 records decisions. Sections 3 to 6 describe the pipeline, and Sections 7 to 11 refine inference, escape analysis, shared state, the boundary with the runtime and value representation.

## 1 Requirements taken from the specification

- One incremental query compiler shared by the REPL, the language server, the built-in editor, hot reload and the shell commands (§20.2, §20.8), holding the buffer view and the app view in one cache.
- Three processes: host, app image and scratch image (§20.1). Hot reload is a transaction that checks live roots against the new types; development images call between modules through indirection tables.
- Execution tiers: a fast baseline tier for REPL and development code, an optimizing tier for hot functions, and ahead-of-time release builds that are reproducible, link the runtime statically and cross-compile (§20.7).
- Compile-time evaluation by the REPL's evaluator under a step limit (§18.4), including type functions over `Type` (§18.3).
- A runtime with stackful fibers on growable, copied stacks, a scheduler over non-blocking I/O, atomic reference counting, mimalloc-style allocation with deferred teardown, runtime-owned maps and arenas, streams and hubs, guaranteed tail calls, and a separate system stack for foreign calls (Ch. 10, 13, 16).
- Runtime re-type-checking of transported code and metered evaluation (§18.7).

## 2 Implementation decisions

- **Language.** The compiler, the host and the runtime are written in Rust.
- **Query system.** Salsa provides the in-memory incremental graph, behind a thin facade of our own, so its API changes stay in one place and a hand-rolled query system remains a fallback.
- **Backend.** Cranelift is the only backend, behind a facade. LLVM is considered later only if top-notch optimization is needed; two backends are not worth their cost.
- **Persistence.** Results survive sessions in a content-hash artifact store, which is also the build cache of §20.4 and the cache that shell commands share with a session under a file lock (§20.6). Salsa itself holds nothing across sessions.
- **Recursive groups.** The fixpoints of §3.13.2 (error unions, inferred returns, effects) are computed in one query per strongly connected component of the call graph, not through Salsa's cycle handling.
- **No interpreter.** Every tier, compile-time evaluation and metered transport included, runs Cranelift-generated code, so every frame on a fiber stack has a layout the compiler knows.

### 2.1 Runtime discipline

- **Side stack.** Every address-taken stack value (non-escaping closures, records passed by reference) lives on a per-fiber side stack that never moves. The machine stack holds no pointers into itself, so growing a stack copies it and rewrites only the frame-pointer chain.
- **System stack.** Runtime code never sits on a fiber stack across a growth or suspension point; it runs on the worker's system stack, as foreign calls do (§13.6).
- **No callbacks.** The runtime never calls Crag code from its own stack: map operations are generated code, deferred teardown runs on a runtime-owned fiber of ordinary Crag frames, and foreign callbacks run on a fixed stack (Section 10).
- **No thread-locals.** Fibers migrate between worker threads, so runtime state is reached through a worker-context pointer, never through `thread_local!`. Panics abort.

## 3 Intermediate representations

- **CST.** Lossless syntax tree with error nodes. Used by the editor, the formatter and refactorings.
- **Item tree.** Per module, the declaration skeletons only: names, signature syntax, imports and `embed` sources. Editing a function body leaves it unchanged, which makes it the main incremental firewall.
- **HIR.** Resolved, desugared bodies. UFCS calls become candidate sets; operators and prefixes become calls; named arguments become records; `for`, `let … else` and patterns get explicit forms.
- **THIR.** HIR with every expression typed, every call resolved, and each union lifting turned into an explicit dispatch node.
- **MIR.** One per instance (function plus concrete type arguments): a control-flow graph with explicit reference-count operations, drops, dispose timing, overflow checks, marked tail calls and safepoints.
- **CLIF.** Cranelift's IR, reached only through the backend facade.

## 4 Stages

- **Parsing.** Resilient, incremental per buffer. Recovery is anchored at braces and statement newlines (§2.3), so one broken function never breaks its neighbours.
- **Names and imports.** A module scope combines its own items with its imports. Overload sets, collisions and the no-shadowing rule are checked here (§5.4, §14.2–14.3).
- **Signatures.** Written types are lowered to interned `Type` values; type functions are evaluated here through compile-time evaluation.
- **Inference.** Per function: local bidirectional checking, union absorption where branches meet, flow-sensitive narrowing, overload resolution (specificity within a module, cross-module ties are errors, the return type only filters) and union lifting (§3.13, §4.6, §5.6.1). Generic bodies are checked once against their bounds; form requirements stay as slots until monomorphization.
- **Recursive groups.** One query per strongly connected component runs the fixpoints for error unions, inferred return types and effects together.
- **Effects.** The effects of a body plus those of each closure parameter at its call sites. The `is Pure`, `atomic` and update-closure checks run here (§3.14, §9.5).
- **Escape and bindings-only analysis.** On THIR with per-function parameter summaries: refs, `ext` bindings, groups, hubs, stream ends and ref-carrying closures are never stored or returned; each stream end is captured once; vars are never captured by escaping closures; each closure is placed on the stack, the side stack or the heap (§3.12, §9.2, §10.5.3, §13.1).
- **Monomorphization.** Instances are collected from the roots (`main`, tests, REPL input, hot functions). It unrolls `fields`, fills form slots with concrete functions, and decides `Immediate`, `Solid` and `typeInfo` per instance.
- **Compile-time evaluation.** MIR of `is Pure` code is compiled in the host with step counters; results are hashed Solid values. It covers constants, conditions with known inputs, `embed` handlers and type positions (§18.4).
- **Lowering to MIR.** `case` becomes decision trees over tags carrying the full type; a closure becomes an environment record plus a code pointer; `lazy` becomes a once-cell with an atomic state; a ref becomes a runtime cell, or a plain local when it has one user; `update` becomes a compare-and-swap loop with reruns; `atomic` becomes runtime transaction-log calls; `ext` becomes a lock.
- **MIR optimization.** Inlining, Perceus-style reference-count elision and reuse, in-place persistent updates (§13.4) and commutative ref updates (§9.4). Most of the speed comes from here, since Cranelift optimizes little.
- **Code generation.** One code object per instance and tier: machine code, relocations, stack maps, line tables and frame tables.

## 5 Execution tiers

- **Baseline.** Light MIR optimization and Cranelift's fast setting. Calls between modules go through indirection slots, with safepoint polls for the debugger and cancellation. The host compiles; images load the code objects.
- **Optimizing.** Full MIR optimization and Cranelift's speed setting, still behind slots. A breakpoint sends the function back to baseline (§20.3).
- **Release.** Full optimization and direct calls, the single static string blob of §20.7, linked with a bundled lld against the runtime prebuilt as a static archive per target.
- **Metered.** Baseline plus step counters, used for compile-time evaluation and for transported code (§18.7). It is linked into a release build only when the program can receive code.

## 6 Queries and invalidation

All file inputs are keyed by view (buffer or app). Identical text hashes the same, so the two views share most results.

| Query | Invalidated by |
| --- | --- |
| `parse(file)` | an edit to that file |
| `item_tree(module)` | signature, import or `embed` changes only |
| `module_scope(module)` | its own item tree, or an imported module's |
| `signature(fn)` | its syntax, or a type it names |
| `body_types(fn), scc_summary(group)` | an edit to a member body, or a callee's outward signature |
| `inferred_signature(fn)` | firewall: an unchanged success type, errors, effects and parameter escape levels stop rechecking of callers |
| `escape_summary(fn)` | its body, or a callee's summary |
| `mir(instance, tier)` | THIR, escape results, or bodies of inlined callees |
| `const_eval(site)` | the MIR of everything it reaches |
| `code(instance, tier)` | the MIR hash; persisted in the artifact store |
| `reload_check(app view, roots)` | never cached across reloads |

The artifact store keeps item trees, inferred signatures, MIR and code objects keyed by content hash.

## 7 Inference and recursive groups

- **Two phases.** `body_types(fn)` does local bidirectional checking, narrowing, overload resolution and union lifting. Its result is THIR with every call resolved, plus the errors and effects the body produces itself. When it calls a non-pub function with no written success type, it asks for that type on demand. `scc_summary(group)` then runs on the exact call graph: strongly connected components are found by walking `callees(fn)`, and each group runs one fixpoint, starting empty, for error unions, effects and parameter escape levels.
- **Outward signature.** `signature(fn)` holds the written parts, the inferred success type (non-pub only), the inferred errors, the effects and the parameter escape levels. Callers depend only on it, so editing a body that leaves it unchanged rechecks nothing else. REPL definitions are treated like non-pub module functions, so `:rebind` invalidates their dependents through the same queries.
- **Effects.** An effect set is `io`, `ref` and `signal` plus one entry per closure parameter, such as "the effects of `f`". A call site replaces that entry with the effects of the closure actually passed (§3.14). The set is finite, so the fixpoint terminates.
- **Error unions.** A set of declared types, normalized by absorption after every join (§3.13.2). Errors carried in a closure's return type are part of that type, not of the fixpoint.
- **Generics.** A generic body is checked once against its bounds; a call through a bound becomes a slot. The caller's body typing records which functions fill the slots, from what is visible where it instantiates the generic. An instance key is the function, its type arguments and its slot fillings.
- **Missing success types.** A query cycle in success-type inference marks a recursive group, including cycles through every overload the return-type filter compares (§3.13.1, §5.6.1). The diagnostic names every member missing a success type and the call that links them.
- **Resilience.** A failed expression gets an error type that silences follow-up errors; a `???` hole takes its expected type; a broken body changes no other function unless it changes its own outward signature.

## 8 Escape and bindings-only analysis

- **Levels.** *Local*: used in this frame only, called or passed to a Local parameter. *Scoped*: captured by a task of a combinator or group, which ends before the scope does. *Escaping*: returned, stored in a record, collection or ref, captured by an escaping closure, or passed to an unknown function.
- **Summaries.** One level per parameter, computed in the component fixpoint of Section 7 and part of the outward signature. For pub functions they are recorded in `api.crag`, so a parameter becoming Escaping is a breaking change (§20.5).
- **Unknown callees.** A closure parameter or a function stored in a field has no summary, so its arguments count as Escaping. A ref-carrying closure cannot be passed to one; `xs.map { … }` is fine because `map` is known.
- **Checks.** Refs, `ext` bindings, groups, hubs, stream ends and ref-carrying closures or `lazy` values are never Escaping (§3.12). An escaping closure never captures a var (§6.4.1). A stream end is counted across sibling task closures, and a task started in a loop counts as many, so capturing an end there is an error (§10.5).
- **Placement.** A Local closure passed to a known higher-order function that inlines gets no environment. Other Local and Scoped closures, records passed by reference and vars read by closures live on the side stack without reference counting; task closures sit on the parent fiber's side stack, safe because the parent waits and the side stack never moves. Escaping closures go to the heap. A side-stack closure passed in a tail call is copied into the callee's side-stack frame (§5.6.3).
- **Group tasks.** A task started through a group captures vars by value at `start` (§10.2.1).

## 9 Shared state: refs, atomic and ext

- **Cells.** A ref cell is a version word, whose low bit is a lock, plus a value word holding an immediate or a pointer to an immutable, reference-counted box. Refs are bindings-only, so a cell lives on the declaring frame's side stack and has no count of its own. Module-level refs are static cells and are live roots for hot reload.
- **Reads.** A reader takes the value without incrementing its count. A value replaced by a commit goes to deferred teardown and is freed only after every worker has passed a scheduling point, so no reader sees it freed.
- **Single-ref update.** Read version and value, run the closure. If it returns the identical value or an error value, nothing is written (§9.3). Otherwise lock the cell if the version is unchanged, write, and release with the version incremented; if the version changed, rerun. `use`, `swap` and `empty` follow the same path; a ref with one user becomes a plain local (§9.2).
- **atomic.** A TL2 write log on the side stack. Each attempt reads a global version clock; each read checks that the cell's version is no newer, otherwise the attempt reruns, so a doomed attempt never sees inconsistent values. Writes are buffered and read back within the block. Commit locks the written cells in address order, increments the clock, validates the reads, writes and unlocks. When the compiler knows every ref a block touches, the log is fixed slots. An inner `atomic` joins its outer one through a savepoint, so an inner error drops only its own changes. Reruns back off randomly, and after a bounded number the block runs alone under a global lock.
- **Signals.** Emits inside an attempt are buffered in emission order. On commit, unqualified and `ok` signals are delivered after unlocking; on a conflict, `retry` signals are delivered and the attempt reruns; on an error, `fail` signals are delivered (§9.5.1, §11.2). Other signals of a discarded attempt are dropped.
- **Commutative updates.** Closures shaped like `v ⊕ k`, with `k` independent of `v` and `⊕` one of `+`, `-`, `min`, `max` or a boolean and/or (field-update lists included), take the cell lock briefly instead of rerunning (§9.4). A hardware add is not used, because overflow traps depend on order and readers need the version to move. `k = 0` writes nothing.
- **ext.** A fiber-aware lock: a waiting fiber suspends without blocking its thread, and the closure runs exactly once (§9.6).

## 10 Boundary between generated code and the runtime

- **Calls.** Crag-to-Crag calls use Cranelift's tail calling convention (§5.6.3). Every Crag function receives an implicit task-context pointer holding the stack limit, the side-stack pointer, the worker, the allocator's free lists, fuel and memory budget for metered code, and the task's flags. Development images call between modules through the slot table; release builds call directly.
- **One check.** Each prologue compares the stack pointer with the stack limit and on failure calls `rt_morestack` on the system stack; loop back-edges load and compare the same limit. To pause or cancel a task (debugger, preemption, hot reload, cancellation), the runtime sets the limit to a sentinel, so the next check calls the runtime. Cancellation is deferred inside atomic blocks, update and `ext` closures, foreign calls, and drop or dispose handlers (§10.4). Counted loops may check every N iterations. Metered code also decrements fuel at the same points and traps when it runs out.
- **Inline fast paths.** Allocation pops the worker's size-class free list and calls `rt_alloc_slow` on a miss. Reference counts are atomic increments and decrements, skipped for static values; reaching zero calls `rt_release(ptr, type)`, which runs `Immediate` drop glue at once and queues other values for deferred teardown (§13.5). Overflow and other checks branch to a cold `rt_trap(kind)` that never returns.
- **Fiber-switching calls.** `put`, `next`, `sleep`, I/O, waits on a `Lazy`, `ext` locks, and starting and joining tasks switch to the system stack first. Cancellation arrives as a return status; the generated code then unwinds, running `Immediate` drops and disposing stream ends so the other side reads `Abandoned`.
- **No callbacks.** Map operations are generated, monomorphized code, so hash and equality inline and the runtime supplies only node memory. Deferred teardown runs on a runtime-owned fiber calling Crag drop glue. A foreign callback runs on a fixed stack; if it suspends, the worker blocks and hands its other fibers to another thread (Ch. 16).
- **Tables.** Per code object: a safepoint table (per offset, the live owned values with type IDs, the source position and the inline chain), used by the unwinder, the debugger and the live-root check of hot reload; a handler table for trap handlers and cancellation cleanup; frame layout and line table; type descriptors, drop and dispose glue, codec glue and slot indices. In the baseline tier, locals stay in stack slots at statement boundaries, so every variable is readable.
- **Debugger.** Breakpoints patch a trap instruction at statement starts from the line table, so they hit in frames already running. Pausing uses the sentinel. An optimized function with a breakpoint returns to baseline through its slot (§20.3).

## 11 Value representation

Every Crag type occupies zero, one or two machine words, so a parameter or result is never more than two registers and the Cranelift lowering stays simple. Every value still has its complete runtime type (§3.6.2).

- **Zero words.** Unit `()` and tag types such as `True`, `Empty[Int]` or `NotFound`; a tag's identity is its type.
- **One word, immediate.** `Int`, the sized integers, `Float`, `CodePoint`, `Fixed[S]` as an `i64` scaled by 10^S (about ±9.2·10^14 at S = 4), and arena handles (32-bit index, 32-bit generation).
- **One word, box pointer.** Records, collections, grids, lazy cells and runtime objects (refs, `ext`, stream ends, hubs, groups).
- **Two words.** Unions: a type index plus a payload (an immediate, a box pointer, or nothing for tags). `Str` and `Bytes`: up to 15 bytes inline, otherwise a buffer pointer with offset and length, which is how slices share storage (§12.4). Closures: a code pointer plus an environment pointer, null for plain functions.

### 11.1 Records

- Records are immutable and boxed. A box has a 16-byte header: an atomic count with flag bits (static, side-stack) and a 32-bit type index.
- A type that spreads a parent lays out the parent's fields first, at the same offsets, so a `NotFound` pointer works wherever a `LookupError` is expected and its header keeps it matchable (§3.6.1).
- After the parent prefix, own fields are ordered by alignment, then by name, so the layout never depends on source order (§3.4).
- Open records (`..`) are monomorphized like generics, so every field access has a fixed offset.
- Optimizations stay out of the semantics: records that do not escape live on the side stack with the static flag set, and MIR may split small non-escaping records into registers.

### 11.2 Type identity

- A type index is a 32-bit index into the image's descriptor table. Indices are global within the image, so widening a value from `A | B` to `A | B | C` needs no retagging.
- Each descriptor carries a 128-bit hash of the canonical type. Transport and hot reload compare hashes, never indices.
- A descriptor holds size, field names and offsets, the parent, drop and dispose glue, the `Immediate`, `Secret` and `Solid` flags, and element types.

### 11.3 Collections, strings and the codec

- A collection is one pointer to a runtime root node; empty collections are shared static singletons. `List[UInt8]` and the other sized-integer lists use packed leaves (§3.1.3).
- In-place updates check for a count of one at run time, as in Perceus, unless the compiler already proved the value unique.
- The codec writes `Float` NaNs in canonical form and map keys in sorted order, so equal values encode and hash equally.

## 12 Known risks

- Salsa's API churn: pinned version, thin facade.
- Release performance stays at Cranelift's level, with MIR optimization carrying the weight.
- Stack-copy bugs: CI runs fibers with tiny initial stacks so every call forces growth.
- A JIT inside release binaries that receive code: macOS needs an entitlement; iOS rules it out.
- Reproducible linking with lld needs a deterministic symbol order, verified in CI.
- The TL2 global version clock can become a point of contention on many cores; it stays behind the runtime ABI so it can be replaced.
