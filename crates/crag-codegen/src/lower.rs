//! Lowering from LIR to machine code through Cranelift. Cranelift types stay
//! inside this module.

use std::collections::HashMap;

use crag_abi::{FRAME_BUDGET, RuntimeFn, SIDE_END_OFFSET, SIDE_PTR_OFFSET, STACK_LIMIT_OFFSET};
use cranelift_codegen::binemit::Reloc as ClifReloc;
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::I64;
use cranelift_codegen::ir::{
    AbiParam, ExtFuncData, ExternalName, FuncRef, Function, InstBuilder, MemFlagsData, Signature,
    UserExternalName, UserFuncName, Value,
};
use cranelift_codegen::isa::{self, CallConv, OwnedTargetIsa, TargetIsa};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::{Context, FinalizedRelocTarget};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};

use crate::lir::{BinOp, Cond, Inst, LirFunction, Term};
use crate::{
    CodeObject, CodegenError, CodegenSettings, FuncId, OptLevel, Reloc, RelocKind, RelocTarget,
    StackCheck, StackMap,
};

/// Namespaces of the external names the lowering declares. A relocation's
/// target is recovered from the namespace and index.
const NS_FUNCTION: u32 = 0;
const NS_RUNTIME: u32 = 1;
const NS_LOCAL: u32 = 2;

/// A machine the facade can generate code for.
#[derive(Clone)]
pub struct Target {
    baseline: OwnedTargetIsa,
    speed: OwnedTargetIsa,
}

impl Target {
    fn isa(&self, opt: OptLevel) -> &dyn TargetIsa {
        match opt {
            OptLevel::None => &*self.baseline,
            OptLevel::Speed => &*self.speed,
        }
    }
}

#[derive(Debug)]
pub struct UnknownTarget(pub String);

impl std::fmt::Display for UnknownTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unknown target: {}", self.0)
    }
}

impl std::error::Error for UnknownTarget {}

/// Picks the instruction set and settings for a target triple such as
/// `x86_64-unknown-linux-gnu`.
pub fn target_for(triple: &str) -> Result<Target, UnknownTarget> {
    Ok(Target {
        baseline: build_isa(triple, "none")?,
        speed: build_isa(triple, "speed")?,
    })
}

fn build_isa(triple: &str, opt_level: &str) -> Result<OwnedTargetIsa, UnknownTarget> {
    let unknown = |why: String| UnknownTarget(format!("{triple}: {why}"));
    let mut flags = settings::builder();
    for (name, value) in [
        ("opt_level", opt_level),
        // The runtime walks and rewrites the frame-pointer chain when it
        // copies a stack, and tail calls require frame pointers.
        ("preserve_frame_pointers", "true"),
        // Calls load absolute addresses, so one relocation kind suffices.
        ("is_pic", "false"),
        // Unwinding uses our own tables, not the platform's.
        ("unwind_info", "false"),
    ] {
        flags.set(name, value).map_err(|e| unknown(e.to_string()))?;
    }
    let parsed: target_lexicon::Triple = triple.parse().map_err(|e| unknown(format!("{e}")))?;
    let isa = isa::lookup(parsed)
        .map_err(|e| unknown(e.to_string()))?
        .finish(settings::Flags::new(flags))
        .map_err(|e| unknown(e.to_string()))?;
    if isa.pointer_bytes() != 8 {
        return Err(unknown("only 64-bit targets are supported".into()));
    }
    Ok(isa)
}

/// Compiles one function. The result starts with a stack check: the margin
/// check when the frame fits the budget, otherwise a wrapper with the sized
/// check that tail-calls the body.
pub fn compile(lir: &LirFunction, settings: &CodegenSettings) -> Result<CodeObject, CodegenError> {
    lir.validate().map_err(CodegenError::InvalidLir)?;
    let isa = settings.target.isa(settings.opt);

    let body = run_backend(isa, build_body(lir, isa))?;
    let footprint = body.footprint(isa, tail_args_growth(lir));
    if footprint <= FRAME_BUDGET {
        return Ok(CodeObject {
            code: body.code,
            align: body.align,
            entry: 0,
            relocs: body.relocs,
            footprint,
            stack_check: StackCheck::Margin,
            stack_maps: body.stack_maps,
        });
    }

    // The frame is too large to allocate unchecked. Put a wrapper in front
    // that checks for the whole footprint and then tail-calls the body. The
    // body keeps its own margin check: by then it always fits, and it still
    // serves as a stop point.
    let wrapper = run_backend(isa, build_wrapper(lir, isa, footprint))?;
    let wrapper_footprint = wrapper.footprint(isa, 0);
    if wrapper_footprint > FRAME_BUDGET {
        return Err(CodegenError::FrameTooLarge {
            footprint: wrapper_footprint,
            budget: FRAME_BUDGET,
        });
    }

    let align = wrapper.align.max(body.align).max(1);
    let mut code = wrapper.code;
    code.resize(code.len().next_multiple_of(align as usize), 0);
    let body_offset = code.len() as u32;
    code.extend_from_slice(&body.code);

    let mut relocs = wrapper.relocs;
    for reloc in &mut relocs {
        if reloc.target == RelocTarget::Local(0) {
            reloc.target = RelocTarget::Local(body_offset);
        }
    }
    relocs.extend(body.relocs.into_iter().map(|r| Reloc {
        offset: r.offset + body_offset,
        ..r
    }));

    let mut stack_maps = wrapper.stack_maps;
    stack_maps.extend(body.stack_maps.into_iter().map(|m| StackMap {
        return_offset: m.return_offset + body_offset,
        ..m
    }));

    Ok(CodeObject {
        code,
        align,
        entry: 0,
        relocs,
        footprint,
        stack_check: StackCheck::Sized { needed: footprint },
        stack_maps,
    })
}

/// Compiles the stub through which Rust enters Crag code:
///
/// ```text
/// extern "C" fn(ctx: *mut TaskContext, target: *const u8,
///               args: *const u64, results: *mut u64)
/// ```
///
/// It loads `params` words from `args`, calls `target` with the Crag calling
/// convention and stores `returns` words to `results`. It has no stack check,
/// so the caller must provide `STACK_MARGIN` bytes of stack.
pub fn compile_entry_stub(
    params: u32,
    returns: u32,
    settings: &CodegenSettings,
) -> Result<CodeObject, CodegenError> {
    if returns > 2 {
        return Err(CodegenError::InvalidLir(format!(
            "{returns} results, at most 2 fit in registers"
        )));
    }
    let isa = settings.target.isa(settings.opt);

    let mut sig = Signature::new(isa.default_call_conv());
    sig.params.extend([AbiParam::new(I64); 4]);
    let mut func = Function::with_name_signature(UserFuncName::default(), sig);
    let mut fb_ctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut func, &mut fb_ctx);

    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let (ctx, target, args_ptr, results_ptr) = match *b.block_params(entry) {
        [ctx, target, args, results] => (ctx, target, args, results),
        _ => unreachable!("the stub has four parameters"),
    };
    let mut args = vec![ctx];
    for i in 0..params {
        args.push(
            b.ins()
                .load(I64, MemFlagsData::trusted(), args_ptr, (i * 8) as i32),
        );
    }
    let callee_sig = b.import_signature(crag_signature(params, returns));
    let call = b.ins().call_indirect(callee_sig, target, &args);
    let results = b.inst_results(call).to_vec();
    for (i, value) in results.into_iter().enumerate() {
        b.ins()
            .store(MemFlagsData::trusted(), value, results_ptr, (i * 8) as i32);
    }
    b.ins().return_(&[]);
    b.seal_all_blocks();
    b.finalize(isa.frontend_config());

    let stub = run_backend(isa, func)?;
    let footprint = stub.footprint(isa, 0);
    Ok(CodeObject {
        code: stub.code,
        align: stub.align,
        entry: 0,
        relocs: stub.relocs,
        footprint,
        stack_check: StackCheck::None,
        stack_maps: stub.stack_maps,
    })
}

/// The signature of every Crag function: the task context, then the
/// parameters, with Cranelift's tail calling convention.
fn crag_signature(params: u32, returns: u32) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.extend((0..=params).map(|_| AbiParam::new(I64)));
    sig.returns.extend((0..returns).map(|_| AbiParam::new(I64)));
    sig
}

/// Upper bound on how far tail calls move this function's frame down. A tail
/// call with more stack-passed arguments than the function received makes
/// the prologue enlarge the incoming argument area. Cranelift does not report
/// that size, so assume every argument of the largest tail call is passed on
/// the stack.
fn tail_args_growth(lir: &LirFunction) -> u32 {
    match lir.max_tail_call_args() {
        Some(args) if args > lir.params => ((args + 1) * 8).next_multiple_of(16),
        _ => 0,
    }
}

/// Imported functions of the function being built, declared once each.
#[derive(Default)]
struct Imports {
    functions: HashMap<(u32, u32, u32, u32), FuncRef>,
}

impl Imports {
    fn get(
        &mut self,
        b: &mut FunctionBuilder,
        (namespace, index): (u32, u32),
        sig: Signature,
    ) -> FuncRef {
        let key = (
            namespace,
            index,
            sig.params.len() as u32,
            sig.returns.len() as u32,
        );
        *self.functions.entry(key).or_insert_with(|| {
            let name = b
                .func
                .declare_imported_user_function(UserExternalName { namespace, index });
            let signature = b.import_signature(sig);
            b.import_function(ExtFuncData {
                name: ExternalName::user(name),
                signature,
                // Not colocated: the call loads an absolute address, so the
                // loader may place code objects anywhere.
                colocated: false,
                patchable: false,
            })
        })
    }

    fn crag(
        &mut self,
        b: &mut FunctionBuilder,
        func: FuncId,
        params: u32,
        returns: u32,
    ) -> FuncRef {
        self.get(b, (NS_FUNCTION, func.0), crag_signature(params, returns))
    }

    /// `rt_morestack` preserves every register, so the call on the cold path
    /// costs the fast path nothing: no value has to move to a callee-saved
    /// register or a stack slot because of it.
    fn morestack(&mut self, b: &mut FunctionBuilder) -> FuncRef {
        let mut sig = Signature::new(CallConv::PreserveAll);
        sig.params.extend([AbiParam::new(I64); 2]);
        self.get(b, (NS_RUNTIME, RuntimeFn::Morestack as u32), sig)
    }

    /// `rt_side_grow` has the same convention, for the same reason.
    fn side_grow(&mut self, b: &mut FunctionBuilder) -> FuncRef {
        let mut sig = Signature::new(CallConv::PreserveAll);
        sig.params.extend([AbiParam::new(I64); 3]);
        self.get(b, (NS_RUNTIME, RuntimeFn::SideGrow as u32), sig)
    }
}

/// Emits the stack check at the current position and leaves the builder in
/// the block that follows it.
///
/// With `needed == 0` this is the margin check, `sp < limit`, for a frame
/// that already exists. Otherwise it is the sized check, `sp - needed <
/// limit`, for a frame about to be allocated. Both compare unsigned, so the
/// sentinel fails them.
///
/// The limit is loaded on every execution and never cached in a register
/// across checks: another thread stores the sentinel into it.
fn emit_stack_check(b: &mut FunctionBuilder, imports: &mut Imports, ctx: Value, needed: u32) {
    let limit = b
        .ins()
        .load(I64, MemFlagsData::trusted(), ctx, STACK_LIMIT_OFFSET);
    let sp = b.ins().get_stack_pointer(I64);
    let lowest = if needed == 0 {
        sp
    } else {
        b.ins().iadd_imm_s(sp, -i64::from(needed))
    };
    let too_low = b.ins().icmp(IntCC::UnsignedLessThan, lowest, limit);

    let slow = b.create_block();
    let done = b.create_block();
    b.set_cold_block(slow);
    b.ins().brif(too_low, slow, &[], done, &[]);

    b.switch_to_block(slow);
    let morestack = imports.morestack(b);
    let needed = b.ins().iconst(I64, i64::from(needed));
    b.ins().call(morestack, &[ctx, needed]);
    b.ins().jump(done, &[]);

    b.switch_to_block(done);
}

/// Emits a side-stack push at the current position, leaves the builder in
/// the block that follows it and returns the address of the new bytes.
///
/// The bump pointer and the chunk end are read from the task context. If the
/// bytes do not fit, the runtime switches the context to a chunk where they
/// do and the push is repeated, so the call needs no result.
fn emit_side_push(
    b: &mut FunctionBuilder,
    imports: &mut Imports,
    ctx: Value,
    size: u32,
    align: u32,
) -> Value {
    let attempt = b.create_block();
    let grow = b.create_block();
    let done = b.create_block();
    b.set_cold_block(grow);
    b.ins().jump(attempt, &[]);

    b.switch_to_block(attempt);
    let ptr = b
        .ins()
        .load(I64, MemFlagsData::trusted(), ctx, SIDE_PTR_OFFSET);
    let end = b
        .ins()
        .load(I64, MemFlagsData::trusted(), ctx, SIDE_END_OFFSET);
    let start = if align > 1 {
        let bumped = b.ins().iadd_imm_s(ptr, i64::from(align) - 1);
        b.ins().band_imm_s(bumped, -i64::from(align))
    } else {
        ptr
    };
    let new_ptr = b.ins().iadd_imm_s(start, i64::from(size));
    let too_far = b.ins().icmp(IntCC::UnsignedGreaterThan, new_ptr, end);
    b.ins().brif(too_far, grow, &[], done, &[]);

    b.switch_to_block(grow);
    let side_grow = imports.side_grow(b);
    let size = b.ins().iconst(I64, i64::from(size));
    let align = b.ins().iconst(I64, i64::from(align));
    b.ins().call(side_grow, &[ctx, size, align]);
    b.ins().jump(attempt, &[]);

    b.switch_to_block(done);
    b.ins()
        .store(MemFlagsData::trusted(), new_ptr, ctx, SIDE_PTR_OFFSET);
    start
}

fn build_body(lir: &LirFunction, isa: &dyn TargetIsa) -> Function {
    let sig = crag_signature(lir.params, lir.returns);
    let mut func = Function::with_name_signature(UserFuncName::default(), sig);
    let mut fb_ctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut func, &mut fb_ctx);
    let mut imports = Imports::default();

    // A separate entry block, because LIR block 0 may be a loop header and
    // Cranelift's entry block cannot be a branch target.
    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let ctx = b.block_params(entry)[0];
    let vars: Vec<Variable> = (0..lir.vregs).map(|_| b.declare_var(I64)).collect();
    // Before any definition: Cranelift then keeps these values in stack
    // slots across every call and reports the slots in stack maps.
    for reg in &lir.tracked {
        b.declare_var_needs_stack_map(vars[reg.0 as usize]);
    }
    for (i, &var) in vars.iter().enumerate().take(lir.params as usize) {
        let param = b.block_params(entry)[i + 1];
        b.def_var(var, param);
    }

    emit_stack_check(&mut b, &mut imports, ctx, 0);

    // The side-stack mark: both fields as they were on entry. Storing them
    // back frees what this function pushed, whichever chunk it ended up in.
    let side_mark = lir.uses_side_stack().then(|| {
        let ptr = b
            .ins()
            .load(I64, MemFlagsData::trusted(), ctx, SIDE_PTR_OFFSET);
        let end = b
            .ins()
            .load(I64, MemFlagsData::trusted(), ctx, SIDE_END_OFFSET);
        (ptr, end)
    });
    let side_pop = |b: &mut FunctionBuilder| {
        if let Some((ptr, end)) = side_mark {
            b.ins()
                .store(MemFlagsData::trusted(), ptr, ctx, SIDE_PTR_OFFSET);
            b.ins()
                .store(MemFlagsData::trusted(), end, ctx, SIDE_END_OFFSET);
        }
    };

    let blocks: Vec<_> = lir.blocks.iter().map(|_| b.create_block()).collect();
    b.ins().jump(blocks[0], &[]);

    for (block, &clif_block) in lir.blocks.iter().zip(&blocks) {
        b.switch_to_block(clif_block);
        for inst in &block.insts {
            match inst {
                Inst::Const { dst, value } => {
                    let v = b.ins().iconst(I64, *value);
                    b.def_var(vars[dst.0 as usize], v);
                }
                Inst::Bin { op, dst, a, b: rhs } => {
                    let x = b.use_var(vars[a.0 as usize]);
                    let y = b.use_var(vars[rhs.0 as usize]);
                    let v = match op {
                        BinOp::Add => b.ins().iadd(x, y),
                        BinOp::Sub => b.ins().isub(x, y),
                        BinOp::Mul => b.ins().imul(x, y),
                    };
                    b.def_var(vars[dst.0 as usize], v);
                }
                Inst::Cmp {
                    cond,
                    dst,
                    a,
                    b: rhs,
                } => {
                    let x = b.use_var(vars[a.0 as usize]);
                    let y = b.use_var(vars[rhs.0 as usize]);
                    let cc = match cond {
                        Cond::Eq => IntCC::Equal,
                        Cond::Ne => IntCC::NotEqual,
                        Cond::Lt => IntCC::SignedLessThan,
                        Cond::Le => IntCC::SignedLessThanOrEqual,
                        Cond::Gt => IntCC::SignedGreaterThan,
                        Cond::Ge => IntCC::SignedGreaterThanOrEqual,
                    };
                    let flag = b.ins().icmp(cc, x, y);
                    let v = b.ins().uextend(I64, flag);
                    b.def_var(vars[dst.0 as usize], v);
                }
                Inst::Call { func, args, dsts } => {
                    let callee = imports.crag(&mut b, *func, args.len() as u32, dsts.len() as u32);
                    let mut values = vec![ctx];
                    values.extend(args.iter().map(|r| b.use_var(vars[r.0 as usize])));
                    let call = b.ins().call(callee, &values);
                    let results = b.inst_results(call).to_vec();
                    for (dst, v) in dsts.iter().zip(results) {
                        b.def_var(vars[dst.0 as usize], v);
                    }
                }
                Inst::Load { dst, addr, offset } => {
                    let p = b.use_var(vars[addr.0 as usize]);
                    let v = b.ins().load(I64, MemFlagsData::trusted(), p, *offset);
                    b.def_var(vars[dst.0 as usize], v);
                }
                Inst::Store { src, addr, offset } => {
                    let p = b.use_var(vars[addr.0 as usize]);
                    let v = b.use_var(vars[src.0 as usize]);
                    b.ins().store(MemFlagsData::trusted(), v, p, *offset);
                }
                Inst::SidePush { dst, size, align } => {
                    let p = emit_side_push(&mut b, &mut imports, ctx, *size, *align);
                    b.def_var(vars[dst.0 as usize], p);
                }
                Inst::Poll => emit_stack_check(&mut b, &mut imports, ctx, 0),
            }
        }
        match &block.term {
            Term::Jump(target) => {
                b.ins().jump(blocks[target.0 as usize], &[]);
            }
            Term::Branch {
                cond,
                then,
                otherwise,
            } => {
                let c = b.use_var(vars[cond.0 as usize]);
                b.ins().brif(
                    c,
                    blocks[then.0 as usize],
                    &[],
                    blocks[otherwise.0 as usize],
                    &[],
                );
            }
            Term::Return(values) => {
                let values: Vec<_> = values
                    .iter()
                    .map(|r| b.use_var(vars[r.0 as usize]))
                    .collect();
                side_pop(&mut b);
                b.ins().return_(&values);
            }
            Term::TailCall { func, args } => {
                let callee = imports.crag(&mut b, *func, args.len() as u32, lir.returns);
                let mut values = vec![ctx];
                values.extend(args.iter().map(|r| b.use_var(vars[r.0 as usize])));
                side_pop(&mut b);
                b.ins().return_call(callee, &values);
            }
        }
    }

    b.seal_all_blocks();
    b.finalize(isa.frontend_config());
    func
}

/// The wrapper for a function whose frame exceeds the budget: the sized
/// check, then a tail call to the body, which follows in the same code
/// object.
fn build_wrapper(lir: &LirFunction, isa: &dyn TargetIsa, needed: u32) -> Function {
    let sig = crag_signature(lir.params, lir.returns);
    let mut func = Function::with_name_signature(UserFuncName::default(), sig.clone());
    let mut fb_ctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut func, &mut fb_ctx);
    let mut imports = Imports::default();

    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let args = b.block_params(entry).to_vec();
    // The wrapper holds the parameters while its check may enter the runtime.
    for reg in lir.tracked.iter().filter(|reg| reg.0 < lir.params) {
        b.declare_value_needs_stack_map(args[1 + reg.0 as usize]);
    }

    emit_stack_check(&mut b, &mut imports, args[0], needed);

    // `Local(0)` stands for the body; `compile` fills in its offset.
    let body = imports.get(&mut b, (NS_LOCAL, 0), sig);
    b.ins().return_call(body, &args);

    b.seal_all_blocks();
    b.finalize(isa.frontend_config());
    func
}

/// What the backend produced for one Cranelift function.
struct Compiled {
    code: Vec<u8>,
    align: u32,
    relocs: Vec<Reloc>,
    stack_maps: Vec<StackMap>,
    /// Distance from the frame pointer down to the stack pointer.
    frame_below_fp: u32,
}

impl Compiled {
    /// See `CodeObject::footprint`.
    fn footprint(&self, isa: &dyn TargetIsa, tail_args_growth: u32) -> u32 {
        // Return address and saved frame pointer, then the frame.
        2 * u32::from(isa.pointer_bytes()) + self.frame_below_fp + tail_args_growth
    }
}

fn run_backend(isa: &dyn TargetIsa, func: Function) -> Result<Compiled, CodegenError> {
    let mut ctx = Context::for_function(func);
    ctx.compile(isa, &mut ControlPlane::default())
        .map_err(|e| CodegenError::Backend(format!("{:?}", e.inner)))?;
    let compiled = ctx.compiled_code().expect("compile succeeded");
    let buffer = &compiled.buffer;
    let names = ctx.func.params.user_named_funcs();

    let mut relocs = Vec::new();
    for reloc in buffer.relocs() {
        let unsupported = || CodegenError::UnsupportedRelocation(format!("{reloc:?}"));
        if reloc.kind != ClifReloc::Abs8 {
            return Err(unsupported());
        }
        let FinalizedRelocTarget::ExternalName(ExternalName::User(name)) = &reloc.target else {
            return Err(unsupported());
        };
        let name = &names[*name];
        let target = match name.namespace {
            NS_FUNCTION => RelocTarget::Function(FuncId(name.index)),
            NS_RUNTIME => {
                RelocTarget::Runtime(RuntimeFn::from_index(name.index).ok_or_else(unsupported)?)
            }
            NS_LOCAL => RelocTarget::Local(name.index),
            _ => return Err(unsupported()),
        };
        relocs.push(Reloc {
            offset: reloc.offset,
            kind: RelocKind::Abs64,
            target,
            addend: reloc.addend,
        });
    }

    let mut stack_maps: Vec<StackMap> = buffer
        .user_stack_maps()
        .iter()
        .map(|(return_offset, _, map)| StackMap {
            return_offset: *return_offset,
            slots: map.entries().map(|(_, offset)| offset).collect(),
        })
        .collect();
    stack_maps.sort_by_key(|m| m.return_offset);

    let frame = buffer
        .frame_layout()
        .ok_or_else(|| CodegenError::Backend("the backend reported no frame layout".into()))?;
    Ok(Compiled {
        code: buffer.data().to_vec(),
        align: buffer.alignment,
        relocs,
        stack_maps,
        frame_below_fp: frame.frame_to_fp_offset,
    })
}
