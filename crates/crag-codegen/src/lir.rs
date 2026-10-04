//! The lowered IR the facade accepts: the M0 subset.
//!
//! A function is a list of blocks over virtual registers. Registers are not
//! in SSA form: any block may assign any register, and the facade builds SSA.
//! Every register holds one machine word.

use crag_abi::FuncId;

/// A virtual register. Registers `0..params` hold the parameters on entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

/// Index into `LirFunction::blocks`. Block 0 is where execution starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

/// Wrapping 64-bit arithmetic. Overflow checks are explicit operations in
/// MIR and arrive here as compares and branches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
}

/// Signed 64-bit comparisons.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cond {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug)]
pub enum Inst {
    Const {
        dst: VReg,
        value: i64,
    },
    Bin {
        op: BinOp,
        dst: VReg,
        a: VReg,
        b: VReg,
    },
    /// `dst` becomes 1 if the comparison holds, else 0.
    Cmp {
        cond: Cond,
        dst: VReg,
        a: VReg,
        b: VReg,
    },
    /// A normal call. `dsts` receive the results, at most two.
    Call {
        func: FuncId,
        args: Vec<VReg>,
        dsts: Vec<VReg>,
    },
    /// Reads the word at `addr + offset`.
    Load {
        dst: VReg,
        addr: VReg,
        offset: i32,
    },
    /// Writes `src` to the word at `addr + offset`.
    Store {
        src: VReg,
        addr: VReg,
        offset: i32,
    },
    /// Allocates `size` bytes on the side stack and puts their address in
    /// `dst`. The address stays valid when the machine stack moves. The
    /// function frees everything it pushed when it returns or tail-calls, so
    /// the address must not be passed to a tail call or returned.
    SidePush {
        dst: VReg,
        size: u32,
        align: u32,
    },
    /// The stack check without a frame: a point where the runtime may stop
    /// the fiber. Producers place one on every loop back-edge.
    Poll,
}

#[derive(Clone, Debug)]
pub enum Term {
    Jump(BlockId),
    /// Goes to `then` if `cond` is not zero.
    Branch {
        cond: VReg,
        then: BlockId,
        otherwise: BlockId,
    },
    Return(Vec<VReg>),
    /// A guaranteed tail call: the callee replaces this frame. The callee
    /// must return as many values as this function.
    TailCall {
        func: FuncId,
        args: Vec<VReg>,
    },
}

#[derive(Clone, Debug)]
pub struct Block {
    pub insts: Vec<Inst>,
    pub term: Term,
}

#[derive(Clone, Debug)]
pub struct LirFunction {
    /// Number of parameters, not counting the implicit task context.
    pub params: u32,
    /// Number of results, at most two (Compiler Architecture §11).
    pub returns: u32,
    /// Number of virtual registers, parameters included.
    pub vregs: u32,
    /// Registers holding owned values the runtime must be able to find while
    /// the function is suspended at a call: the unwinder drops them, the
    /// debugger shows them, hot reload checks them (Compiler Architecture
    /// §10). At every call the live ones are in stack slots listed in the
    /// code object's stack maps.
    pub tracked: Vec<VReg>,
    pub blocks: Vec<Block>,
}

impl LirFunction {
    /// Checks the structural rules the lowering relies on.
    pub(crate) fn validate(&self) -> Result<(), String> {
        if self.returns > 2 {
            return Err(format!(
                "{} results, at most 2 fit in registers",
                self.returns
            ));
        }
        if self.params > self.vregs {
            return Err("fewer registers than parameters".into());
        }
        if self.blocks.is_empty() {
            return Err("no blocks".into());
        }
        let reg = |r: &VReg| {
            if r.0 < self.vregs {
                Ok(())
            } else {
                Err(format!("register {} out of range", r.0))
            }
        };
        let block = |b: &BlockId| {
            if (b.0 as usize) < self.blocks.len() {
                Ok(())
            } else {
                Err(format!("block {} out of range", b.0))
            }
        };
        self.tracked.iter().try_for_each(reg)?;
        for b in &self.blocks {
            for inst in &b.insts {
                match inst {
                    Inst::Const { dst, .. } => reg(dst)?,
                    Inst::Bin { dst, a, b, .. } | Inst::Cmp { dst, a, b, .. } => {
                        reg(dst)?;
                        reg(a)?;
                        reg(b)?;
                    }
                    Inst::Call { args, dsts, .. } => {
                        if dsts.len() > 2 {
                            return Err("a call with more than 2 results".into());
                        }
                        args.iter().chain(dsts).try_for_each(reg)?;
                    }
                    Inst::Load { dst, addr, .. } => {
                        reg(dst)?;
                        reg(addr)?;
                    }
                    Inst::Store { src, addr, .. } => {
                        reg(src)?;
                        reg(addr)?;
                    }
                    Inst::SidePush { dst, align, .. } => {
                        reg(dst)?;
                        if !align.is_power_of_two() || *align > 4096 {
                            return Err(format!("side-stack alignment {align}"));
                        }
                    }
                    Inst::Poll => {}
                }
            }
            match &b.term {
                Term::Jump(target) => block(target)?,
                Term::Branch {
                    cond,
                    then,
                    otherwise,
                } => {
                    reg(cond)?;
                    block(then)?;
                    block(otherwise)?;
                }
                Term::Return(values) => {
                    if values.len() != self.returns as usize {
                        return Err(format!(
                            "return of {} values in a function with {} results",
                            values.len(),
                            self.returns
                        ));
                    }
                    values.iter().try_for_each(reg)?;
                }
                Term::TailCall { args, .. } => args.iter().try_for_each(reg)?,
            }
        }
        Ok(())
    }

    /// Whether the function allocates on the side stack.
    pub(crate) fn uses_side_stack(&self) -> bool {
        self.blocks
            .iter()
            .flat_map(|b| &b.insts)
            .any(|i| matches!(i, Inst::SidePush { .. }))
    }

    /// The most arguments any tail call passes, if there is one.
    pub(crate) fn max_tail_call_args(&self) -> Option<u32> {
        self.blocks
            .iter()
            .filter_map(|b| match &b.term {
                Term::TailCall { args, .. } => Some(args.len() as u32),
                _ => None,
            })
            .max()
    }
}
