use llvm_ir::instruction::Instruction;
use llvm_ir::{Constant, Function, Name, Operand, Terminator};
use petgraph::prelude::{DiGraphMap, Direction};
use std::collections::HashMap;
use std::fmt;

use std::error::Error;
use std::fs::File;
use std::io::Write;

/// The control flow graph for a particular function.
///
/// To construct a `ControlFlowGraph`, use
/// [`FunctionAnalysis`](struct.FunctionAnalysis.html), which you can get
/// from [`ModuleAnalysis`](struct.ModuleAnalysis.html).
pub struct ControlFlowGraph<'m> {
    /// The graph itself. Nodes are basic block names, and an edge from bbX to
    /// bbY indicates that control may (immediately) flow from bbX to bbY
    ///
    /// Or, an edge from bbX to `Return` indicates that the function may return
    /// from bbX
    pub(crate) graph: DiGraphMap<CFGNode<'m>, ()>,

    /// Entry node for the function
    pub(crate) entry_node: CFGNode<'m>,
}

/// A CFGNode represents a basic block, or the special node `Return`
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum CFGNode<'m> {
    /// The block with the given `Name`
    Block(&'m Name),
    /// The special `Return` node indicating function return
    Return,
}

impl<'m> fmt::Display for CFGNode<'m> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CFGNode::Block(block) => write!(f, "{}", block),
            CFGNode::Return => write!(f, "Return"),
        }
    }
}

impl<'m> ControlFlowGraph<'m> {
    pub(crate) fn new(function: &'m Function) -> Self {
        let mut graph: DiGraphMap<CFGNode<'m>, ()> = DiGraphMap::with_capacity(
            function.basic_blocks.len() + 1,
            2 * function.basic_blocks.len(), // arbitrary guess
        );

        for bb in &function.basic_blocks {
            match &bb.term {
                Terminator::Br(br) => {
                    graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Block(&br.dest), ());
                }
                Terminator::CondBr(condbr) => {
                    graph.add_edge(
                        CFGNode::Block(&bb.name),
                        CFGNode::Block(&condbr.true_dest),
                        (),
                    );
                    graph.add_edge(
                        CFGNode::Block(&bb.name),
                        CFGNode::Block(&condbr.false_dest),
                        (),
                    );
                }
                Terminator::IndirectBr(ibr) => {
                    for dest in &ibr.possible_dests {
                        graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Block(dest), ());
                    }
                }
                Terminator::Switch(switch) => {
                    graph.add_edge(
                        CFGNode::Block(&bb.name),
                        CFGNode::Block(&switch.default_dest),
                        (),
                    );
                    for (_, dest) in &switch.dests {
                        graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Block(dest), ());
                    }
                }
                Terminator::Ret(_) | Terminator::Resume(_) => {
                    graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Return, ());
                }
                Terminator::Invoke(invoke) => {
                    graph.add_edge(
                        CFGNode::Block(&bb.name),
                        CFGNode::Block(&invoke.return_label),
                        (),
                    );
                    graph.add_edge(
                        CFGNode::Block(&bb.name),
                        CFGNode::Block(&invoke.exception_label),
                        (),
                    );
                }
                Terminator::CleanupRet(cleanupret) => {
                    if let Some(dest) = &cleanupret.unwind_dest {
                        graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Block(dest), ());
                    } else {
                        graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Return, ());
                    }
                }
                Terminator::CatchRet(catchret) => {
                    // Despite its name, my reading of the LLVM 10 LangRef indicates that CatchRet cannot directly return from the function
                    graph.add_edge(
                        CFGNode::Block(&bb.name),
                        CFGNode::Block(&catchret.successor),
                        (),
                    );
                }
                Terminator::CatchSwitch(catchswitch) => {
                    if let Some(dest) = &catchswitch.default_unwind_dest {
                        graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Block(dest), ());
                    } else {
                        graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Return, ());
                    }
                    for handler in &catchswitch.catch_handlers {
                        graph.add_edge(CFGNode::Block(&bb.name), CFGNode::Block(handler), ());
                    }
                }
                Terminator::CallBr(_) => unimplemented!("CallBr instruction"),
                Terminator::Unreachable(_) => {
                    // no successors
                }
            }
        }

        Self {
            graph,
            entry_node: CFGNode::Block(&function.basic_blocks[0].name),
        }
    }

    /// Build the control flow graph with **coroutine normalization** applied: for an
    /// `async fn` lowered to a state machine, rewire the resume-dispatch so that dominance
    /// reflects source order across `await` points. See [`coroutine_rewiring`]. For a
    /// non-coroutine function this is identical to [`ControlFlowGraph::new`].
    pub(crate) fn new_coroutine_aware(function: &'m Function) -> Self {
        let mut cfg = Self::new(function);
        if let Some(rw) = coroutine_rewiring(function) {
            let entry = cfg.entry_node;
            for (suspend, resume) in rw.rewire {
                // the resume block was reached only from the entry dispatch; move that edge
                // to come from the suspend block, so pre-await code dominates the resume.
                cfg.graph.remove_edge(entry, CFGNode::Block(resume));
                cfg.graph
                    .add_edge(CFGNode::Block(suspend), CFGNode::Block(resume), ());
            }
        }
        cfg
    }

    /// Get the predecessors of the basic block with the given `Name`
    pub fn preds<'s>(&'s self, block: &'m Name) -> impl Iterator<Item = &'m Name> + 's {
        self.preds_of_cfgnode(CFGNode::Block(block))
    }

    /// Get the predecessors of the special `Return` node, i.e., get all blocks
    /// which may directly return
    pub fn preds_of_return<'s>(&'s self) -> impl Iterator<Item = &'m Name> + 's {
        self.preds_of_cfgnode(CFGNode::Return)
    }

    pub(crate) fn preds_of_cfgnode<'s>(
        &'s self,
        node: CFGNode<'m>,
    ) -> impl Iterator<Item = &'m Name> + 's {
        self.preds_as_nodes(node).map(|cfgnode| match cfgnode {
            CFGNode::Block(block) => block,
            CFGNode::Return => panic!("Shouldn't have CFGNode::Return as a predecessor"), // perhaps you tried to call this on a reversed CFG? In-crate users can use `preds_as_nodes()` if they need to account for the possibility of a reversed CFG
        })
    }

    pub(crate) fn preds_as_nodes<'s>(
        &'s self,
        node: CFGNode<'m>,
    ) -> impl Iterator<Item = CFGNode<'m>> + 's {
        self.graph.neighbors_directed(node, Direction::Incoming)
    }

    /// Get the successors of the basic block with the given `Name`.
    /// Here, `CFGNode::Return` indicates that the function may directly return
    /// from this basic block.
    pub fn succs<'s>(&'s self, block: &'m Name) -> impl Iterator<Item = CFGNode<'m>> + 's {
        self.graph
            .neighbors_directed(CFGNode::Block(block), Direction::Outgoing)
    }

    /// Get the `Name` of the entry block for the function
    pub fn entry(&self) -> &'m Name {
        match self.entry_node {
            CFGNode::Block(block) => block,
            CFGNode::Return => panic!("Return node should not be entry"), // perhaps you tried to call this on a reversed CFG? In-crate users can use the `entry_node` field directly if they need to account for the possibility of a reversed CFG
        }
    }

    /// Get the reversed CFG; i.e., the CFG where all edges have been reversed
    pub(crate) fn reversed(&self) -> Self {
        Self {
            graph: DiGraphMap::from_edges(self.graph.all_edges().map(|(a, b, _)| (b, a, ()))),
            entry_node: CFGNode::Return,
        }
    }

    pub fn print_cfg(&self, func_name: &str, file: &mut File) -> Result<(), Box<dyn Error>> {
        writeln!(file, "Function: {}", func_name)?;
        writeln!(file)?;

        for block in self.graph.nodes() {
            writeln!(file, "  Basic block: {}", block)?;

            writeln!(file, "    Predecessors:")?;
            let preds: Vec<_> = self
                .graph
                .neighbors_directed(block, Direction::Incoming)
                .collect();

            if preds.is_empty() {
                writeln!(file, "      <none>")?;
            } else {
                for pred in preds {
                    writeln!(file, "      {}", pred)?;
                }
            }

            writeln!(file, "    Successors:")?;
            let succs: Vec<_> = self
                .graph
                .neighbors_directed(block, Direction::Outgoing)
                .collect();

            if succs.is_empty() {
                writeln!(file, "      <none>")?;
            } else {
                for succ in succs {
                    writeln!(file, "      {}", succ)?;
                }
            }

            writeln!(file)?;
        }

        writeln!(file, "----------------------------------------")?;
        writeln!(file)?;

        Ok(())
    }
}

/// The CFG rewiring to apply for a coroutine: `(suspend block, resume block)` pairs whose
/// `entry -> resume` edge should become `suspend -> resume`.
pub(crate) struct CoroutineRewiring<'m> {
    pub rewire: Vec<(&'m Name, &'m Name)>,
}

/// Detect the `async fn` state machine and compute the resume-dispatch rewiring, or `None`
/// for a non-coroutine function.
///
/// rustc lowers an `async fn` so that the poll function's entry block loads a state
/// discriminant from a fixed offset in the coroutine frame and `switch`es on it to a resume
/// block per state. Blocks after an `await` are reached only from that dispatch, so a block
/// before the `await` does not dominate them. We recover the logical order: a resume state is
/// one that some block stores into the state field (just before suspending); that storing
/// block is the suspend whose continuation is the resume block. (The start/unresumed state is
/// never stored inside the poll function, so it is left attached to the entry.) Rewiring
/// `entry -> resume` into `suspend -> resume` makes the pre-`await` code dominate the resume.
pub(crate) fn coroutine_rewiring(function: &Function) -> Option<CoroutineRewiring<'_>> {
    let entry = function.basic_blocks.first()?;

    // entry terminator must be a switch (the resume dispatch)
    let Terminator::Switch(sw) = &entry.term else {
        return None;
    };
    let disc = operand_name(&sw.operand)?;

    // map SSA name -> defining instruction within the entry block (to trace the discriminant)
    let entry_defs = block_defs(entry);
    let state_offset = trace_state_offset(&disc, &entry_defs)?;

    // switch cases: state value -> resume block
    let cases: Vec<(u64, &Name)> = sw
        .dests
        .iter()
        .filter_map(|(c, blk)| const_int(c).map(|k| (k, blk)))
        .collect();
    if cases.is_empty() {
        return None;
    }

    // Find, across all blocks, stores of a constant to the state field. The storing block is
    // a suspend; the stored value is the state it resumes into.
    let mut stores_for_state: HashMap<u64, Vec<&Name>> = HashMap::new();
    for bb in &function.basic_blocks {
        let defs = block_defs(bb);
        for inst in &bb.instrs {
            if let Instruction::Store(st) = inst {
                let Some(k) = operand_const_int(&st.value) else { continue };
                let Some(addr) = operand_name(&st.address) else { continue };
                if gep_offset_of(&addr, &defs) == Some(state_offset) {
                    stores_for_state.entry(k).or_default().push(&bb.name);
                }
            }
        }
    }

    // A case is a resume point iff some block stores its state; rewire those.
    let mut rewire = Vec::new();
    for (k, resume) in &cases {
        if let Some(suspends) = stores_for_state.get(k) {
            for sb in suspends {
                rewire.push((*sb, *resume));
            }
        }
    }
    if rewire.is_empty() {
        return None;
    }
    Some(CoroutineRewiring { rewire })
}

/// Map each SSA value defined in a block to its defining instruction.
fn block_defs(bb: &llvm_ir::BasicBlock) -> HashMap<Name, &Instruction> {
    let mut m = HashMap::new();
    for inst in &bb.instrs {
        if let Some(dest) = inst_dest(inst) {
            m.insert(dest.clone(), inst);
        }
    }
    m
}

/// The destination name of an instruction, if it defines one.
fn inst_dest(inst: &Instruction) -> Option<&Name> {
    match inst {
        Instruction::GetElementPtr(g) => Some(&g.dest),
        Instruction::Load(l) => Some(&l.dest),
        Instruction::ZExt(z) => Some(&z.dest),
        Instruction::SExt(s) => Some(&s.dest),
        Instruction::Trunc(t) => Some(&t.dest),
        Instruction::BitCast(b) => Some(&b.dest),
        _ => None,
    }
}

/// Trace the switch discriminant back through casts and a load to the constant byte offset
/// of the state field it is loaded from.
fn trace_state_offset(name: &Name, defs: &HashMap<Name, &Instruction>) -> Option<u64> {
    let mut cur = name.clone();
    // follow casts
    for _ in 0..8 {
        match defs.get(&cur)? {
            Instruction::ZExt(z) => cur = operand_name(&z.operand)?,
            Instruction::SExt(s) => cur = operand_name(&s.operand)?,
            Instruction::Trunc(t) => cur = operand_name(&t.operand)?,
            Instruction::Load(l) => {
                let addr = operand_name(&l.address)?;
                return gep_offset_of(&addr, defs);
            }
            _ => return None,
        }
    }
    None
}

/// If `name` is defined by a `getelementptr i8, ptr, i64 OFF`, return `OFF`.
fn gep_offset_of(name: &Name, defs: &HashMap<Name, &Instruction>) -> Option<u64> {
    match defs.get(name)? {
        Instruction::GetElementPtr(g) => gep_single_const_offset(&g.indices),
        _ => None,
    }
}

/// The single constant index of a byte-offset GEP (the first constant int operand).
fn gep_single_const_offset(indices: &[Operand]) -> Option<u64> {
    for op in indices {
        if let Some(k) = operand_const_int(op) {
            return Some(k);
        }
    }
    None
}

fn operand_name(op: &Operand) -> Option<Name> {
    match op {
        Operand::LocalOperand { name, .. } => Some(name.clone()),
        _ => None,
    }
}

fn operand_const_int(op: &Operand) -> Option<u64> {
    match op {
        Operand::ConstantOperand(c) => const_int(c),
        _ => None,
    }
}

fn const_int(c: &llvm_ir::ConstantRef) -> Option<u64> {
    match c.as_ref() {
        Constant::Int { value, .. } => Some(*value),
        _ => None,
    }
}

#[cfg(test)]
mod coroutine_tests {
    use super::*;
    use crate::DominatorTree;

    fn async_fixture() -> String {
        std::env::var("AFG_ASYNC_LL").unwrap_or_else(|_| {
            format!("{}/tests/fixtures/async_demo_dbg.ll", env!("CARGO_MANIFEST_DIR"))
        })
    }

    #[test]
    fn detects_async_coroutine_and_skips_plain_fn() {
        let path = async_fixture();
        let m = llvm_ir::Module::from_ir_path(&path).expect("parse async fixture");

        // the `guarded` coroutine (async fn body) must be detected as a coroutine
        let guarded = m
            .functions
            .iter()
            .find(|f| f.name.contains("7guarded") && f.name.contains("closure"))
            .expect("guarded coroutine");
        let rw = coroutine_rewiring(guarded).expect("guarded detected as coroutine");
        assert!(!rw.rewire.is_empty(), "expected resume-dispatch rewiring edges");

        // a non-async function (the no-op waker fn) is not a coroutine
        let plain = m
            .functions
            .iter()
            .find(|f| f.name.contains("4noop"))
            .expect("noop fn");
        assert!(
            coroutine_rewiring(plain).is_none(),
            "a non-coroutine function must not be rewired"
        );
    }

    #[test]
    fn rewiring_makes_suspend_dominate_resume() {
        let path = async_fixture();
        let m = llvm_ir::Module::from_ir_path(&path).expect("parse async fixture");
        let guarded = m
            .functions
            .iter()
            .find(|f| f.name.contains("7guarded") && f.name.contains("closure"))
            .expect("guarded coroutine");

        let rw = coroutine_rewiring(guarded).unwrap();
        let plain = DominatorTree::new(&ControlFlowGraph::new(guarded));
        let coro = DominatorTree::new(&ControlFlowGraph::new_coroutine_aware(guarded));
        let entry = &guarded.basic_blocks[0].name;

        // For each rewired (suspend -> resume): in the coroutine CFG the suspend block
        // dominates the resume block (source order restored); in the plain CFG it does not
        // (the resume hung off the entry dispatch instead).
        let mut saw_change = false;
        for (suspend, resume) in &rw.rewire {
            assert!(
                coro.dominates(CFGNode::Block(suspend), CFGNode::Block(resume)),
                "suspend {suspend} should dominate resume {resume} in coroutine CFG"
            );
            if !plain.dominates(CFGNode::Block(suspend), CFGNode::Block(resume))
                && plain.dominates(CFGNode::Block(entry), CFGNode::Block(resume))
            {
                saw_change = true;
            }
        }
        assert!(
            saw_change,
            "coroutine normalization should change dominance for at least one resume block"
        );
    }
}
