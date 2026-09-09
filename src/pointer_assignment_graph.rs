use crate::taint_analysis::SemanticPoint;
use crate::taint_analysis::SemanticPointKind;
use crate::call_graph::CallGraph;
use crate::context::{
    PAConfig, PAContext, PAContextElem, PAContextMode, PAContextSelectPolicy, PAObjectContextKind,
};
use crate::signature::Signature;
use crate::util;
use crate::TaintAnalysis;
use crate::ControlFlowGraph;
use crate::FunctionsByType;
use core::panic;
use llvm_ir::function::Parameter;
use llvm_ir::function::ParameterAttribute;
use llvm_ir::instruction::{InlineAssembly, Instruction};
use llvm_ir::DebugLoc;
use llvm_ir::HasDebugLoc;
use llvm_ir::{Constant, ConstantRef, Function, Module, Name, Operand, Type, TypeRef};
use log::debug;
use rustc_demangle::demangle;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::error::Error;
use std::fs::File;
use std::hash::Hash;
use std::io::Write;
use std::time::Instant;
use std::{format, println};

/// field-sensitive: to avoid circular dependency in gep, where %x = gep(%a, ...), then %a = %x
/// then there will be infinite fieldobject created in this loop
const MAX_FIELD_DEPTH: usize = 2;
const SUMMARY_FIELD: u64 = u64::MAX; // collapse

const BYTE_OFFSET_MARKER: u64 = u64::MAX - 1;
const BYTE_OFFSET_SUMMARY: u64 = u64::MAX - 2;

pub type PANodeId = usize;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PASourceLocation {
    pub file: Option<String>,
    pub directory: Option<String>,
    pub line: Option<u32>,
    pub column: Option<u32>,
}

impl PASourceLocation {
    pub fn unknown() -> Self {
        Self {
            file: None,
            directory: None,
            line: None,
            column: None,
        }
    }

    pub fn display(&self) -> String {
        match (&self.directory, &self.file, self.line, self.column) {
            (Some(dir), Some(file), Some(line), Some(col)) => {
                format!("{}/{}:{}:{}", dir, file, line, col)
            }
            (_, Some(file), Some(line), Some(col)) => {
                format!("{}:{}:{}", file, line, col)
            }
            (_, Some(file), Some(line), None) => {
                format!("{}:{}", file, line)
            }
            _ => "<unknown source location>".to_string(),
        }
    }
}

impl std::fmt::Display for PASourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        return write!(f, "{}", self.display());
    }
}

pub enum PAValueRef<'m> {
    Operand(&'m llvm_ir::Operand),
    Parameter(&'m llvm_ir::function::Parameter),
    Name {
        name: &'m llvm_ir::Name,
        ty: Option<llvm_ir::TypeRef>,
    },
}

#[derive(Debug, Clone)]
pub enum PANodeKind<'m> {
    SSAValue {
        /// exist is if LocalOperand
        function: Option<String>,
        name: &'m llvm_ir::Name,
        ty: Option<llvm_ir::TypeRef>,
    },

    Constant {
        op: &'m llvm_ir::Operand,
    },

    AllocaObject {
        function: String,
        block: String,
        dest: &'m llvm_ir::Name,
        allocated_type: &'m TypeRef,
    },

    FieldObject {
        base: PANodeId,
        field: Vec<u64>,
        field_type: Option<llvm_ir::TypeRef>,
    },

    /// the return value of a function
    FunctionReturn {
        function: String,
    },

    /// the function object itself
    FunctionObject {
        function: String,
    },

    /// the receiver object of a call instruction (e.g., the `self` or `this` pointer)
    ReceiverObject {
        caller: String,
        block: String,
        callsite_id: usize,
        self_idx: usize,
    },

    /// the target of an indirect call instruction (e.g., a function pointer)
    IndirectCallTarget {
        caller: String,
        block: String,
        callsite_id: usize,
    },

    /// a global object (e.g., a global allocation or a global function)
    GlobalObject {
        name: String,
    },

    /// intermediate var
    GlobalAddress {
        name: String,
    },

    /// a global object that is part of a table (e.g., a vtable or a function pointer table)
    TableSlot {
        global: String,
        index: usize,
    },

    /// the value packed into a field of an aggregate SSA value (insertvalue)
    AggregateField {
        origin: PANodeId,
        field: Vec<u64>,
    },

    /// a heap allocation site (modeled heuristically at the allocator callsite)
    HeapObject {
        function: String,
        block: String,
        name: String,
        obj_callsite_id: usize,
        allocated_type: Option<llvm_ir::TypeRef>, // TODO: ??
    },
}

#[derive(Debug, Clone)]
pub struct PANode<'m> {
    pub id: PANodeId,
    pub kind: PANodeKind<'m>,
    /// LLVM type of the value/object represented by this node, if known.
    pub ty: Option<llvm_ir::TypeRef>,
    pub context: PAContext,

    pub points_to: BTreeSet<PANodeId>,
    pub source_loc: Option<PASourceLocation>,
}

impl<'m> PANode<'m> {
    pub fn new(
        id: PANodeId,
        kind: PANodeKind<'m>,
        ty: Option<llvm_ir::TypeRef>,
        context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) -> Self {
        Self {
            id,
            kind,
            ty,
            context,
            points_to: BTreeSet::new(),
            source_loc,
        }
    }

    pub fn key(&self) -> String {
        return format!("{} (ctx::{:?})", self.kind.key(), self.context);
    }

    /// The enclosing function (mangled name) of this node, if it has one.
    pub fn function(&self) -> Option<&str> {
        match &self.kind {
            PANodeKind::SSAValue { function, .. } => function.as_deref(),
            PANodeKind::AllocaObject { function, .. } => Some(function),
            PANodeKind::FunctionReturn { function, .. } => Some(function),
            PANodeKind::FunctionObject { function, .. } => Some(function),
            PANodeKind::ReceiverObject { caller, .. } => Some(caller),
            _ => None,
        }
    }
}

impl<'m> PANodeKind<'m> {
    pub fn key(&self) -> String {
        match self {
            Self::SSAValue { function, name, .. } => {
                return format!(
                    "ssa::{:?}::{}",
                    function.as_deref().unwrap_or("<global>"),
                    name_key(name)
                );
            }

            Self::Constant { op } => return format!("constant::{}", op),

            Self::AllocaObject {
                function,
                block,
                dest,
                allocated_type,
            } => {
                return format!(
                    "alloca_object::{}::{}::{}::{}(type)",
                    function, block, dest, allocated_type
                )
            }

            Self::FieldObject {
                base,
                field,
                field_type,
            } => {
                return format!(
                    "field_object::n{}::{:?}::{:?}(type)",
                    base, field, field_type
                )
            }

            Self::FunctionReturn { function } => return format!("function_return::{}", function),

            Self::FunctionObject { function } => return format!("function_object::{}", function),

            Self::ReceiverObject {
                caller,
                block,
                callsite_id,
                self_idx,
            } => {
                return format!(
                    "receiver_object::{}::{}::{}(cs_id)::{}(self_idx)",
                    caller, block, callsite_id, self_idx
                )
            }

            Self::IndirectCallTarget {
                caller,
                block,
                callsite_id,
            } => {
                return format!(
                    "indirect_call_target::{}::{}::{}(cs_id)",
                    caller, block, callsite_id
                )
            }

            Self::GlobalObject { name } => return format!("global_object::{}", name),

            Self::GlobalAddress { name } => return format!("global_address::{}", name),

            Self::TableSlot { global, index } => {
                return format!("table_slot::{}::{}", global, index)
            }

            Self::AggregateField { origin, field } => {
                return format!("aggregate_field::n{}::{:?}", origin, field)
            }

            Self::HeapObject {
                function,
                block,
                name,
                obj_callsite_id,
                allocated_type,
            } => {
                return format!(
                    "heap_object::{}::{}::{}::{}(cs_id)::{:?}(type)",
                    function, block, name, obj_callsite_id, allocated_type,
                )
            }
        }
    }
}

impl<'m> std::fmt::Display for PANodeKind<'m> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return write!(f, "{}", self.key());
    }
}

impl<'m> std::fmt::Display for PANode<'m> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return write!(f, "n{}:{} (ctx:{:?})", self.id, self.kind, self.context);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PAEdgeKind {
    /// dst = &src
    AddressOf,

    /// dst = src
    Copy,

    /// dst = *src
    Load,

    /// *dst = src
    Store,

    /// dst = src[offset]: getelementptr when src has type
    GEP { indices: Vec<u64> },

    /// GEP when source have no type, e.g., const int
    ByteOffsetGEP { offset: i64 },

    /// GEP when source is value/ref, e.g., %_9
    UnknownOffsetGEP,

    /// dst = bitcast src
    BitCast,

    /// dst = addrspacecast src
    AddrSpaceCast,

    /// dst = inttoptr src
    IntToPtr,

    /// dst = phi(src1, src2, ...)
    Phi,

    /// dst = select(cond, src_true, src_false)
    Select,

    /// dst = call i32 () %ptr( ... ) function pointer %ptr changes the target of the call
    IndirectCall { callsite_id: usize },

    /// dst = call(self, src2, ...) receiver pointer changes the target of the call
    ReceiverCall { callsite_id: usize },

    /// dst = call(self, src2, ...) we know the function name but we have to postpone the solving to obtain objects in pts(self)
    /// self_idx is the argument index for %self, which is the receiver
    DirectCall { callsite_id: usize, self_idx: usize },

    /// for llvm.memcpy(dst_ptr, src_ptr, size)
    /// edge.src = src pointer
    /// edge.dst = dst pointer
    MemCopy,

    /// dst = src, for aggregate SSA values (filtered by nodes_may_carry_pointer)
    AggregateCopy,

    /// dst = extractvalue src, field
    ExtractCopy { field: Vec<u64> },
}

#[derive(Debug, Clone)]
pub struct PAEdge {
    pub src: PANodeId,
    pub dst: PANodeId,
    pub kind: PAEdgeKind,
    pub function: String,
    pub block: String,
}

#[derive(Debug, Clone, Copy)]
pub enum PACallSiteKind<'m> {
    Call(&'m llvm_ir::instruction::Call),
    Invoke(&'m llvm_ir::terminator::Invoke),
}

#[derive(Debug, Clone)]
pub struct PACallSite<'m> {
    pub id: usize,
    pub caller: String,
    pub block: String,
    pub kind: PACallSiteKind<'m>,

    /// exist when callee is syntactically know, e.g., call void @"_ZN3stdxxx or %_5 = invoke ptr @"_ZN68_$LTxxx
    pub direct_callee: Option<String>,

    /// caller's context
    pub context: PAContext,

    /// Source location of the call site, if available.
    pub source_loc: Option<PASourceLocation>,
}

/// For other edge types, change is from Src(delta).
/// but special for store:
///  Store with Src(delta)   // src got new pointer values
///  Store with Dst(delta)   // dst got new target objects
#[derive(Debug, Clone)]
pub enum PAWorkDelta {
    /// edge.src received these newly added pointees.
    Src(BTreeSet<PANodeId>),

    /// edge.dst received these newly added pointees.
    /// Mainly for Store: *dst = src.
    Dst(BTreeSet<PANodeId>),

    /// Used for AddressOf or special seed events.
    Full,
}

#[derive(Debug, Clone)]
pub struct PAWorkItem {
    pub edge: PAEdge,

    /// Newly discovered points-to objects for edge.src.
    ///
    /// For most edges, this means:
    ///   delta = new pointees of edge.src
    ///
    /// For Store, we may need special handling because both src and dst matter.
    pub delta: PAWorkDelta,
}

// #[derive(Debug, Clone)]
pub struct PointerAssignmentGraph<'m> {
    pub modules: Vec<&'m Module>,
    pub functions_by_type: FunctionsByType<'m>,
    pub functions_by_name: BTreeMap<String, &'m llvm_ir::Function>,
    pub ssa_types: BTreeMap<String, Option<llvm_ir::TypeRef>>,
    pub global_types: BTreeMap<String, llvm_ir::TypeRef>,

    // for functions in vtable
    pub vtable2function: BTreeMap<String, Vec<String>>,
    pub function2vtable: BTreeMap<String, Vec<String>>,

    // our created cg when on-the-fy, otherwise import from llvm-ir
    pub call_graph: CallGraph<'m>,

    /// (src, dst, kind) of every edge in `edges`, for O(log n) duplicate checks
    /// instead of an O(E) linear scan over `edges` on each insertion
    pub edge_index: BTreeSet<(PANodeId, PANodeId, PAEdgeKind)>,
    pub edges: Vec<PAEdge>,

    /// callsite id -> PACallSite
    pub callsites: BTreeMap<usize, PACallSite<'m>>,
    next_callsite_id: usize,

    /// id -> PANode
    pub nodes: HashMap<PANodeId, PANode<'m>>,

    /// canonical key -> id
    pub node_ids: HashMap<String, PANodeId>,

    /// global next available node id
    next_node_id: PANodeId,

    /// functions (and their contexts) whose instructions have already been scanned and constraints generated
    pub visited_functions: BTreeSet<(String, PAContext)>,

    /// functions (and their contexts) whose instructions wait to be scanned
    pub pending_functions: VecDeque<(String, PAContext)>,

    /// for each iteration of Andersen's algorithm, we will discover new edges and new cgnodes
    pub worklist: Vec<PAWorkItem>,
    /// node id -> all edges where this node is the source/lhs (outgoing edges)
    pub lhs2edges: BTreeMap<PANodeId, Vec<PAEdge>>,

    /// node id -> Store edges where this node is edge.dst
    /// Needed because Store depends on both src and dst.
    pub store_dst_edges: BTreeMap<PANodeId, Vec<PAEdge>>,

    /// node id -> MemCopy edges where this node is edge.dst, i.e., dst pointer -> memcopy edges
    pub memcpy_dst_edges: BTreeMap<PANodeId, Vec<PAEdge>>,

    /// base object -> all known constant-offset field objects
    pub byte_offset_field_objects: HashMap<PANodeId, BTreeSet<PANodeId>>,

    // base object -> destinations of unknown-offset GEPs that depend on this base
    pub unknown_offset_users: HashMap<PANodeId, BTreeSet<PANodeId>>,

    pub config: PAConfig,

    /// crate name of the entry (main) module; used for selective context: only
    /// application functions carry a call context, library/runtime plumbing
    /// (std/core/alloc/tokio/...) stays context-insensitive (Global) to avoid
    /// the (function, context) instantiation blow-up. empty => gate disabled.
    pub app_crate: String,

    /// for AFG, the engine to record functions
    pub semantic_points: Vec<SemanticPoint>,
    pub taint_analysis: Option<TaintAnalysis<'m>>,
}

impl<'m> PointerAssignmentGraph<'m> {
    pub fn new(
        modules: impl IntoIterator<Item = &'m Module>,
        functions_by_type: &FunctionsByType<'m>,
        mode: &str,
        k: Option<usize>,
        context_signatures: Option<(Vec<Signature>, Vec<Signature>, Vec<Signature>)>,
    ) -> Self {
        let start_time: Instant = Instant::now();

        let modules: Vec<&'m Module> = modules.into_iter().collect();
        let functions_by_name: BTreeMap<String, &'m llvm_ir::Function> = modules
            .iter()
            .flat_map(|module| {
                module.functions.iter().map(|f| {
                    (
                        util::normalize_function_name(f.name.as_str()).to_string(),
                        f,
                    )
                })
            })
            .collect();
        let cg = CallGraph::empty();
        // let cg = CallGraph::new(modules.clone(), functions_by_type);

        // for type filter
        let mut ssa_types = BTreeMap::new();
        let mut global_types = BTreeMap::new();
        for module in &modules {
            for gv in &module.global_vars {
                global_types.insert(
                    util::normalize_function_name(&format!("{}", gv.name)).to_string(),
                    gv.ty.clone(),
                );
            }

            for func in &module.functions {
                for param in &func.parameters {
                    ssa_types.insert(name_key(&param.name), Some(param.ty.clone()));
                }

                for block in &func.basic_blocks {
                    for instr in &block.instrs {
                        record_instruction_result_type(instr, &mut ssa_types);
                    }

                    record_terminator_result_type(&block.term, &mut ssa_types);
                }
            }
        }

        let (global_function_refs, function_referrers) = collect_vtable_functions(&modules);
        let config = match mode {
            "insensitive" => PAConfig::insensitive(),
            "kcfa" => PAConfig::k_callsite(k.unwrap()),
            "kobj" => PAConfig::k_object(k.unwrap()),
            "kmix" => PAConfig::k_mixed(k.unwrap()),
            "afg" => PAConfig::afg(context_signatures),
            _ => panic!("no such config."),
        };

        let mut engine = if config.policy == PAContextSelectPolicy::AFG {
            Some(TaintAnalysis::new())
        } else {
            None
        };

        let mut pag = Self {
            modules: modules.clone(),
            functions_by_name,
            functions_by_type: functions_by_type.clone(),
            ssa_types: ssa_types,
            global_types: global_types,
            function2vtable: function_referrers,
            vtable2function: global_function_refs,
            call_graph: cg,
            edges: Vec::new(),
            edge_index: BTreeSet::new(),
            callsites: BTreeMap::new(),
            next_callsite_id: 0,
            nodes: HashMap::new(),
            node_ids: HashMap::new(),
            next_node_id: 0,
            visited_functions: BTreeSet::new(),
            pending_functions: VecDeque::new(),
            worklist: Vec::new(),
            lhs2edges: BTreeMap::new(),
            store_dst_edges: BTreeMap::new(),
            memcpy_dst_edges: BTreeMap::new(),
            byte_offset_field_objects: HashMap::new(),
            unknown_offset_users: HashMap::new(),
            config: config,
            app_crate: String::new(),
            semantic_points: Vec::new(),
            taint_analysis: engine,
        };

        if let Some(main_name) = pag.find_main_function_name() {
            println!("[PAG] potential main function: {}", main_name);

            // Derive the application crate for all policies (used by selective
            // context, entry-point seeding, and the taint analysis's execution
            // propagation), not only under AppOnly.
            pag.app_crate = parse_app_crate(&main_name);

            match pag.config.policy {
                PAContextSelectPolicy::AppOnly => {
                    println!("[PAG] selective context app crate: {:?}", pag.app_crate);
                }
                _ => {}
            }

            pag.pending_functions
                .push_back((main_name.clone(), PAContext::global()));

            // Entry-point seeding: framework-dispatched handlers (axum/actix
            // .route(..).post(handler), spawned closures, etc.) are invoked by the
            // runtime, not reached from main, so their bodies -- and the LLM/AC
            // calls inside them -- would never be analyzed. Seed every app-crate,
            // non-skipped function as a Global root so those handlers are reached.
            // The skip-list keeps std/tokio out, so this stays bounded.
            let seed_crate = parse_app_crate(&main_name);
            pag.seed_app_crate_entry_points(&seed_crate);
        } else {
            println!("[PAG] warning: cannot find main function; no constraints discovered");
            return pag;
        }

        println!(
            "[PAG] config: context mode = {:?} with k = {} under policy = {:?}",
            pag.config.context_mode, pag.config.default_k, pag.config.policy
        );

        // discover new constraints and solve until fixed point
        // pag.discover_all_constraints();
        pag.discover_reachable_constraints();
        while pag.worklist.len() > 0 {
            debug!(
                "PointerAssignmentGraph::new: discovered {} new edges in worklist",
                pag.worklist.len(),
            );

            pag.solve();
        }

        let pag_build_time = start_time.elapsed();
        println!(
            "[Timing] pointer assignment graph construction finished in {:.3?} (including call graph construction)",
            pag_build_time
        );

        pag.print_statistics();

        if let Some(mut engine) = pag.taint_analysis.take() {
            engine.init(&pag);
            engine.run();
            engine.print_result();
        }

        pag
    }

    /// find main function
    /// heuristics here: my compiled ir all have the following string in main:
    /// _ZN4main4main17h
    fn find_main_function_name(&self) -> Option<String> {
        // Rust-mangled main usually contains "main4main" or ends around "4main".
        for name in self.functions_by_name.keys() {
            if name.contains("main4main") || name.contains("main17h") {
                return Some(name.to_string());
            }
        }

        None
    }

    /// Seed every app-crate, non-skipped function as a Global root so that
    /// framework-dispatched entry points (HTTP handlers, spawned closures) that
    /// are unreachable from `main` still get analyzed. Bounded by the skip-list
    /// (std/tokio stay out) and by the app crate (deps stay out).
    fn seed_app_crate_entry_points(&mut self, app_crate: &str) {
        if app_crate.is_empty() {
            println!("[PAG] entry-point seeding skipped (no app crate)");
            return;
        }

        let roots: Vec<String> = self
            .functions_by_name
            .keys()
            .filter(|name| name.contains(app_crate) && !should_skip_function_body(name))
            .cloned()
            .collect();

        let mut seeded = 0usize;
        for name in roots {
            let key = (name.clone(), PAContext::global());
            if self.visited_functions.contains(&key)
                || self.pending_functions.iter().any(|x| x == &key)
            {
                continue;
            }
            self.pending_functions.push_back(key);
            seeded += 1;
        }

        println!(
            "[PAG] seeded {} app-crate non-main entry-points (from crate {:?})",
            seeded, app_crate
        );
    }

    pub fn discover_reachable_constraints(&mut self) {
        while let Some((function_name, context)) = self.pending_functions.pop_front() {
            let key = (function_name.clone(), context.clone());
            if self.visited_functions.contains(&key) {
                continue;
            }

            if should_skip_function_body(&function_name) {
                println!("[PAG] skip visiting function body: {}", function_name);
                continue;
            }

            let Some(func) = self.functions_by_name.get(&function_name).copied() else {
                println!(
                    "[PAG] reachable function {} not found in functions_by_name",
                    function_name
                );
                continue;
            };

            debug!(
                "[PAG] discovering constraints in function: {} with context: {:?}",
                function_name, context
            );

            self.visited_functions.insert(key);

            self.discover_constraints_in_function(func, context);
        }
    }

    /// since we create and process constraints for all functions in all modules,
    /// no matter whether they can be reached by main function or not,
    /// this discover_new_constraints should include all constraints
    /// after excluding those can only be discovered by receiver object and indirect functions
    /// -> so this process can be slow and theoratically should not see many iterations ...
    pub fn discover_all_constraints(&mut self) {
        let modules: Vec<&'m Module> = self.modules.clone();
        for module in modules {
            for func in &module.functions {
                self.discover_constraints_in_function(func, PAContext::global());
            }
        }
    }

    /// TODO: handle special rust functions, e.g., clone()
    /// most functions we handled here does not have a function in function_by_type/name
    pub fn handle_special_rust_functions(
        &mut self,
        function_name: &str, //callee
        caller_name: &str,
        block_name: &str,
        callsite_kind: &PACallSiteKind<'m>,
        callsite_id: usize,
        caller_context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) -> bool {
        // model:
        // declare void @llvm.memcpy.p0.p0.i64(ptr nocapture writeonly %dst,  // The starting address of the destination memory block.
        //                            ptr nocapture readonly %src,             // The starting address of the source memory block.
        //                            i64 %len,                                // The total number of bytes to copy from the source to the destination.
        //                            i1 %isvolatile)
        // copy %len bytes from memory at %src into memory at %dst
        // create:
        // %y -[Copy]-> %x
        if function_name.starts_with("llvm.memcpy.") {
            let args = self.get_callsite_arguments(&callsite_kind);

            if args.len() >= 2 {
                // llvm.memcpy(dst, src, size, volatile)
                let dst_ptr = &args[0].0;
                let src_ptr = &args[1].0;

                let (src_id, dst_id) = self.add_pag_edge(
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(src_ptr), caller_name),
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(dst_ptr), caller_name),
                    PAEdgeKind::MemCopy,
                    caller_name.to_string(),
                    block_name.to_string(),
                    caller_context.clone(),
                    source_loc.clone(),
                );

                // println!("[PAG] handling memcpy from caller = {}", caller_name);
                // println!("[PAG] src id = {}, dst id = {}", src_id, dst_id);

                debug!(
                    "[PAG] model llvm.memcpy as MemCopy: src={:?} dst={:?}",
                    src_ptr, dst_ptr
                );

                return true;
            }
        }

        // heap allocation: model the raw allocator as a fresh heap object at the
        // callsite and bind it to the result, without analyzing the allocator body
        if is_heap_allocator(function_name) {
            if let Some(result) = self.get_callsite_result(&callsite_kind) {
                let heap = PANodeKind::HeapObject {
                    function: caller_name.to_string(),
                    block: block_name.to_string(),
                    name: format!("{}", result),
                    obj_callsite_id: callsite_id,
                    allocated_type: None,
                };

                self.add_pag_edge(
                    heap,
                    self.get_nodekind_for_value_ref(
                        PAValueRef::Name {
                            name: result,
                            ty: None,
                        },
                        caller_name,
                    ),
                    PAEdgeKind::AddressOf,
                    caller_name.to_string(),
                    block_name.to_string(),
                    caller_context.clone(),
                    source_loc.clone(),
                );

                debug!(
                    "[PAG] model heap alloc: {}::{}::{} for {}",
                    caller_name, block_name, result, function_name
                );
            }

            return true;
        }

        // smart-pointer deref: the result aliases the self argument
        // <T as core::ops::deref::Deref>::deref(self) -> &T
        if is_deref(function_name) {
            let self_arg = self
                .get_callsite_arguments(&callsite_kind)
                .first()
                .map(|(op, _)| op);
            let result = self.get_callsite_result(&callsite_kind);

            if let (Some(self_arg), Some(result)) = (self_arg, result) {
                self.add_pag_edge(
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(self_arg), caller_name),
                    self.get_nodekind_for_value_ref(
                        PAValueRef::Name {
                            name: result,
                            ty: None,
                        },
                        caller_name,
                    ),
                    PAEdgeKind::AggregateCopy,
                    caller_name.to_string(),
                    block_name.to_string(),
                    caller_context.clone(),
                    source_loc.clone(),
                );

                // String::deref returns { ptr, i64 }; expose the data pointer as field 0
                if is_string_deref(function_name) {
                    let dst = self.get_or_create_node(
                        self.get_nodekind_for_value_ref(
                            PAValueRef::Name {
                                name: result,
                                ty: None,
                            },
                            caller_name,
                        ),
                        caller_context.clone(),
                        source_loc.clone(),
                    );
                    let slot = PANodeKind::AggregateField {
                        origin: dst,
                        field: vec![0],
                    };

                    self.add_pag_edge(
                        self.get_nodekind_for_value_ref(PAValueRef::Operand(self_arg), caller_name),
                        slot.clone(),
                        PAEdgeKind::AggregateCopy,
                        caller_name.to_string(),
                        block_name.to_string(),
                        caller_context.clone(),
                        source_loc.clone(),
                    );

                    self.add_pag_edge(
                        slot,
                        self.get_nodekind_for_value_ref(
                            PAValueRef::Name {
                                name: result,
                                ty: None,
                            },
                            caller_name,
                        ),
                        PAEdgeKind::AddressOf,
                        caller_name.to_string(),
                        block_name.to_string(),
                        caller_context.clone(),
                        source_loc,
                    );
                }
            }

            return true;
        }

        // <alloc::sync::Arc<T, A> as core::clone::Clone>::clone
        // may have return value or sret
        // normal return:
        //      clone(self) -> result
        // sret:
        //      clone(sret_result, self)
        if is_clone(function_name) {
            let args = self.get_callsite_arguments(callsite_kind);

            let (self_operand, result_kind) = match args.len() {
                // normal return:
                // %r = call @Clone::clone(%self)
                1 => {
                    let Some(result) = self.get_callsite_result(callsite_kind) else {
                        return true;
                    };
                    let self_operand = &args[0].0;
                    let result_kind = self.get_nodekind_for_value_ref(
                        PAValueRef::Name {
                            name: result,
                            ty: None,
                        },
                        caller_name,
                    );

                    (self_operand, result_kind)
                }

                // sret:
                // call @Clone::clone(%result, %self)
                2 => {
                    let result_operand = &args[0].0;
                    let self_operand = &args[1].0;

                    let result_kind = self.get_nodekind_for_value_ref(
                        PAValueRef::Operand(result_operand),
                        caller_name,
                    );

                    (self_operand, result_kind)
                }

                _ => return true,
            };

            let self_kind =
                self.get_nodekind_for_value_ref(PAValueRef::Operand(self_operand), caller_name);

            self.add_pag_edge_w_diff_contexts(
                self_kind,
                result_kind,
                PAEdgeKind::Copy,
                caller_name.to_string(),
                block_name.to_string(),
                caller_context.clone(),
                caller_context.clone(),
                source_loc.clone(),
            );
        }

        // core::option::Option<&T>::cloned(sret out, opt): copy contents opt -> out
        if is_option_cloned(function_name) {
            let args = self.get_callsite_arguments(&callsite_kind);

            if args.len() >= 2 {
                let out_ptr = &args[0].0;
                let src_ptr = &args[1].0;

                self.add_pag_edge(
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(src_ptr), function_name),
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(out_ptr), function_name),
                    PAEdgeKind::MemCopy,
                    function_name.to_string(),
                    block_name.to_string(),
                    caller_context,
                    source_loc,
                );

                return true;
            }
        }

        false
    }

    fn get_source_location_from_instruction(&self, inst: &Instruction) -> Option<PASourceLocation> {
        // Implement the logic to extract source location from debug information in the instruction
        // Return Some(PASourceLocation) if available, otherwise None
        let dbg = instruction_debugloc(inst)?;

        Some(PASourceLocation {
            file: Some(dbg.filename.clone()),
            directory: dbg.directory.clone(),
            line: Some(dbg.line),
            column: dbg.col,
        })
    }

    fn get_source_location_from_debug(&self, dbg: Option<&DebugLoc>) -> Option<PASourceLocation> {
        let dbg = dbg?;

        Some(PASourceLocation {
            file: Some(dbg.filename.clone()),
            directory: dbg.directory.clone(),
            line: Some(dbg.line),
            column: dbg.col,
        })
    }

    /// visit ir instructions and create constraints
    fn discover_constraints_in_function(
        &mut self,
        func: &'m llvm_ir::Function,
        context: PAContext,
    ) {
        let function_name = func.name.clone();

        let skip = self.compute_cleanup_blocks_with_cfg(func);

        for block in &func.basic_blocks {
            let block_name = format!("{}", block.name);
            if skip.contains(&util::normalize_block_label(&block_name)) {
                debug!(
                    "discover_constraints_in_function: skip basicblock={}",
                    block_name
                );
                continue;
            }

            for instr in &block.instrs {
                let source_loc = self.get_source_location_from_instruction(instr);
                match instr {
                    Instruction::Alloca(alloca) => {
                        let src = PANodeKind::AllocaObject {
                            function: function_name.clone(),
                            block: block_name.clone(),
                            dest: &alloca.dest,
                            allocated_type: &alloca.allocated_type,
                        };
                        let dst = self.get_nodekind_for_value_ref(
                            PAValueRef::Name {
                                name: &alloca.dest,
                                ty: None,
                            },
                            &function_name.clone(),
                        );

                        self.add_pag_edge(
                            src,
                            dst,
                            PAEdgeKind::AddressOf,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::Load(load) => {
                        let src = self.get_nodekind_for_value_ref(
                            PAValueRef::Operand(&load.address),
                            &function_name.clone(),
                        );
                        let dst = self.get_nodekind_for_value_ref(
                            PAValueRef::Name {
                                name: &load.dest,
                                ty: Some(load.loaded_ty.clone()),
                            },
                            &function_name.clone(),
                        );

                        self.add_pag_edge(
                            src,
                            dst,
                            PAEdgeKind::Load,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::Store(store) => {
                        let value = &store.value;
                        self.add_global_address_if_needed(
                            value,
                            &function_name,
                            &block_name,
                            context.clone(),
                            source_loc.clone(),
                        );

                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&store.value),
                                &function_name.clone(),
                            ),
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&store.address),
                                &function_name.clone(),
                            ),
                            PAEdgeKind::Store,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::GetElementPtr(gep) => {
                        // we have:
                        // GlobalObject(@g)  -> GlobalAddress(@g)  [AddressOf]
                        // GlobalAddress(@g) -> Operand(@g)        [Copy]
                        // Operand(@g)       -> %gep_dest          [GEP(indices)]
                        self.add_global_address_if_needed(
                            &gep.address,
                            &function_name,
                            &block_name,
                            context.clone(),
                            source_loc.clone(),
                        );

                        match gep.source_element_type.as_ref() {
                            llvm_ir::Type::IntegerType { bits: 8 }
                            | llvm_ir::Type::IntegerType { bits: 32 }
                            | llvm_ir::Type::IntegerType { bits: 64 } => {
                                // byte-offset GEP
                                // e.g.,  %42 = getelementptr inbounds i8, ptr %41, i64 8
                                // and
                                // %_18 = getelementptr inbounds ptr %_8, i64 %len
                                let src = self.get_nodekind_for_value_ref(
                                    PAValueRef::Operand(&gep.address),
                                    &function_name.clone(),
                                );
                                let dst = self.get_nodekind_for_value_ref(
                                    PAValueRef::Name {
                                        name: &gep.dest,
                                        ty: None,
                                    },
                                    &function_name.clone(),
                                );

                                let edge_kind = if let Some(offset) =
                                    gep_single_constant_offset(&gep.indices)
                                {
                                    PAEdgeKind::ByteOffsetGEP { offset }
                                } else {
                                    PAEdgeKind::UnknownOffsetGEP
                                };

                                self.add_pag_edge(
                                    src,
                                    dst,
                                    edge_kind,
                                    function_name.to_string(),
                                    block_name.to_string(),
                                    context.clone(),
                                    source_loc.clone(),
                                );
                            }

                            llvm_ir::Type::StructType { .. }
                            | llvm_ir::Type::NamedStructType { .. }
                            | llvm_ir::Type::ArrayType { .. } => {
                                // typed aggregate GEP
                                // %133 = getelementptr inbounds %"core::result::Result<...>::Ok", ptr %_46, i32 0, i32 1
                                let indices = gep_indices_as_u64(&gep.indices);
                                self.add_pag_edge(
                                    self.get_nodekind_for_value_ref(
                                        PAValueRef::Operand(&gep.address),
                                        &function_name.clone(),
                                    ),
                                    self.get_nodekind_for_value_ref(
                                        PAValueRef::Name {
                                            name: &gep.dest,
                                            ty: None,
                                        },
                                        &function_name.clone(),
                                    ),
                                    PAEdgeKind::GEP { indices },
                                    function_name.clone(),
                                    block_name.clone(),
                                    context.clone(),
                                    source_loc.clone(),
                                );
                            }

                            _ => {
                                // unknown/general GEP
                                println!(
                                    "[PAG] unknow GEP source type = {:?} in {}",
                                    gep.source_element_type, gep,
                                );
                            }
                        }
                    }

                    Instruction::BitCast(bitcast) => {
                        self.add_global_address_if_needed(
                            &bitcast.operand,
                            &function_name,
                            &block_name,
                            context.clone(),
                            source_loc.clone(),
                        );

                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&bitcast.operand),
                                &function_name.clone(),
                            ),
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Name {
                                    name: &bitcast.dest,
                                    ty: None,
                                },
                                &function_name.clone(),
                            ),
                            PAEdgeKind::BitCast,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::AddrSpaceCast(cast) => {
                        let src = self.get_nodekind_for_value_ref(
                            PAValueRef::Operand(&cast.operand),
                            &function_name.clone(),
                        );
                        let dst = self.get_nodekind_for_value_ref(
                            PAValueRef::Name {
                                name: &cast.dest,
                                ty: None,
                            },
                            &function_name.clone(),
                        );

                        self.add_pag_edge(
                            src,
                            dst,
                            PAEdgeKind::AddrSpaceCast,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::IntToPtr(inttoptr) => {
                        // self.add_pag_edge(
                        //     PANodeKind::UnknownObject {
                        //         reason: format!(
                        //             "inttoptr:{}:{}:{}",
                        //             function_name, block_name, i.dest
                        //         ),
                        //     },
                        //     PANodeKind::ValueName(&i.dest),
                        //     PAEdgeKind::AddressOf,
                        //     function_name,
                        //     block_name.to_string(),
                        // );

                        debug!(
                            "[PAG] skip IntToPtr: operand={:?} dest={}",
                            inttoptr.operand, inttoptr.dest
                        );
                    }

                    Instruction::Phi(phi) => {
                        let dst = self.get_nodekind_for_value_ref(
                            PAValueRef::Name {
                                name: &phi.dest,
                                ty: None,
                            },
                            &function_name.clone(),
                        );

                        for (incoming_value, incoming_block) in &phi.incoming_values {
                            let src = self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(incoming_value),
                                &function_name.clone(),
                            );
                            let kind = format!("phi from {}", incoming_block);

                            self.add_pag_edge(
                                src,
                                dst.clone(),
                                PAEdgeKind::Phi,
                                function_name.clone(),
                                block_name.clone() + " (" + &kind + ")",
                                context.clone(),
                                source_loc.clone(),
                            );
                        }
                    }

                    Instruction::Select(select) => {
                        let dst = self.get_nodekind_for_value_ref(
                            PAValueRef::Name {
                                name: &select.dest,
                                ty: None,
                            },
                            &function_name.clone(),
                        );

                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&select.true_value),
                                &function_name.clone(),
                            ),
                            dst.clone(),
                            PAEdgeKind::Select, // true branch
                            function_name.clone(),
                            block_name.clone() + " (true branch)",
                            context.clone(),
                            source_loc.clone(),
                        );

                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&select.false_value),
                                &function_name.clone(),
                            ),
                            dst.clone(),
                            PAEdgeKind::Select, // false branch
                            function_name.clone(),
                            block_name.clone() + " (false branch)",
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::InsertValue(insertvalue) => {
                        // %new = insertvalue %old, %val, field
                        let field = indices_as_u64(&insertvalue.indices);
                        let dst = self.get_or_create_node(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Name {
                                    name: &insertvalue.dest,
                                    ty: None,
                                },
                                &function_name.clone(),
                            ),
                            context.clone(),
                            source_loc.clone(),
                        );
                        let slot = PANodeKind::AggregateField { origin: dst, field };

                        // inherit the other fields from the base aggregate
                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&insertvalue.aggregate),
                                &function_name.clone(),
                            ),
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Name {
                                    name: &insertvalue.dest,
                                    ty: None,
                                },
                                &function_name.clone(),
                            ),
                            PAEdgeKind::AggregateCopy,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );

                        // pts(slot) = pts(%val)
                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&insertvalue.element),
                                &function_name.clone(),
                            ),
                            slot.clone(),
                            PAEdgeKind::AggregateCopy,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );

                        // %new points to the slot
                        self.add_pag_edge(
                            slot,
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Name {
                                    name: &insertvalue.dest,
                                    ty: None,
                                },
                                &function_name.clone(),
                            ),
                            PAEdgeKind::AddressOf,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::ExtractValue(extractvalue) => {
                        // %dst = extractvalue %agg, field
                        let field = indices_as_u64(&extractvalue.indices);
                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&extractvalue.aggregate),
                                &function_name.clone(),
                            ),
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Name {
                                    name: &extractvalue.dest,
                                    ty: None,
                                },
                                &function_name.clone(),
                            ),
                            PAEdgeKind::ExtractCopy { field },
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc.clone(),
                        );
                    }

                    Instruction::Trunc(trunc) => {
                        self.add_pag_edge(
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Operand(&trunc.operand),
                                &function_name.clone(),
                            ),
                            self.get_nodekind_for_value_ref(
                                PAValueRef::Name {
                                    name: &trunc.dest,
                                    ty: None,
                                },
                                &function_name.clone(),
                            ),
                            PAEdgeKind::Copy,
                            function_name.clone(),
                            block_name.clone(),
                            context.clone(),
                            source_loc,
                        );
                    }

                    Instruction::Call(call) => {
                        self.add_edges_for_call(
                            &function_name.clone(),
                            &block_name,
                            PACallSiteKind::Call(call),
                            context.clone(),
                            source_loc,
                        );
                    }

                    _ => {
                        debug!(
                            "Ignoring instruction {:?} in function {} block {}",
                            instr,
                            function_name.clone(),
                            block_name
                        );
                    }
                }
            }

            match &block.term {
                llvm_ir::terminator::Terminator::Invoke(invoke) => {
                    let debug_info = invoke.get_debug_loc();
                    let source_loc = self.get_source_location_from_debug(debug_info.as_ref());
                    let function_name = func.name.clone();

                    self.add_edges_for_call(
                        &function_name.clone(),
                        &block_name,
                        PACallSiteKind::Invoke(invoke),
                        context.clone(),
                        source_loc,
                    );
                }

                llvm_ir::Terminator::Ret(ret) => {
                    let debug_info = ret.get_debug_loc();
                    let source_loc = self.get_source_location_from_debug(debug_info.as_ref());

                    if let Some(ret_val) = &ret.return_operand {
                        let src = self.get_nodekind_for_value_ref(
                            PAValueRef::Operand(ret_val),
                            &function_name.clone(),
                        );
                        let dst = PANodeKind::FunctionReturn {
                            function: func.name.clone(),
                        };

                        self.add_pag_edge_w_diff_contexts(
                            src,
                            dst,
                            PAEdgeKind::Copy,
                            func.name.clone(),
                            block_name.clone(),
                            context.clone(),
                            context.clone(), // TODO: using caller's context for now
                            source_loc,
                        );
                    }
                }

                _ => {}
            }
        }
    }

    /// Model:
    ///
    ///   store ptr @global, ptr %addr
    ///
    /// as:
    ///
    ///   GlobalObject(@global) -[AddressOf]-> GlobalAddress(@global)
    ///   FunctionObject(@f)  -[AddressOf]-> GlobalAddress(@f)
    ///   GlobalAddress(@global)      -[Store/Copy...]->    Operand(%addr)
    ///
    /// Then the Store solver will propagate pts(Operand(@global))
    /// into the memory objects pointed to by %addr.
    /// same for bitcast and GEP
    fn add_global_address_if_needed(
        &mut self,
        op: &'m llvm_ir::Operand,
        function_name: &str,
        block_name: &str,
        context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) {
        let Some(global_name) = global_name_from_operand(op) else {
            return;
        };

        let clean_name = util::normalize_function_name(&global_name).to_string();

        let address_node = PANodeKind::GlobalAddress {
            name: clean_name.clone(),
        };

        if self.functions_by_name.contains_key(clean_name.as_str()) {
            // we did this in collect_vtable
            // // FunctionObject(@f) -[AddressOf]-> GlobalAddress(@f)
            // self.add_pag_edge(
            //     PANodeKind::FunctionObject {
            //         function: clean_name.clone(),
            //     },
            //     address_node.clone(),
            //     PAEdgeKind::AddressOf,
            //     function_name,
            //     block_name.to_string(),
            // );
        } else {
            // GlobalObject(@g) -[AddressOf]-> GlobalAddress(@g)
            let (src_id, dst_id) = self.add_pag_edge(
                PANodeKind::GlobalObject {
                    name: clean_name.clone(),
                },
                address_node.clone(),
                PAEdgeKind::AddressOf,
                function_name.to_string(),
                block_name.to_string(),
                context.clone(),
                source_loc.clone(),
            );

            debug!("[PAG] add_global_address_if_needed: create global pag edge: src={} -[AddressOf]-> dst={} ", src_id, dst_id);
        }

        // GlobalAddress(@g/@f) -[Copy]-> Operand(ptr @g/@f)
        //
        // This lets normal store/copy/GEP edges that use `op` work.
        let (src_id, dst_id) = self.add_pag_edge(
            PANodeKind::GlobalObject { name: global_name },
            self.get_nodekind_for_value_ref(PAValueRef::Operand(op), &function_name),
            PAEdgeKind::AddressOf,
            function_name.to_string(),
            block_name.to_string(),
            context.clone(),
            source_loc,
        );

        debug!("[PAG] add_global_address_if_needed: create global pag edge: src={} -[AddressOf]-> dst={} ", src_id, dst_id);
    }

    fn infer_node_type(&self, kind: &PANodeKind<'m>) -> Option<llvm_ir::TypeRef> {
        match kind {
            PANodeKind::SSAValue { function, name, ty } => ty.clone(),
            PANodeKind::Constant { op } => operand_type(op),

            PANodeKind::AllocaObject { allocated_type, .. } => {
                Some(allocated_type.clone()).cloned()
            }

            PANodeKind::FieldObject { field_type, .. } => field_type.clone(),

            PANodeKind::GlobalObject { name } => self.global_types.get(name).cloned(),

            PANodeKind::FunctionReturn { function } => self
                .functions_by_name
                .get(function)
                .map(|f| f.return_type.clone()),

            PANodeKind::ReceiverObject { .. }
            | PANodeKind::IndirectCallTarget { .. }
            | PANodeKind::TableSlot { .. }
            | PANodeKind::GlobalAddress { .. }
            | PANodeKind::AggregateField { .. }
            | PANodeKind::HeapObject { .. }
            | PANodeKind::FunctionObject { .. } => None,
        }
    }

    /// TODO: skip creating nodes for xxx.debug.spill.xxx
    fn get_nodekind_for_value_ref(
        &self,
        value: PAValueRef<'m>,
        function_name: &str,
    ) -> PANodeKind<'m> {
        let function = util::normalize_function_name(function_name).to_string();

        match value {
            PAValueRef::Operand(llvm_ir::Operand::LocalOperand { name, ty }) => {
                PANodeKind::SSAValue {
                    function: Some(function),
                    name,
                    ty: Some(ty.clone()),
                }
            }

            PAValueRef::Parameter(param) => PANodeKind::SSAValue {
                function: Some(function),
                name: &param.name,
                ty: Some(param.ty.clone()),
            },

            PAValueRef::Name { name, ty } => PANodeKind::SSAValue {
                function: Some(function),
                name,
                ty: ty
                    .clone()
                    .or_else(|| self.ssa_types.get(&name_key(name)).cloned().flatten()),
            },

            PAValueRef::Operand(op) => PANodeKind::Constant { op },
        }
    }

    /// create a pag node (with context) if not exist in self.nodes; otherwise, return the node
    pub fn get_or_create_node(
        &mut self,
        nodekind: PANodeKind<'m>,
        context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) -> PANodeId {
        let context = self.get_context_for_node_kind(&nodekind, &context);
        let ty = self.infer_node_type(&nodekind);
        let id = self.nodes.len();

        // temp node to get a key
        let node = PANode {
            id,
            kind: nodekind,
            context,
            ty,
            points_to: BTreeSet::new(),
            source_loc,
        };

        let key = node.key();

        if let Some(id) = self.node_ids.get(&key) {
            debug!(
                "get_or_create_node: found existing node with id={} for key={}",
                id, key
            );
            return *id;
        }

        debug!(
            "get_or_create_node: created new node with id={} for key={}",
            id, key
        );

        let track_id = self.next_node_id;
        assert!(
            id == track_id,
            "inconsistent node id assignment: should have {} but have {}",
            track_id,
            id
        );
        self.next_node_id += 1; // keep track of the node size
        self.nodes.insert(id, node);
        self.node_ids.insert(key, id);

        id
    }

    pub fn get_node_by_id(&self, id: PANodeId) -> Option<PANode> {
        let node = self.nodes.get(&id);
        let Some(node) = node else {
            debug!("[PAG] get_node_by_id: cannot find node with id = {}", id);
            return None;
        };

        debug!("[PAG] get_node_by_id: find id = {} -> node = {}", id, node);

        Some(node.clone())
    }

    /// policy for whether apply context on a node
    pub fn get_context_for_node_kind(
        &self,
        kind: &PANodeKind<'m>,
        requested_context: &PAContext,
    ) -> PAContext {
        if self.config.context_mode == PAContextMode::Insensitive {
            return PAContext::global();
        }

        match kind {
            PANodeKind::AllocaObject { .. }
            | PANodeKind::HeapObject { .. }
            | PANodeKind::ReceiverObject { .. }
            | PANodeKind::IndirectCallTarget { .. } => requested_context.clone(),

            // Usually keep function objects and globals context-insensitive.
            PANodeKind::FunctionObject { .. }
            | PANodeKind::GlobalObject { .. }
            | PANodeKind::GlobalAddress { .. }
            | PANodeKind::TableSlot { .. }
            | PANodeKind::Constant { .. } => PAContext::global(),

            // SSA values can be context-sensitive only when you are discovering
            // function body under a context.
            PANodeKind::SSAValue { .. }
            | PANodeKind::FunctionReturn { .. }
            | PANodeKind::FieldObject { .. }
            | PANodeKind::AggregateField { .. } => requested_context.clone(),
        }
    }

    /// for field-sensitive
    /// object/struct-field -> use object-sensitive
    fn get_or_create_field_object(&mut self, base_obj: PANodeId, indices: &[u64]) -> PANodeId {
        let new_field = normalize_gep_indices(indices);

        // GEP with no meaningful field access should not create FieldObject(base, []).
        if new_field.is_empty() {
            return base_obj;
        }

        let Some(base_node) = self.nodes.get(&base_obj) else {
            return base_obj;
        };

        let (root_base, mut field, root_ty) = match &base_node.kind {
            PANodeKind::FieldObject {
                base,
                field,
                field_type,
            } => {
                // Flatten:
                // FieldObject(base=A, field=[1]) + GEP [2]
                // becomes FieldObject(base=A, field=[1,2])
                (*base, field.clone(), field_type.clone())
            }

            _ => (base_obj, Vec::new(), base_node.ty.clone()),
        };

        field.extend(new_field);

        if field.len() > MAX_FIELD_DEPTH {
            debug!(
                "[PAG GEP] field path too deep; truncate extra indices: root=n{} field={:?}",
                root_base, field
            );

            field.truncate(MAX_FIELD_DEPTH);
            field.push(SUMMARY_FIELD);
        }

        let field_type = root_ty
            .as_ref()
            .and_then(|ty| gep_result_object_type(ty, &field));

        let base_context: PAContext = base_node.context.clone();

        self.get_or_create_node(
            PANodeKind::FieldObject {
                base: root_base,
                field,
                field_type,
            },
            base_context,
            base_node.source_loc.clone(), // should be ?
        )
    }

    /// for field-sensitive (byte offset and unknown offset)
    /// object/struct-field -> use object-sensitive
    fn get_or_create_byte_offset_field_object(
        &mut self,
        base_obj: PANodeId,
        offset: i64,
    ) -> PANodeId {
        let Some(base_node) = self.nodes.get(&base_obj) else {
            return base_obj;
        };

        let root_base = match &base_node.kind {
            PANodeKind::FieldObject { base, .. } => *base,
            _ => base_obj,
        };

        let offset_key = if offset >= 0 && offset <= 4096 {
            offset as u64
        } else {
            BYTE_OFFSET_SUMMARY
        };

        let base_context = base_node.context.clone();

        let field_obj = self.get_or_create_node(
            PANodeKind::FieldObject {
                base: root_base,
                field: vec![BYTE_OFFSET_MARKER, offset_key],
                field_type: None,
            },
            base_context,
            base_node.source_loc.clone(), // should be ?
        );

        /*
         * Important:
         * BTreeSet::insert tells us whether this field object is newly
         * discovered for root_base.
         */
        let is_new = self
            .byte_offset_field_objects
            .entry(root_base)
            .or_default()
            .insert(field_obj);

        if is_new {
            self.notify_unknown_offset_users(root_base, field_obj);
        }

        field_obj
    }

    /// update unknown offset whenever byte offset changs
    fn notify_unknown_offset_users(&mut self, root_base: PANodeId, new_field_obj: PANodeId) {
        let users = self
            .unknown_offset_users
            .get(&root_base)
            .cloned()
            .unwrap_or_default();

        if users.is_empty() {
            return;
        }

        let mut delta = BTreeSet::new();
        delta.insert(new_field_obj);

        for dst in users {
            self.add_points_to_and_enqueue(dst, &delta);
        }
    }

    /// add the new edge with lhs's pts (Store is different) to worklist
    /// edge -> newly discovered edge with no propagation
    /// we will merge delta for the same edge later in solver
    fn enqueue_initial_edge(&mut self, edge: PAEdge) {
        debug!(
            "[PAG Solver] enqueue new edge: n{} -[{:?}]-> n{}",
            edge.src, edge.kind, edge.dst
        );

        match edge.kind {
            PAEdgeKind::AddressOf => {
                self.worklist.push(PAWorkItem {
                    edge,
                    delta: PAWorkDelta::Full,
                });
            }

            PAEdgeKind::Store | PAEdgeKind::MemCopy => {
                // Store/MemCopy depends on src and dst.
                let src_pts = self.points_to_snapshot(edge.src);
                if !src_pts.is_empty() {
                    self.worklist.push(PAWorkItem {
                        edge: edge.clone(),
                        delta: PAWorkDelta::Src(src_pts),
                    });
                }

                let dst_pts = self.points_to_snapshot(edge.dst);
                if !dst_pts.is_empty() {
                    self.worklist.push(PAWorkItem {
                        edge,
                        delta: PAWorkDelta::Dst(dst_pts),
                    });
                }
            }

            _ => {
                // all other types of edges
                let src_pts = self.points_to_snapshot(edge.src);
                if !src_pts.is_empty() {
                    self.worklist.push(PAWorkItem {
                        edge,
                        delta: PAWorkDelta::Src(src_pts),
                    });
                }
            }
        }
    }

    /// check whether the edge already in self.edges;
    /// if not, update lhs2edges and add to worklist
    /// NOTE: this is for adding initial edge (before any propogation)
    fn insert_edge(&mut self, edge: PAEdge) {
        if self
            .edge_index
            .contains(&(edge.src, edge.dst, edge.kind.clone()))
        {
            return;
        }

        debug!(
            "insert_edge: adding new edge n{} -[{:?}]-> n{} in function={} block={}",
            edge.src, edge.kind, edge.dst, edge.function, edge.block
        );

        match edge.kind {
            PAEdgeKind::Store => {
                // For store edges, we need to add the edge to the store_dst_edges map for the dst node
                self.store_dst_edges
                    .entry(edge.dst)
                    .or_default()
                    .push(edge.clone());
            }
            PAEdgeKind::MemCopy => {
                // for MemCopy edges, ...
                self.memcpy_dst_edges
                    .entry(edge.dst)
                    .or_default()
                    .push(edge.clone());
            }
            _ => {
                // For all other edges, we add the edge to the lhs2edges map for the src node
                self.lhs2edges
                    .entry(edge.src)
                    .or_default()
                    .push(edge.clone());
            }
        }

        self.edges.push(edge.clone());
        self.edge_index
            .insert((edge.src, edge.dst, edge.kind.clone()));

        // Also seed it into the worklist.
        self.enqueue_initial_edge(edge);
    }

    fn create_and_indert_pag_edge(
        &mut self,
        kind: PAEdgeKind,
        src: PANodeId,
        dst: PANodeId,
        function: String,
        block: String,
    ) {
        if (kind == PAEdgeKind::Copy
            || kind == PAEdgeKind::BitCast
            || kind == PAEdgeKind::AddrSpaceCast
            || kind == PAEdgeKind::Phi
            || kind == PAEdgeKind::Select)
            && !self.nodes_are_copy_compatible(src, dst)
        {
            debug!(
                "[PAG] skip incompatible Copy edge: n{} ty={:?} -> n{} ty={:?}",
                src,
                self.nodes.get(&src).and_then(|n| n.ty.as_ref()),
                dst,
                self.nodes.get(&dst).and_then(|n| n.ty.as_ref()),
            );
            return;
        }

        // aggregate copies keep struct/array values whose fields hold pointers
        if kind == PAEdgeKind::AggregateCopy && !self.nodes_may_carry_pointer(src, dst) {
            debug!(
                "[PAG] skip pointer-free AggregateCopy edge: n{} ty={:?} -> n{} ty={:?}",
                src,
                self.nodes.get(&src).and_then(|n| n.ty.as_ref()),
                dst,
                self.nodes.get(&dst).and_then(|n| n.ty.as_ref()),
            );
            return;
        }

        debug!(
            "add_edge: adding edge from n{} -[{:?}]-> n{} in function={} block={}",
            src, kind, dst, function, block
        );

        let edge = PAEdge {
            src,
            dst,
            kind,
            function,
            block,
        };

        self.insert_edge(edge);
    }

    /// create pag nodes (if not exist) and add the corresponding pag edge if not exist
    /// nodes have the same context
    /// -> (PANodeId, PANodeId)
    fn add_pag_edge(
        &mut self,
        src_kind: PANodeKind<'m>,
        dst_kind: PANodeKind<'m>,
        kind: PAEdgeKind,
        function: String,
        block: String,
        context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) -> (PANodeId, PANodeId) {
        let src = self.get_or_create_node(src_kind, context.clone(), source_loc.clone());
        let dst = self.get_or_create_node(dst_kind, context, source_loc);

        self.create_and_indert_pag_edge(kind, src, dst, function, block);

        (src, dst)
    }

    /// for creating and adding pag nodes and edges of function call's parameters and return values
    /// they require different contexts
    /// return (src id, dst id)
    fn add_pag_edge_w_diff_contexts(
        &mut self,
        src_kind: PANodeKind<'m>,
        dst_kind: PANodeKind<'m>,
        kind: PAEdgeKind,
        function: String,
        block: String,
        src_context: PAContext, // caller context
        dst_context: PAContext, // callee context
        source_loc: Option<PASourceLocation>,
    ) -> (PANodeId, PANodeId) {
        let src = self.get_or_create_node(src_kind, src_context, source_loc.clone());
        let dst = self.get_or_create_node(dst_kind, dst_context, source_loc);

        self.create_and_indert_pag_edge(kind, src, dst, function, block);

        (src, dst)
    }

    // fn nodes_are_copy_compatible(&self, src: PANodeId, dst: PANodeId) -> bool {
    //     let src_ty = self.nodes.get(&src).and_then(|n| n.ty.as_ref());
    //     let dst_ty = self.nodes.get(&dst).and_then(|n| n.ty.as_ref());

    //     match (src_ty, dst_ty) {
    //         (Some(src_ty), Some(dst_ty)) => {
    //             type_is_pointer_like(src_ty) && type_is_pointer_like(dst_ty)
    //         }

    //         // Unknown type: do not reject.
    //         (None, _) | (_, None) => true,
    //     }
    // }

    fn nodes_are_copy_compatible(&self, src: PANodeId, dst: PANodeId) -> bool {
        let Some(src_node) = self.nodes.get(&src) else {
            return true;
        };
        let Some(dst_node) = self.nodes.get(&dst) else {
            return true;
        };

        let src_ty = src_node.ty.as_ref();
        let dst_ty = dst_node.ty.as_ref();

        match (src_ty, dst_ty) {
            (Some(src_ty), Some(dst_ty)) => {
                if type_is_pointer_like(src_ty) && type_is_pointer_like(dst_ty) {
                    return true;
                }

                if type_is_pointer_like(dst_ty) {
                    if let PANodeKind::Constant { op } = &src_node.kind {
                        if is_global_reference_constant(op) {
                            return true;
                        }
                    }
                }

                false
            }

            _ => true,
        }
    }

    /// like nodes_are_copy_compatible, but keeps aggregates whose fields hold pointers
    fn nodes_may_carry_pointer(&self, src: PANodeId, dst: PANodeId) -> bool {
        let src_ty = self.nodes.get(&src).and_then(|n| n.ty.as_ref());
        let dst_ty = self.nodes.get(&dst).and_then(|n| n.ty.as_ref());

        match (src_ty, dst_ty) {
            (Some(src_ty), Some(dst_ty)) => {
                type_may_contain_pointer(src_ty) && type_may_contain_pointer(dst_ty)
            }

            // Unknown type: do not reject.
            (None, _) | (_, None) => true,
        }
    }

    fn callsite_function_operand(&self, kind: &PACallSiteKind<'m>) -> Option<&'m llvm_ir::Operand> {
        match kind {
            PACallSiteKind::Call(call) => call_function_operand(&call.function),
            PACallSiteKind::Invoke(invoke) => call_function_operand(&invoke.function),
        }
    }

    /// push newly discovered callee to pending_functions if not exist
    fn enqueue_reachable_function(&mut self, callee_name: &str, callee_context: PAContext) {
        let callee_name = util::normalize_function_name(callee_name).to_string();
        let key = (callee_name.clone(), callee_context.clone());
        if self.visited_functions.contains(&key) {
            return;
        }

        if self.pending_functions.iter().any(|x| x == &key) {
            return;
        }

        if !self.functions_by_name.contains_key(&callee_name) {
            debug!(
                "enqueue_reachable_function: cannot find {} in functions_by_name.",
                callee_name
            );
            return;
        }

        if should_skip_function_body(&callee_name) {
            debug!("[PAG] skip visiting function body: {}", callee_name);
            return;
        }

        debug!("[PAG] enqueue newly reachable function: {}", callee_name);

        self.pending_functions
            .push_back((callee_name, callee_context));
    }

    /// simple heuristics to link return value and argument together  
    /// when we cannot find function body in function_by_names/types
    /// TODO: we only handle llm related apis here
    fn handle_bodyless_call(
        &mut self,
        callee_name: &str,
        callsite_kind: &PACallSiteKind<'m>,
        caller_name: &str,
        block_name: &str,
        caller_context: &PAContext,
        source_loc: Option<PASourceLocation>,
    ) -> bool {
        if !is_llm_api_function(callee_name) {
            return false;
        }

        let arguments = self.get_callsite_arguments(callsite_kind);

        // Case 1:
        // call void @foo(ptr sret(...) %dst, ptr %src)
        //
        // Model:
        // %src --Copy--> %dst
        if arguments.len() == 2 {
            if let Some((sret_idx, sret)) = first_pointer_like_sret_arg(arguments) {
                let src_idx = if sret_idx == 0 { 1 } else { 0 };

                let (sret_arg, _) = &arguments[sret_idx];
                let (src_arg, _) = &arguments[src_idx];

                self.add_pag_edge(
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(src_arg), caller_name),
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(sret_arg), caller_name),
                    PAEdgeKind::Copy,
                    caller_name.to_string(),
                    block_name.to_string(),
                    caller_context.clone(),
                    source_loc.clone(),
                );

                return true;
            }
        }

        // Case 2:
        // %result = call @foo(%arg)
        //
        // Model:
        // %arg --Copy--> %result
        if arguments.len() == 1 {
            if let Some(result) = self.get_callsite_result(callsite_kind) {
                let (arg, _) = &arguments[0];

                self.add_pag_edge(
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(arg), caller_name),
                    self.get_nodekind_for_value_ref(
                        PAValueRef::Name {
                            name: result,
                            ty: None,
                        },
                        caller_name,
                    ),
                    PAEdgeKind::Copy,
                    caller_name.to_string(),
                    block_name.to_string(),
                    caller_context.clone(),
                    source_loc.clone(),
                );

                return true;
            }
        }

        false
    }

    /// this function does the following:
    /// Direct call: check/add call edge in call_graph.
    /// Indirect call: add PAG edge from function pointer node so callee discovery is re-run when function pointer points-to changes.
    /// Receiver-based call: add PAG edge from receiver pointer node so callee discovery is re-run when receiver points-to changes.
    /// Add actual→formal, return→lhs, and receiver/self edges.
    fn add_edges_for_call(
        &mut self,
        caller_name: &str,
        block_name: &str,
        callsite_kind: PACallSiteKind<'m>,
        caller_context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) {
        let function_operand = self.callsite_function_operand(&callsite_kind);
        let Some(direct_callee) = function_operand else {
            debug!(
                "[PAG] add_call_edges: cannot find function operand for callsite_kind = {:?}",
                callsite_kind
            );
            return;
        };

        let callee_name = direct_callee_name(direct_callee);

        let (callsite_id, callsite) = self.register_callsite(
            caller_name.to_string(),
            block_name.to_string(),
            callsite_kind.clone(),
            callee_name.clone(),
            caller_context.clone(),
            source_loc.clone(),
        );

        // ------------------------------------------------------------
        // 1. Direct call: make sure call graph has caller -> callee.
        // ------------------------------------------------------------
        if let Some(callee_name) = callee_name {
            // handle special functions if exists
            // TODO: they are fine with caller_context for now
            if self.handle_special_rust_functions(
                &callee_name,
                caller_name,
                block_name,
                &callsite_kind,
                callsite_id,
                caller_context.clone(), // <- here
                source_loc.clone(),
            ) {
                return;
            }

            let callee_func = self
                .functions_by_name
                .get(util::normalize_function_name(callee_name.as_str()))
                .copied();

            // normal flow when context mode is kobj or kmix
            // we need to postpone the handling of callee to
            // obtain the receiver object as context in solver later
            // so we creat an edge here and return
            if self.create_direct_call_edge(
                caller_name,
                block_name,
                callsite_id,
                callee_name.clone(),
                callee_func,
                source_loc.clone(),
            ) {
                return;
            }

            // normal flow when context mode is insensitive or kcfa
            if let Some(callee_func) = callee_func {
                let callee_name = callee_func.name.as_str();
                let callee_context: PAContext =
                    self.get_callee_context(&callee_name, callsite_id, None);

                self.add_cg_edge(
                    caller_name,
                    caller_context.clone(),
                    callee_name,
                    callee_context.clone(),
                );

                self.enqueue_reachable_function(callee_name, callee_context.clone());

                self.add_constraints_for_call(
                    caller_name,
                    caller_context.clone(),
                    block_name,
                    callsite,
                    callee_func,
                    callee_context.clone(),
                    source_loc.clone(),
                );
            } else {
                debug!(
                    "[PAG] add_edges_for_call: cannot find function with name {} from functions_by_name",
                    callee_name.clone()
                );

                self.handle_bodyless_call(
                    &callee_name,
                    &callsite_kind,
                    caller_name,
                    block_name,
                    &caller_context,
                    source_loc.clone(),
                );
            }

            return;
        }

        // ------------------------------------------------------------
        // 2. Indirect call through function pointer.
        //
        // function_operand -[IndirectCall]-> indirect_target
        //
        // Whenever pts(function_operand) changes, solver should process
        // this edge and update callees.
        // ------------------------------------------------------------
        self.add_pag_edge_w_diff_contexts(
            self.get_nodekind_for_value_ref(
                PAValueRef::Operand(direct_callee),
                &caller_name.clone(),
            ),
            PANodeKind::IndirectCallTarget {
                caller: caller_name.to_string(),
                block: block_name.to_string(),
                callsite_id: callsite_id,
            },
            PAEdgeKind::IndirectCall { callsite_id },
            caller_name.to_string(),
            block_name.to_string(),
            caller_context.clone(),
            caller_context.clone(),
            source_loc.clone(),
        );

        // ------------------------------------------------------------
        // 3. Receiver-based dispatch.
        //     receiver -[ReceiverCall]-> target (unknown)
        // LLVM IR has no explicit receiver, but Rust/C++ method calls often pass
        // self/this as the first pointer-like argument. We model the first
        // pointer-like argument as receiver for indirect calls only.
        // ------------------------------------------------------------
        let arguments = self.get_callsite_arguments(&callsite_kind);

        if let Some((idx, receiver_arg)) = first_pointer_like_non_sret_arg_index(arguments) {
            self.add_pag_edge(
                self.get_nodekind_for_value_ref(PAValueRef::Operand(receiver_arg), caller_name),
                PANodeKind::ReceiverObject {
                    caller: util::normalize_function_name(caller_name).to_string(),
                    block: block_name.to_string(),
                    callsite_id: callsite_id,
                    self_idx: idx,
                },
                PAEdgeKind::ReceiverCall { callsite_id },
                caller_name.to_string(),
                block_name.to_string(),
                caller_context.clone(),
                source_loc.clone(),
            );
        } else {
            debug!(
                "[PAG] ReceiverDispatch: no receiver arg found for callsite {}",
                callsite_id
            );
        }

        // the following too conservative and expensive. skip
        if !self.config.on_the_fly {
            // ------------------------------------------------------------
            // 4. Also add edges for callees already known by call graph.
            // ------------------------------------------------------------
            let known_callees: Vec<String> = self
                .call_graph
                .callees(caller_name)
                .map(|s| s.to_string())
                .collect();

            for callee_name in known_callees {
                if let Some(callee_func) = self.functions_by_name.get(callee_name.as_str()) {
                    self.add_constraints_for_call(
                        caller_name,
                        caller_context.clone(),
                        block_name,
                        callsite.clone(),
                        callee_func,
                        caller_context.clone(),
                        source_loc.clone(),
                    );
                }
            }
        }
    }

    fn get_callsite_arguments(
        &mut self,
        kind: &PACallSiteKind<'m>,
    ) -> &'m Vec<(llvm_ir::Operand, Vec<llvm_ir::function::ParameterAttribute>)> {
        match kind {
            PACallSiteKind::Call(call) => &call.arguments,
            PACallSiteKind::Invoke(invoke) => &invoke.arguments,
        }
    }

    fn get_callsite_result(&mut self, kind: &PACallSiteKind<'m>) -> Option<&'m llvm_ir::Name> {
        match kind {
            PACallSiteKind::Call(call) => call.dest.as_ref(),
            PACallSiteKind::Invoke(invoke) => Some(&invoke.result),
        }
    }

    fn get_callsite_context_elem(
        &self,
        caller: &str,
        block: &str,
        callsite_id: usize,
    ) -> PAContextElem {
        PAContextElem::CallSite {
            caller: util::normalize_function_name(caller).to_string(),
            block: block.to_string(),
            callsite_id,
        }
    }

    fn get_object_context_elem(&self, receiver_obj: PANodeId) -> Option<PAContextElem> {
        let Some(node) = self.nodes.get(&receiver_obj) else {
            panic!("no node for node id = {}", receiver_obj);
        };

        match &node.kind {
            PANodeKind::HeapObject {
                function, block, ..
            } => {
                let fname = function.clone();
                return Some(PAContextElem::Object {
                    kind: PAObjectContextKind::Allocation,
                    function: util::normalize_function_name(&fname).to_string(),
                    block: block.clone(),
                    id: receiver_obj,
                });
            }

            PANodeKind::AllocaObject {
                function, block, ..
            } => {
                let fname = function.clone();
                return Some(PAContextElem::Object {
                    kind: PAObjectContextKind::Allocation,
                    function: util::normalize_function_name(&fname).to_string(),
                    block: block.clone(),
                    id: receiver_obj,
                });
            }

            _ => {
                debug!(
                    "[CTX] no allocation context for object n{} kind={:?}",
                    receiver_obj, &node.kind
                );
                None
            }
        }
    }

    /// compute callee_context by applying different context policies
    /// see PAContextSelectPolicy
    fn get_callee_context(
        &self,
        callee_name: &str,
        callsite_id: usize,
        receiver_obj_id: Option<PANodeId>,
    ) -> PAContext {
        if self.config.context_mode == PAContextMode::Insensitive || self.config.default_k == 0 {
            return PAContext::global();
        }

        let Some(callsite) = self.callsites.get(&callsite_id) else {
            panic!("cannot find callsite for callsite_id = {}", callsite_id);
        };

        let caller_name = &callsite.caller.clone();
        let block_name = &callsite.block.clone();
        let caller_context = &callsite.context;
        let mut callee_context = caller_context.clone().filtered_for_mode(&self.config);

        // use context policy, see PAContextSelectPolicy
        let create = match self.config.policy {
            PAContextSelectPolicy::Default => !should_skip_function_context(callee_name),
            PAContextSelectPolicy::AppOnly => {
                self.app_crate.is_empty() || self.is_from_app_crate(callee_name)
            }

            // TODO: we may not need this context creating for AFG
            PAContextSelectPolicy::AFG => {
                // // TODO: do we need so complex matching?
                // let matched = if let Some((llm, ac)) = self.config.context_signatures.as_ref() {
                //     crate::context_finder::match_callsite(
                //         callee_name,
                //         caller_name, // this is not used
                //         block_name,  // this is not used
                //         llm,
                //         ac,
                //     )
                // } else {
                //     None
                // };

                // // for debugging, print the matched context if any
                // if let Some(context_point) = matched.clone() {
                //     println!(
                //         "[AFG] hit context = {} with category = {:?} through strategy = {}",
                //         context_point.matched_fn_name,
                //         context_point.category,
                //         context_point.strategy
                //     );
                // }

                // matched.is_some()

                false
            }
        };

        // For KCFA / KMixed
        if create {
            let elem = self.get_callsite_context_elem(caller_name, block_name, callsite_id);
            callee_context = callee_context.push_with_config(elem, &self.config);
        }

        // For Kobj / KMixed.
        if let Some(receiver_obj) = receiver_obj_id {
            // TODO: we may need to use receiver_obj's type as filter, not just callee_name
            if create {
                if let Some(elem) = self.get_object_context_elem(receiver_obj) {
                    callee_context = callee_context.push_with_config(elem, &self.config);
                }
            }
        } else {
            debug!("no receiver_obj_id for receiver-dispatched call.");
        };

        debug!(
            "[PAG] select context: function {} -> context {:?}",
            callee_name, callee_context
        );

        if create && self.config.policy == PAContextSelectPolicy::AFG {
            println!(
                "[AFG] select context: function {} -> context {:?}",
                callee_name, callee_context
            )
        }

        callee_context.filtered_for_mode(&self.config)
    }

    fn is_from_app_crate(&self, function_name: &str) -> bool {
        function_name.contains(&self.app_crate)
    }

    fn add_constraints_for_call(
        &mut self,
        caller_name: &str,
        caller_context: PAContext,
        block_name: &str,
        callsite: PACallSite<'m>,
        callee: &'m llvm_ir::Function,
        callee_context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) {
        let callee_name = callee.name.as_str();
        let arguments = self.get_callsite_arguments(&callsite.kind);
        let mut idx2arg_nodeid: HashMap<usize, PANodeId> = HashMap::new();

        debug!("[PAG] add_constraints_for_call: callee = {}", callee_name);

        // ------------------------------------------------------------
        // actual_i -> formal_i
        // this should already include receiver/self edge:
        //
        //     receiver_actual -> formal_0
        //
        // ------------------------------------------------------------
        for (idx, (actual_arg, _attrs)) in arguments.iter().enumerate() {
            if let Some(formal) = callee.parameters.get(idx) {
                let (src_id, dst_id) = self.add_pag_edge_w_diff_contexts(
                    self.get_nodekind_for_value_ref(PAValueRef::Operand(actual_arg), caller_name),
                    self.get_nodekind_for_value_ref(PAValueRef::Parameter(formal), callee_name),
                    PAEdgeKind::Copy,
                    caller_name.to_string(),
                    block_name.to_string(),
                    caller_context.clone(),
                    callee_context.clone(),
                    source_loc.clone(),
                );

                debug!(
                    "[PAG][args] caller={} callee={} idx={} actual={:?} formal={} src_id={} dst_id={} caller_ctx={:?} callee_ctx={:?}",
                    caller_name,
                    callee_name,
                    idx,
                    actual_arg,
                    formal.name,
                    src_id,
                    dst_id,
                    caller_context,
                    callee_context,
                );

                idx2arg_nodeid.insert(idx, src_id);
            }
        }

        // // ------------------------------------------------------------
        // // receiver/self edge.
        // //
        // // For Rust methods, the self receiver is usually the first pointer-like
        // // argument. We explicitly add:
        // //
        // //     receiver_actual -> formal_0
        // //
        // // if formal_0 exists.
        // // ------------------------------------------------------------
        // if let Some((self_idx, self_param)) = first_pointer_like_self_parameter(callee) {
        //     if let Some((receiver_arg, _attr)) = arguments.get(self_idx) {
        //         self.add_pag_edge_w_diff_contexts(
        //             self.get_nodekind_for_value_ref(PAValueRef::Operand(receiver_arg), caller_name),
        //             self.get_nodekind_for_value_ref(PAValueRef::Parameter(self_param), callee_name),
        //             PAEdgeKind::Copy,
        //             caller_name.to_string(),
        //             block_name.to_string(),
        //             caller_context.clone(),
        //             callee_context.clone(),
        //         );
        //     }
        // }

        // ------------------------------------------------------------
        // callee formal sret -> function_return(callee)
        // ------------------------------------------------------------
        if let Some((_idx, formal_sret)) = first_pointer_like_sret_parameter(callee) {
            debug!(
                "[PAG] found sret = {:?} in callee param = {}",
                formal_sret, callee_name
            );

            self.add_pag_edge_w_diff_contexts(
                self.get_nodekind_for_value_ref(PAValueRef::Parameter(formal_sret), callee_name),
                PANodeKind::FunctionReturn {
                    function: callee_name.to_string(),
                },
                PAEdgeKind::Copy,
                caller_name.to_string(),
                block_name.to_string(),
                // Both nodes belong to the callee context.
                callee_context.clone(),
                callee_context.clone(),
                source_loc.clone(),
            );
        }

        // ------------------------------------------------------------
        // function_return(callee) -> lhs
        // ------------------------------------------------------------
        let result_id: Option<PANodeId> = if let Some(result_name) =
            self.get_callsite_result(&callsite.kind)
        {
            // Normal LLVM return:
            //
            // FunctionReturn(callee) -> caller lhs
            let (_return_id, lhs_id) = self.add_pag_edge_w_diff_contexts(
                PANodeKind::FunctionReturn {
                    function: callee_name.to_string(),
                },
                self.get_nodekind_for_value_ref(
                    PAValueRef::Name {
                        name: result_name,
                        ty: None,
                    },
                    caller_name,
                ),
                PAEdgeKind::Copy,
                caller_name.to_string(),
                block_name.to_string(),
                callee_context.clone(),
                caller_context.clone(),
                source_loc.clone(),
            );

            // The result of this callsite is the caller-side lhs.
            Some(lhs_id)
        } else if let Some((idx, actual_sret_operand)) = first_pointer_like_sret_arg(arguments) {
            // Hidden sret return:
            //
            // FunctionReturn(callee) -> caller actual sret operand
            //
            // Example:
            // invoke void @build(ptr sret(...) %_17, ...)
            //
            // The call result is caller local %_17.
            let actual_sret_kind = self
                .get_nodekind_for_value_ref(PAValueRef::Operand(actual_sret_operand), caller_name);

            debug!(
                "[PAG] found sret = {} in argument when calling = {}",
                actual_sret_operand, callee_name
            );

            let (_return_id, actual_sret_id) = self.add_pag_edge_w_diff_contexts(
                PANodeKind::FunctionReturn {
                    function: callee_name.to_string(),
                },
                actual_sret_kind,
                PAEdgeKind::Copy,
                caller_name.to_string(),
                block_name.to_string(),
                callee_context.clone(),
                caller_context.clone(),
                source_loc.clone(),
            );

            Some(actual_sret_id)
        } else {
            None
        };
        // normal flow ends here

        // for AFG, check if the callsite matches any context signature
        let matched = (self.config.policy == PAContextSelectPolicy::AFG)
            .then(|| self.config.context_signatures.as_ref())
            .flatten()
            .and_then(|(llm, ac, data)| {
                crate::signature::match_callsite(
                    callee_name,
                    caller_name,
                    block_name,
                    llm,
                    ac,
                    data,
                )
            });

        // for debugging, print the matched context if any
        if let Some(context_point) = matched {
            println!(
                "[AFG] hit function = {} with category = {:?} through strategy = {}",
                context_point.matched_fn_name, context_point.category, context_point.strategy
            );

            // let mut entries: Vec<(usize, PANodeId)> = idx2arg_nodeid
            //     .iter()
            //     .map(|(&idx, &node_id)| (idx, node_id))
            //     .collect();

            // entries.sort_by_key(|(idx, _)| *idx);

            // let arg_node_ids: Vec<PANodeId> =
            //     entries.into_iter().map(|(_, node_id)| node_id).collect();

            // select arguments relate to request/prompt and return/sret
            let mut related_nodeids: Vec<PANodeId> = Vec::new();
            if let Some(prompt_idx) = context_point.prompt_arg_index {
                if let Some(prompt_nodeid) = idx2arg_nodeid.get(&prompt_idx) {
                    related_nodeids.push(*prompt_nodeid);
                }
            }

            if let Some(request_idx) = context_point.request_index {
                if let Some(request_nodeid) = idx2arg_nodeid.get(&request_idx) {
                    related_nodeids.push(*request_nodeid);
                }
            }

            // special handling for authentication, llm-api, and data-store categories
            if let Some(category) = context_point.category.clone() {
                let kind = match category.as_str() {
                    // access-control decisions
                    "authentication" | "authorization" | "policy-enforcement"
                    | "raw-http" => Some(SemanticPointKind::AccessControl { category }),

                    // prompt-construction api call
                    "llm-api-prompt" => Some(SemanticPointKind::LlmPrompt { category }),

                    // external llm api call (bare "llm-api" is the pre-migration
                    // category still used by several catalog entries)
                    "llm-api" | "llm-api-chat" => Some(SemanticPointKind::LlmCall {
                        category,
                        provider: None,
                    }),

                    // shared data-store access (read = leak-exposing, write = the
                    // stored data); the category string carries the direction.
                    "data-read" | "data-write" => {
                        Some(SemanticPointKind::DataAccess { category })
                    }

                    // Unknown category: warn and skip rather than crashing the
                    // analysis, so the evolving catalog can add categories safely.
                    _ => {
                        eprintln!(
                            "[AFG] warning: skipping unhandled context category = {:?} for callsite {:?}",
                            category, callsite
                        );
                        None
                    }
                };

                if let Some(kind) = kind {
                    let semantic_point = SemanticPoint {
                        callsite_id: callsite.id,
                        kind,
                        security_point: context_point,

                        caller: caller_name.to_string(),
                        block: block_name.to_string(),
                        callee: Some(callee_name.to_string()),
                        caller_context: caller_context.clone(),

                        argument_nodes: related_nodeids,
                        result_node: result_id,
                    };

                    println!("[AFG] register semantic point = {}", semantic_point);

                    self.semantic_points.push(semantic_point);
                }
            }
        }
    }

    /// add cg edge to self.call_graph (with context)
    fn add_cg_edge(
        &mut self,
        caller_name: &str,
        caller_context: PAContext,
        callee_name: &str,
        callee_context: PAContext,
    ) -> bool {
        let caller = format!("{} (ctx::{:?})", caller_name, caller_context);
        let callee = format!("{} (ctx::{:?})", callee_name, callee_context);
        if self.call_graph.add_call_edge(caller, callee) {
            debug!(
                "[PAG Call] add direct call edge: {} -> {}",
                caller_name, callee_name
            );

            return true;
        }

        false
    }

    /// create DirectCall edge when using kobj or kmix only
    fn create_direct_call_edge(
        &mut self,
        caller_name: &str,
        block_name: &str,
        callsite_id: usize,
        callee_name: String,
        callee_func: Option<&Function>,
        source_loc: Option<PASourceLocation>,
    ) -> bool {
        if !matches!(
            self.config.context_mode,
            PAContextMode::KObject | PAContextMode::KMixed
        ) {
            return false;
        }

        let Some(callsite) = self.callsites.get(&callsite_id).cloned() else {
            panic!("cannot find callsite with id = {}", callsite_id);
        };

        let Some(callee_func) = callee_func else {
            debug!(
                "[PAG] create_direct_call_edge: cannot find function with name {} from functions_by_name",
                callee_name
            );
            return false;
        };

        // check if any param is %self pointer type
        let Some((self_idx, self_param)) = first_pointer_like_self_parameter(callee_func) else {
            return false;
        };

        debug!(
            "[PAG] direct call: found %self ptr = {:?} for function = {}",
            self_param, callee_name
        );

        let args = self.get_callsite_arguments(&callsite.kind);
        let Some((receiver_arg, _attrs)) = args.get(self_idx) else {
            println!(
                "cannot find receiver argument with idx = {} in callsite = {:?}",
                self_idx,
                callsite.clone(),
            );
            return false;
        };

        // add direct call edge
        self.add_pag_edge(
            self.get_nodekind_for_value_ref(PAValueRef::Operand(receiver_arg), &callee_name),
            PANodeKind::ReceiverObject {
                caller: util::normalize_function_name(caller_name).to_string(),
                block: callsite.block.clone(),
                callsite_id: callsite.id,
                self_idx,
            },
            PAEdgeKind::DirectCall {
                callsite_id,
                self_idx,
            },
            caller_name.to_string(),
            block_name.to_string(),
            callsite.context.clone(),
            source_loc,
        );

        true
    }

    ///////////////// solvers below this point /////////////////

    /// Solve the pointer assignment graph using Andersen's algorithm until a fixed point is reached.
    pub fn solve(&mut self) {
        let mut iteration = 0usize;

        loop {
            if self.config.on_the_fly {
                self.discover_reachable_constraints();
            }

            if self.worklist.is_empty() && self.pending_functions.is_empty() {
                break;
            }

            iteration += 1;

            // sort the edges topologically based on their source nodes (lhs)
            let items: Vec<PAWorkItem> = self.worklist.drain(..).collect();
            let items = self.topo_sort_worklist(items);

            println!(
                "[PAG Solver] iteration {}: nodes={}, edges={}, worklist items={}",
                iteration,
                self.nodes.len(),
                self.edges.len(),
                items.len(),
            );

            for item in items {
                let edge = item.edge;

                // debug!(
                //     "[PAG Solver] process item: n{} -[{:?}]-> n{} delta={:?}",
                //     edge.src, edge.kind, edge.dst, item.delta,
                // );

                match edge.kind {
                    PAEdgeKind::AddressOf => self.solve_address_of(edge.src, edge.dst),

                    PAEdgeKind::Copy => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_copy(edge.src, edge.dst, &delta)
                    }

                    PAEdgeKind::Load => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_load(edge, &delta)
                    }

                    PAEdgeKind::Store => match item.delta {
                        PAWorkDelta::Src(delta) => self.solve_store_src(edge, &delta),

                        PAWorkDelta::Dst(delta) => self.solve_store_dst(edge, &delta),

                        PAWorkDelta::Full => false,
                    },

                    PAEdgeKind::GEP { ref indices } => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_gep(edge.src, edge.dst, indices, &delta)
                    }

                    PAEdgeKind::ByteOffsetGEP { offset } => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_byte_offset_gep(edge.src, edge.dst, offset, &delta)
                    }

                    PAEdgeKind::UnknownOffsetGEP => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_unknown_offset_gep(edge.src, edge.dst, &delta)
                    }

                    PAEdgeKind::BitCast => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_bitcast(edge.src, edge.dst, &delta)
                    }

                    PAEdgeKind::AddrSpaceCast => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_addr_space_cast(edge.src, edge.dst, &delta)
                    }

                    PAEdgeKind::IntToPtr => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_int2pointer(edge.src, edge.dst, &delta)
                    }

                    PAEdgeKind::Phi | PAEdgeKind::Select => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_merge(edge.src, edge.dst, &delta)
                    }

                    PAEdgeKind::IndirectCall { callsite_id } => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_indirect_call(edge, callsite_id, &delta)
                    }

                    PAEdgeKind::ReceiverCall { callsite_id } => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_receiver_call(edge, callsite_id, &delta)
                    }

                    PAEdgeKind::DirectCall {
                        callsite_id,
                        self_idx,
                    } => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_direct_call(callsite_id, self_idx, &delta)
                    }

                    PAEdgeKind::MemCopy => match item.delta {
                        PAWorkDelta::Src(delta) => {
                            self.solve_memcpy_src(edge.src, edge.dst, &delta)
                        }

                        PAWorkDelta::Dst(delta) => {
                            self.solve_memcpy_dst(edge.src, edge.dst, &delta)
                        }

                        PAWorkDelta::Full => false,
                    },

                    PAEdgeKind::AggregateCopy => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_copy(edge.src, edge.dst, &delta)
                    }

                    PAEdgeKind::ExtractCopy { ref field } => {
                        let PAWorkDelta::Src(delta) = item.delta else {
                            continue;
                        };

                        self.solve_extract_copy(&edge, field, &delta)
                    }
                };
            }
        }

        println!(
            "[PAG Solver] reached fixed point after {} iteration(s)",
            iteration
        );
    }

    /// Simple sort (not topo sort) for now:
    ///  we merge the deltas from different iterms but for the same edge
    ///
    /// TODO: Sort the given edges topologically based on their source nodes (lhs).
    ///  If there are cycles, the remaining nodes will be appended in deterministic order.
    fn topo_sort_worklist(&self, mut items: Vec<PAWorkItem>) -> Vec<PAWorkItem> {
        items.sort_by(|a, b| {
            work_item_lhs(a)
                .cmp(&work_item_lhs(b))
                .then_with(|| {
                    edge_kind_sort_key(&a.edge.kind).cmp(&edge_kind_sort_key(&b.edge.kind))
                })
                .then_with(|| a.edge.src.cmp(&b.edge.src))
                .then_with(|| a.edge.dst.cmp(&b.edge.dst))
                .then_with(|| delta_kind_rank(&a.delta).cmp(&delta_kind_rank(&b.delta)))
        });

        merge_sorted_work_items(items)
    }

    fn add_points_to_facts(
        &mut self,
        node: PANodeId,
        diff: &BTreeSet<PANodeId>,
    ) -> BTreeSet<PANodeId> {
        let Some(n) = self.nodes.get_mut(&node) else {
            return BTreeSet::new();
        };

        let mut delta = BTreeSet::new();

        for p in diff {
            if n.points_to.insert(*p) {
                delta.insert(*p);
            }
        }

        delta
    }

    fn add_points_to_and_enqueue(
        &mut self,
        changed_node: PANodeId,
        diff: &BTreeSet<PANodeId>,
    ) -> bool {
        let delta = self.add_points_to_facts(changed_node, diff);
        if delta.is_empty() {
            return false;
        }

        // debug!("    delta = {:?}", delta);

        // most edges where changed_node is src/lhs.
        if let Some(edges) = self.lhs2edges.get(&changed_node).cloned() {
            for edge in edges {
                self.worklist.push(PAWorkItem {
                    edge,
                    delta: PAWorkDelta::Src(delta.clone()),
                });
            }
        }

        // Store edges where changed_node is dst pointer.
        if let Some(edges) = self.store_dst_edges.get(&changed_node).cloned() {
            for edge in edges {
                self.worklist.push(PAWorkItem {
                    edge,
                    delta: PAWorkDelta::Dst(delta.clone()),
                });
            }
        }

        // Memcopy edges where changed_node is dst ptr
        if let Some(edges) = self.memcpy_dst_edges.get(&changed_node).cloned() {
            for edge in edges {
                self.worklist.push(PAWorkItem {
                    edge,
                    delta: PAWorkDelta::Dst(delta.clone()),
                });
            }
        }

        true
    }

    /// Address-of constraint:
    ///     dst = &src   
    /// we create:
    ///     src -[AddressOf]-> dst
    /// So:
    ///     pts(dst) += {src}
    fn solve_address_of(&mut self, src: PANodeId, dst: PANodeId) -> bool {
        debug!(
            "[PAG Solver] solve_address_of: pts(n{}) += {{n{}}}",
            dst, src
        );

        let pts = BTreeSet::from([src]);
        self.add_points_to_and_enqueue(dst, &pts)
    }

    /// Copy constraint:
    ///     dst = src
    /// we create:
    ///    src -[Copy]-> dst
    /// So:
    ///     pts(dst) += pts(src)
    fn solve_copy(&mut self, src: PANodeId, dst: PANodeId, delta: &BTreeSet<PANodeId>) -> bool {
        if delta.is_empty() {
            return false;
        }

        debug!(
            "[PAG Solver] solve_copy: pts(n{}) += pts(n{})    delta={:?}",
            dst, src, delta
        );

        self.add_points_to_and_enqueue(dst, delta)
    }

    /// Load constraint:
    ///     dst = *src
    /// we create:
    ///     src -[Load]-> dst
    /// So:
    ///     for each obj in pts(src):
    ///         pts(dst) += pts(obj)
    /// which is equivalent to: if src points to objects o1, o2, ...
    /// then:
    ///     pts(dst) += pts(o1)
    ///     pts(dst) += pts(o2)
    /// so, we create:
    ///     obj -[Copy]-> dst
    fn solve_load(&mut self, edge: PAEdge, delta: &BTreeSet<PANodeId>) -> bool {
        let src = edge.src;
        let dst = edge.dst;
        let mut changed = false;

        for obj in delta {
            if !self.object_may_hold_pointer_value(*obj) {
                continue;
            }

            // For dst = *src and obj ∈ pts(src),
            // create obj -[Copy]-> dst.
            let edge = PAEdge {
                src: *obj,
                dst: dst,
                kind: PAEdgeKind::Copy,
                function: edge.function.clone(),
                block: edge.block.clone(),
            };

            if self
                .edge_index
                .contains(&(edge.src, edge.dst, edge.kind.clone()))
            {
                continue;
            }

            // insert dynamic copy edge
            self.lhs2edges
                .entry(edge.src)
                .or_default()
                .push(edge.clone());
            self.edges.push(edge.clone());
            self.edge_index
                .insert((edge.src, edge.dst, edge.kind.clone()));

            let seed_delta = self.points_to_snapshot(edge.src);
            if !seed_delta.is_empty() {
                // debug!(
                // "[PAG Solver] solve_load: create dynamic Copy edge n{} -[Copy]-> n{}    delta={:?}",
                // edge.src, edge.dst, seed_delta);

                debug!(
                    "[PAG Solver] solve_load: create dynamic Copy edge n{} -[Copy]-> n{} seed pts(n{})={:?}; addr=n{} pts(addr)={:?}",
                    edge.src,
                    edge.dst,
                    edge.src,
                    seed_delta,
                    src,
                    self.points_to_snapshot(src),
                );

                self.worklist.push(PAWorkItem {
                    edge,
                    delta: PAWorkDelta::Src(seed_delta),
                });
            }

            changed = true;
        }

        changed
    }

    /// ExtractValue constraint:
    ///     dst = extractvalue src, field
    /// for each aggregate field slot obj in pts(src) matching field:
    ///     obj -[Copy]-> dst
    fn solve_extract_copy(
        &mut self,
        edge: &PAEdge,
        field: &[u64],
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        let dst = edge.dst;
        let mut changed = false;

        for obj in delta {
            if !self.aggregate_field_matches(*obj, field) {
                continue;
            }

            let edge = PAEdge {
                src: *obj,
                dst,
                kind: PAEdgeKind::Copy,
                function: edge.function.clone(),
                block: edge.block.clone(),
            };

            if self
                .edge_index
                .contains(&(edge.src, edge.dst, edge.kind.clone()))
            {
                continue;
            }

            self.lhs2edges.entry(*obj).or_default().push(edge.clone());
            self.edges.push(edge.clone());
            self.edge_index
                .insert((edge.src, edge.dst, edge.kind.clone()));

            let seed_delta = self.points_to_snapshot(*obj);
            if !seed_delta.is_empty() {
                self.worklist.push(PAWorkItem {
                    edge,
                    delta: PAWorkDelta::Src(seed_delta),
                });
            }

            changed = true;
        }

        changed
    }

    fn aggregate_field_matches(&self, obj: PANodeId, field: &[u64]) -> bool {
        return matches!(
            self.nodes.get(&obj).map(|n| &n.kind),
            Some(PANodeKind::AggregateField { field: f, .. }) if f.as_slice() == field
        );
    }

    /// Store constraint:
    ///     *dst = src
    /// we create:
    ///     dst -[Store]-> src
    /// So:
    ///     for each obj in pts(dst):
    ///         pts(obj) += pts(src)
    /// which is equivalent to: if dst points to objects o1, o2, ...
    /// then:
    ///     pts(o1) += pts(src)
    ///     pts(o2) += pts(src)
    /// so, we create:
    ///     src -[Copy]-> obj
    /// !!! NOTE: this is the only case where dst is lhs, be careful
    /// when pts(dst) changes:
    /// dst newly points to some object obj.
    /// Then the existing src values should flow to obj.
    fn solve_store_dst(&mut self, edge: PAEdge, dst_delta: &BTreeSet<PANodeId>) -> bool {
        if dst_delta.is_empty() {
            return false;
        }

        let src = edge.src;
        let dst = edge.dst;

        let src_objs = self.points_to_snapshot(src);
        self.materialize_store_dynamic_edges(src, dst_delta, &src_objs, &edge)
    }

    /// when pts(src) changes
    /// src has new values, and dst already points to objects.
    /// The already-created copy edges src -> obj will propagate src.diff.
    fn solve_store_src(&mut self, edge: PAEdge, src_delta: &BTreeSet<PANodeId>) -> bool {
        if src_delta.is_empty() {
            return false;
        }

        let src = edge.src;
        let dst = edge.dst;

        let dst_objs = self.points_to_snapshot(dst);
        self.materialize_store_dynamic_edges(src, &dst_objs, src_delta, &edge)
    }

    fn materialize_store_dynamic_edges(
        &mut self,
        src: PANodeId,
        dst_objs: &BTreeSet<PANodeId>,
        delta: &BTreeSet<PANodeId>,
        store_edge: &PAEdge,
    ) -> bool {
        let mut changed = false;

        for dst_obj in dst_objs {
            if !self.object_may_hold_pointer_value(*dst_obj) {
                continue;
            }

            let dyn_edge = PAEdge {
                src,
                dst: *dst_obj,
                kind: PAEdgeKind::Copy,
                function: store_edge.function.clone(),
                block: store_edge.block.clone(),
            };

            if self
                .edge_index
                .contains(&(dyn_edge.src, dyn_edge.dst, dyn_edge.kind.clone()))
            {
                continue;
            }

            self.lhs2edges
                .entry(dyn_edge.src)
                .or_default()
                .push(dyn_edge.clone());

            self.edges.push(dyn_edge.clone());
            self.edge_index
                .insert((dyn_edge.src, dyn_edge.dst, dyn_edge.kind.clone()));

            debug!(
                "[PAG Solver] solve_store: create dynamic Copy edge n{} -[Copy]-> n{} delta={:?}",
                dyn_edge.src, dyn_edge.dst, delta,
            );

            if !delta.is_empty() {
                self.worklist.push(PAWorkItem {
                    edge: dyn_edge,
                    delta: PAWorkDelta::Src(delta.clone()),
                });
            }

            changed = true;
        }

        changed
    }

    fn solve_memcpy_dst(
        &mut self,
        src_ptr: PANodeId,
        _dst_ptr: PANodeId,
        dst_obj_delta: &BTreeSet<PANodeId>,
    ) -> bool {
        if dst_obj_delta.is_empty() {
            return false;
        }

        let src_objs = self.points_to_snapshot(src_ptr);
        if src_objs.is_empty() {
            return false;
        }

        let mut changed_any = false;

        for src_obj in &src_objs {
            if !self.object_may_hold_pointer_value(*src_obj) {
                continue;
            }

            let src_contents = self.points_to_snapshot(*src_obj);
            if src_contents.is_empty() {
                continue;
            }

            for dst_obj in dst_obj_delta {
                if !self.memcpy_may_copy_pointer_contents(*src_obj, *dst_obj) {
                    continue;
                }

                debug!(
                    "[PAG Solver] solve_memcpy (src): create dynamic Copy edge n{} -[Copy]-> n{}    delta={:?}",
                    *src_obj, dst_obj, src_contents
                );

                if self.add_points_to_and_enqueue(*dst_obj, &src_contents) {
                    changed_any = true;
                }
            }
        }

        changed_any
    }

    fn solve_memcpy_src(
        &mut self,
        _src_ptr: PANodeId,
        dst_ptr: PANodeId,
        src_obj_delta: &BTreeSet<PANodeId>,
    ) -> bool {
        if src_obj_delta.is_empty() {
            return false;
        }

        let dst_objs = self.points_to_snapshot(dst_ptr);
        if dst_objs.is_empty() {
            return false;
        }

        let mut changed_any = false;

        for src_obj in src_obj_delta {
            if !self.object_may_hold_pointer_value(*src_obj) {
                continue;
            }

            let src_contents = self.points_to_snapshot(*src_obj);
            if src_contents.is_empty() {
                continue;
            }

            for dst_obj in &dst_objs {
                if !self.memcpy_may_copy_pointer_contents(*src_obj, *dst_obj) {
                    continue;
                }

                debug!(
                    "[PAG Solver] solve_memcpy (src): create dynamic Copy edge n{} -[Copy]-> n{}    delta={:?}",
                    *src_obj, dst_obj, src_contents
                );

                if self.add_points_to_and_enqueue(*dst_obj, &src_contents) {
                    changed_any = true;
                }
            }
        }

        changed_any
    }

    fn solve_gep(
        &mut self,
        src: PANodeId,
        dst: PANodeId,
        indices: &[u64],
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        if delta.is_empty() {
            return false;
        }

        let mut out = BTreeSet::new();

        for base_obj in delta {
            let field_obj = self.get_or_create_field_object(*base_obj, indices);

            if !self.object_may_hold_pointer_value(field_obj) {
                continue;
            }

            debug!(
                "[PAG Solver] solve_gep: base n{} indices={:?} -> field n{}; dst=n{}",
                base_obj, indices, field_obj, dst
            );

            out.insert(field_obj);
        }

        self.add_points_to_and_enqueue(dst, &out)
    }

    fn solve_byte_offset_gep(
        &mut self,
        src: PANodeId,
        dst: PANodeId,
        offset: i64,
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        if delta.is_empty() {
            return false;
        }

        let mut out = BTreeSet::new();

        for base_obj in delta {
            let field_obj = self.get_or_create_byte_offset_field_object(*base_obj, offset);
            out.insert(field_obj);
        }

        self.add_points_to_and_enqueue(dst, &out)
    }

    fn solve_unknown_offset_gep(
        &mut self,
        _src: PANodeId,
        dst: PANodeId,
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        if delta.is_empty() {
            return false;
        }

        let mut out = BTreeSet::new();

        for base_obj in delta {
            let root_base = {
                let Some(base_node) = self.nodes.get(base_obj) else {
                    continue;
                };

                match &base_node.kind {
                    PANodeKind::FieldObject { base, .. } => *base,
                    _ => *base_obj,
                }
            };

            /*
             * Remember that dst depends on every byte-offset field
             * that may ever be discovered for root_base.
             */
            self.unknown_offset_users
                .entry(root_base)
                .or_default()
                .insert(dst);

            /*
             * Add all fields known at this point.
             */
            if let Some(fields) = self.byte_offset_field_objects.get(&root_base) {
                out.extend(fields.iter().copied());
            }
        }

        self.add_points_to_and_enqueue(dst, &out)
    }

    /// BitCast constraint:
    ///     dst = src
    /// we create:
    ///    src -[Copy]-> dst
    /// So:
    ///     pts(dst) += pts(src)
    fn solve_bitcast(&mut self, src: PANodeId, dst: PANodeId, delta: &BTreeSet<PANodeId>) -> bool {
        if delta.is_empty() {
            return false;
        }

        debug!(
            "[PAG Solver] solve_bitcast: pts(n{}) += pts(n{})    delta={:?}",
            dst, src, delta
        );

        self.add_points_to_and_enqueue(dst, delta)
    }

    /// AddrSpaceCast constraint:
    ///     dst = src
    /// we create:
    ///    src -[Copy]-> dst
    /// So:
    ///     pts(dst) += pts(src)
    fn solve_addr_space_cast(
        &mut self,
        src: PANodeId,
        dst: PANodeId,
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        if delta.is_empty() {
            return false;
        }

        debug!(
            "[PAG Solver] solve_addr_space_cast: pts(n{}) += pts(n{})    delta={:?}",
            dst, src, delta
        );

        self.add_points_to_and_enqueue(dst, delta)
    }

    /// IntToPtr constraint:
    ///     skip for now
    fn solve_int2pointer(
        &mut self,
        src: PANodeId,
        dst: PANodeId,
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        return false;
    }

    /// Phi and Select constraint:
    ///     dst = src
    /// we create:
    ///    src -[Copy]-> dst
    /// So:
    ///     pts(dst) += pts(src)
    fn solve_merge(&mut self, src: PANodeId, dst: PANodeId, delta: &BTreeSet<PANodeId>) -> bool {
        if delta.is_empty() {
            return false;
        }

        debug!(
            "[PAG Solver] solve_bitcast: pts(n{}) += pts(n{})    delta={:?}",
            dst, src, delta
        );

        self.add_points_to_and_enqueue(dst, delta)
    }

    fn solve_indirect_call(
        &mut self,
        edge: PAEdge,
        callsite_id: usize,
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        let Some(callsite) = self.callsites.get(&callsite_id).cloned() else {
            return false;
        };

        if callsite.direct_callee.is_some() {
            return false;
        }

        if delta.is_empty() {
            return false;
        }

        let mut changed = false;

        for callee_id in delta {
            let Some(callee_name) = self.get_function_object_from_nodeid(*callee_id) else {
                continue;
            };

            let callee_func = self.functions_by_name.get(callee_name.as_str()).copied();
            let Some(callee_func) = callee_func else {
                continue;
            };

            let callee_name = callee_func.name.as_str();
            let callee_context = self.get_callee_context(callee_name, callsite.id, None);

            if self.add_cg_edge(
                &callsite.caller.clone(),
                callsite.context.clone(),
                callee_name,
                callee_context.clone(),
            ) {
                println!(
                    "[PAG Solver] indirect call discovered: {} -> {}",
                    callsite.caller, callee_func.name
                );

                self.enqueue_reachable_function(callee_name, callee_context.clone());
                changed = true;
            }

            self.add_constraints_for_call(
                &callsite.caller,
                callsite.context.clone(),
                &callsite.block.clone(),
                callsite.clone(),
                callee_func,
                callee_context,
                callsite.source_loc.clone(),
            );
        }

        changed
    }

    fn solve_receiver_call(
        &mut self,
        edge: PAEdge,
        callsite_id: usize,
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        let Some(callsite) = self.callsites.get(&callsite_id).cloned() else {
            return false;
        };

        // TODO: aggressively skip discovering receiver-dispatch calls: this might be wrong for polymophism
        if callsite.direct_callee.is_some() {
            debug!(
                "[PAG Solver] skip receiver resolution for direct callsite: {:?}",
                callsite
            );
            return false;
        }

        if delta.is_empty() {
            return false;
        }

        let mut changed = false;

        for receiver_obj in delta {
            let candidate_callees = self.candidate_callees_for_receiver(*receiver_obj);

            for callee_func in candidate_callees {
                let callee_name = callee_func.name.as_str();
                let callee_context =
                    self.get_callee_context(callee_name, callsite.id, Some(*receiver_obj));

                if self.add_cg_edge(
                    &callsite.caller.clone(),
                    callsite.context.clone(),
                    callee_name,
                    callee_context.clone(),
                ) {
                    println!(
                        "[PAG Solver] indirect call discovered: {} -> {}",
                        callsite.caller, callee_func.name
                    );

                    self.enqueue_reachable_function(callee_name, callee_context.clone());
                    changed = true;
                }

                self.add_constraints_for_call(
                    &callsite.caller,
                    callsite.context.clone(),
                    &callsite.block,
                    callsite.clone(),
                    callee_func,
                    callee_context,
                    callsite.source_loc.clone(),
                );
            }
        }

        changed
    }

    fn solve_direct_call(
        &mut self,
        callsite_id: usize,
        self_idx: usize,
        delta: &BTreeSet<PANodeId>,
    ) -> bool {
        if delta.is_empty() {
            return false;
        }

        let Some(callsite) = self.callsites.get(&callsite_id).cloned() else {
            return false;
        };

        let Some(callee_name) = callsite.direct_callee.clone() else {
            return false;
        };

        let callee_name = util::normalize_function_name(&callee_name);

        let Some(callee_func) = self.functions_by_name.get(callee_name).cloned() else {
            return false;
        };

        let mut changed = false;

        for receiver_obj in delta {
            let callee_context =
                self.get_callee_context(&callee_name, callsite_id, Some(*receiver_obj));

            if self.add_cg_edge(
                &callsite.caller.clone(),
                callsite.context.clone(),
                callee_name,
                callee_context.clone(),
            ) {
                println!(
                    "[PAG Solver] direct call discovered: {} -> {}",
                    callsite.caller, callee_name
                );

                self.enqueue_reachable_function(&callee_name, callee_context.clone());
                changed = true;
            }

            self.add_constraints_for_call(
                &callsite.caller,
                callsite.context.clone(),
                &callsite.block,
                callsite.clone(),
                callee_func,
                callee_context,
                callsite.source_loc.clone(),
            );
        }

        changed
    }

    fn get_function_object_from_nodeid(&self, obj_id: PANodeId) -> Option<String> {
        let obj_node = self.nodes.get(&obj_id)?;

        match &obj_node.kind {
            PANodeKind::FunctionObject { function } => Some(function.clone()),

            // Optional: if your global object may actually refer to a function.
            PANodeKind::GlobalObject { name } => {
                let clean = name.trim_start_matches('@');

                if self.functions_by_name.contains_key(clean) {
                    Some(clean.to_string())
                } else {
                    None
                }
            }

            _ => None,
        }
    }

    /// find callees through vtable/type-based receiver dispatch.
    /// TODO: vtable?
    fn candidate_callees_for_receiver(&self, receiver_obj: PANodeId) -> Vec<&'m llvm_ir::Function> {
        let Some(receiver_node) = self.nodes.get(&receiver_obj) else {
            return Vec::new();
        };

        let Some(receiver_ty) = self.receiver_object_type(receiver_node) else {
            return Vec::new();
        };

        let receiver_type_key = type_key(&receiver_ty);

        debug!(
            "candidate_callees_for_receiver: receiver object n{} has type {}",
            receiver_obj, receiver_type_key
        );

        // heuristics below:
        // i've only seen type NamedStructType has function names, agressively filter here
        let Some(receiver_struct_name) = named_struct_name(&receiver_ty) else {
            return Vec::new();
        };

        debug!(
            "candidate_callees_for_receiver: receiver_ty is NamedStructType: {}",
            receiver_struct_name
        );

        let receiver_type_key = receiver_struct_name.replace("<'_>", "").replace(' ', "");

        let patterns = [
            format!("<{}as", receiver_type_key),
            format!("{}::", receiver_type_key),
        ];

        let mut matches = Vec::new();

        for (mangled_name, func) in &self.functions_by_name {
            let demangled = demangle(mangled_name).to_string();
            let demangled_key = &demangled.replace("<'_>", "").replace(' ', "");

            if patterns.iter().any(|pat| demangled_key.contains(pat)) {
                debug!(
                    "candidate_callees_for_receiver: receiver-method match: type={} function={} demangled={}",
                    receiver_struct_name, mangled_name, demangled
                );

                matches.push(*func);
            }
        }

        matches
    }

    fn receiver_object_type(&self, node: &PANode<'m>) -> Option<llvm_ir::TypeRef> {
        match &node.kind {
            PANodeKind::AllocaObject { allocated_type, .. } => Some((*allocated_type).clone()),

            PANodeKind::SSAValue { function, name, ty } => ty.clone(),

            // PANodeKind::DerefOperand(op) => {
            //     let ptr_ty = operand_type(op)?;
            //     pointee_type_of_pointer(&ptr_ty)
            // }
            _ => None,
        }
    }

    fn register_callsite(
        &mut self,
        caller: String,
        block: String,
        call: PACallSiteKind<'m>,
        direct_callee: Option<String>,
        caller_context: PAContext,
        source_loc: Option<PASourceLocation>,
    ) -> (usize, PACallSite<'m>) {
        let id = self.next_callsite_id;
        self.next_callsite_id += 1;

        let callsite = PACallSite {
            id,
            caller,
            block,
            kind: call,
            direct_callee,
            context: caller_context,
            source_loc,
        };

        self.callsites.insert(id, callsite.clone());

        (id, callsite)
    }

    fn points_to_snapshot(&self, node: PANodeId) -> BTreeSet<PANodeId> {
        self.nodes
            .get(&node)
            .map(|n| n.points_to.clone())
            .unwrap_or_default()
    }

    /// type filter for FieldObject solvers
    fn object_may_hold_pointer_value(&self, obj: PANodeId) -> bool {
        let Some(node) = self.nodes.get(&obj) else {
            return false;
        };

        match &node.kind {
            // Stack/heap/global objects may hold pointer values depending on their type.
            // If type is unknown, be conservative and allow.
            PANodeKind::AllocaObject { allocated_type, .. } => {
                type_may_contain_pointer(allocated_type)
            }

            PANodeKind::HeapObject { allocated_type, .. } => allocated_type
                .as_ref()
                .map(type_may_contain_pointer)
                .unwrap_or(true),

            PANodeKind::GlobalObject { .. } => true,

            // Critical: field objects can hold pointer values.
            // If field_type is None, be conservative.
            PANodeKind::FieldObject { field_type, .. } => field_type
                .as_ref()
                .map(type_may_contain_pointer)
                .unwrap_or(true),

            // These are values/functions, not memory objects that hold contents.
            PANodeKind::SSAValue { .. }
            | PANodeKind::Constant { .. }
            | PANodeKind::FunctionObject { .. }
            | PANodeKind::FunctionReturn { .. }
            | PANodeKind::IndirectCallTarget { .. }
            | PANodeKind::ReceiverObject { .. } => false,

            // adapt if you still have other variants
            _ => true,
        }
    }

    /// type filter for memcpy
    fn memcpy_may_copy_pointer_contents(&self, src_obj: PANodeId, dst_obj: PANodeId) -> bool {
        let src_ty = self.nodes.get(&src_obj).and_then(|n| n.ty.as_ref());
        let dst_ty = self.nodes.get(&dst_obj).and_then(|n| n.ty.as_ref());

        match (src_ty, dst_ty) {
            // For unknown FieldObject type, reject to avoid explosion.
            (None, _) | (_, None) => {
                !self.is_field_object(src_obj) && !self.is_field_object(dst_obj)
            }

            (Some(src_ty), Some(dst_ty)) => {
                type_may_contain_pointer(src_ty)
                    && type_may_contain_pointer(dst_ty)
                    && memcpy_object_types_compatible(src_ty, dst_ty)
            }
        }
    }

    fn is_field_object(&self, id: PANodeId) -> bool {
        return matches!(
            self.nodes.get(&id).map(|n| &n.kind),
            Some(PANodeKind::FieldObject { .. })
        );
    }

    pub fn print_points_to_sets(&self) -> Result<(), Box<dyn Error>> {
        let mut file = File::create("points_to.txt")?;

        writeln!(file, "=== Points-To Sets ===")?;
        writeln!(file)?;

        // sort and print
        let mut nodes: Vec<_> = self.nodes.iter().collect();
        nodes.sort_by_key(|(id, _node)| **id);

        for (id, node) in nodes {
            write!(file, "  {} \n    -> {{", node)?;

            let mut first = true;

            for pointee_id in &node.points_to {
                if !first {
                    write!(file, ", ")?;
                }

                //// print the pointee node in a more readable format
                // let pointee = self
                //     .nodes
                //     .get(pointee_id)
                //     .map(|n| format!("n{}:{}", pointee_id, n))
                //     .unwrap_or_else(|| format!("n{}:<missing>", pointee_id));
                // write!(file, "{}", pointee)?;
                write!(file, "n{}", pointee_id)?;
                first = false;
            }

            writeln!(file, "}}")?;
        }

        Ok(())
    }

    pub fn print_source_locations(&self) -> Result<(), Box<dyn Error>> {
        let mut file = File::create("source_locations.txt")?;

        writeln!(file, "=== Source Locations from Debug Info ===")?;
        writeln!(file)?;

        // sort and print
        let mut nodes: Vec<_> = self.nodes.iter().collect();
        nodes.sort_by_key(|(id, _node)| **id);

        for (id, node) in nodes {
            if let Some(source_loc) = &node.source_loc {
                write!(file, "  {}  ->  {}\n", node, source_loc)?;
            } else {
                write!(file, "  {}  ->  <N/A>\n", node)?;
            }
        }

        Ok(())
    }

    /// print the PAG to a file
    pub fn print_pointer_assignment_graph(&self) -> Result<(), Box<dyn Error>> {
        if self.config.on_the_fly {
            self.call_graph.print_call_graph()?;
            println!("Wrote call graph to cg.txt");
        }

        let mut file = File::create("pag.txt")?;

        writeln!(file, "=== Pointer Assignment Graph ===")?;
        // writeln!(file, "modules: ")?;
        // for module in modules {
        //     writeln!(file, "  {}", module.name)?;
        // }
        writeln!(file)?;

        writeln!(file, "=== Nodes ===")?;
        // sort and print
        let mut nodes: Vec<_> = self.nodes.iter().collect();
        nodes.sort_by_key(|(id, _node)| **id);

        for (_, node) in nodes {
            writeln!(file, "  {}", node)?;
        }

        writeln!(file)?;
        writeln!(file, "=== Edges ===")?;
        for edge in &self.edges {
            let src = self.nodes.get(&edge.src).unwrap();
            let dst = self.nodes.get(&edge.dst).unwrap();

            writeln!(
                file,
                "  {} -[{:?}]-> {}       (function={} block={})",
                src, edge.kind, dst, edge.function, edge.block
            )?;
        }

        self.print_points_to_sets()?;
        self.print_source_locations()?;

        writeln!(file, "=== functions_by_name ===")?;
        writeln!(file, "total functions: {}", self.functions_by_name.len())?;

        for (name, func) in &self.functions_by_name {
            writeln!(file, "key = {}", name)?;
            writeln!(file, "  func.name = {}", func.name)?;
        }

        Ok(())
    }

    pub fn print_statistics(&self) {
        let num_nodes = self.nodes.len();
        let num_edges = self.edges.len();
        let num_lhs_index_entries = self.lhs2edges.len();
        let num_callsites = self.callsites.len();
        let num_discovered_functions = self.visited_functions.len();
        let num_pending_functions = self.pending_functions.len();

        let total_points_to: usize = self.nodes.values().map(|node| node.points_to.len()).sum();

        println!("=== Pointer Analysis Statistics ===");
        println!("nodes: {}", num_nodes);
        println!("constraints/edges: {}", num_edges);
        println!("lhs2edges index entries: {}", num_lhs_index_entries); // TODO: update other statistics
        println!("callsites: {}", num_callsites);
        println!("discovered functions: {}", num_discovered_functions);
        println!("pending functions: {}", num_pending_functions);
        println!("total points-to facts: {}", total_points_to);

        self.print_node_kind_statistics();
        self.print_edge_kind_statistics();
        self.print_context_statistics();
        self.print_node_context_statistics();
        // self.print_vtable_function_refs();

        // if self.config.context_signatures.is_some() {
        //     let _ = self.print_context_points();
        //     println!();
        //     println!("=== Context Statistics ===");
        //     println!("context points: {}", self.context_points().len());
        // }
        println!()
    }

    fn print_edge_kind_statistics(&self) {
        let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();

        for edge in &self.edges {
            let kind = match &edge.kind {
                PAEdgeKind::AddressOf => "AddressOf",
                PAEdgeKind::Copy => "Copy",
                PAEdgeKind::Load => "Load",
                PAEdgeKind::Store => "Store",
                PAEdgeKind::GEP { .. } => "GEP",
                PAEdgeKind::ByteOffsetGEP { .. } => "ByteOffsetGEP",
                PAEdgeKind::UnknownOffsetGEP => "UnknownOffsetGEP",
                PAEdgeKind::AddrSpaceCast { .. } => "AddrSpaceCast",
                PAEdgeKind::BitCast { .. } => "BitCast",
                PAEdgeKind::IntToPtr { .. } => "IntToPtr",
                PAEdgeKind::Phi { .. } => "Phi",
                PAEdgeKind::Select => "Select",
                PAEdgeKind::IndirectCall { .. } => "IndirectCall",
                PAEdgeKind::ReceiverCall { .. } => "ReceiverCall",
                PAEdgeKind::DirectCall { .. } => "DirectCall",
                PAEdgeKind::MemCopy => "MemCopy",
                PAEdgeKind::AggregateCopy => "AggregateCopy",
                PAEdgeKind::ExtractCopy { .. } => "ExtractCopy",
            };

            *counts.entry(kind).or_insert(0) += 1;
        }

        let mut entries: Vec<(&'static str, usize)> =
            counts.iter().map(|(kind, count)| (*kind, *count)).collect();

        entries.sort_by(|a, b| {
            b.1.cmp(&a.1) // count descending
                .then_with(|| a.0.cmp(b.0)) // tie-break by name ascending
        });

        println!();
        println!("=== Constraint Kind Statistics ===");

        for (kind, count) in entries {
            println!("{}: {}", kind, count);
        }
        println!()
    }

    fn print_node_kind_statistics(&self) {
        let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();

        for node in self.nodes.values() {
            let kind = match &node.kind {
                PANodeKind::SSAValue { .. } => "SSAValue",
                PANodeKind::Constant { .. } => "Constant",
                PANodeKind::AllocaObject { .. } => "AllocaObject",
                PANodeKind::FieldObject { .. } => "FieldObject",
                PANodeKind::FunctionReturn { .. } => "FunctionReturn",
                PANodeKind::FunctionObject { .. } => "FunctionObject",
                PANodeKind::ReceiverObject { .. } => "ReceiverObject",
                PANodeKind::IndirectCallTarget { .. } => "IndirectCallTarget",

                PANodeKind::GlobalObject { .. } => "GlobalObject",
                PANodeKind::GlobalAddress { .. } => "GlobalAddress",
                PANodeKind::TableSlot { .. } => "TableSlot",
                PANodeKind::AggregateField { .. } => "AggregateField",
                PANodeKind::HeapObject { .. } => "HeapObject",
            };

            *counts.entry(kind).or_insert(0) += 1;
        }

        let mut entries: Vec<(&'static str, usize)> =
            counts.iter().map(|(kind, count)| (*kind, *count)).collect();

        entries.sort_by(|a, b| {
            b.1.cmp(&a.1) // count descending
                .then_with(|| a.0.cmp(b.0)) // tie-break by name ascending
        });

        println!();
        println!("=== Node Kind Statistics ===");

        for (kind, count) in entries {
            println!("{}: {}", kind, count);
        }
    }

    pub fn print_context_statistics(&self) {
        let mut functions_per_ctx: BTreeMap<String, usize> = BTreeMap::new();
        let mut ctx_lengths: BTreeMap<usize, usize> = BTreeMap::new();

        for (function, ctx) in &self.visited_functions {
            *functions_per_ctx.entry(ctx.key()).or_default() += 1;
            *ctx_lengths.entry(ctx.len()).or_default() += 1;

            debug!("[CTX FUNC] {} @ {}", function, ctx.key());
        }

        println!();
        println!("=== Context Statistics ===");
        println!(
            "distinct function instances: {}",
            self.visited_functions.len()
        );
        println!("distinct contexts: {}", functions_per_ctx.len());
        println!("context length histogram: {:?}", ctx_lengths);
    }

    pub fn print_node_context_statistics(&self) {
        let mut nodes_per_ctx: BTreeMap<String, usize> = BTreeMap::new();

        for node in self.nodes.values() {
            *nodes_per_ctx.entry(node.context.key()).or_default() += 1;
        }

        println!();
        println!("=== Node Context Statistics ===");
        println!("distinct node contexts: {}", nodes_per_ctx.len());

        for (ctx, count) in nodes_per_ctx.iter().take(30) {
            println!("  {} -> {} nodes", ctx, count);
        }
    }

    pub fn print_vtable_function_refs(&self) {
        println!("\n=== Global Function Refs ===");
        println!("globals with function refs: {}", self.vtable2function.len());

        for (global, refs) in &self.vtable2function {
            println!("{}:", global);
            for r in refs {
                println!("  {}", r);
            }
        }
    }

    ////////////////////////// cfg related //////////////////////////

    /// compute the cleanup basicblocks and its successors that do not have normal incoming control flow edges
    /// return a set of basicblock names that need to skip
    fn compute_cleanup_blocks_with_cfg(&mut self, func: &llvm_ir::Function) -> BTreeSet<String> {
        let cfg: ControlFlowGraph<'_> = ControlFlowGraph::new(func);

        let mut skip = BTreeSet::new();
        let mut worklist = VecDeque::new();

        for bb in &func.basic_blocks {
            let name = util::normalize_block_label(&format!("{}", &bb.name));
            if util::is_cleanup_block_name(&name) {
                if skip.insert(name.clone()) {
                    worklist.push_back(name);
                }
            }
        }

        while let Some(block_name) = worklist.pop_front() {
            let name = Name::Name(Box::new(block_name));
            for succ in cfg.succs(&name) {
                let succ = util::normalize_block_label(&format!("{}", succ));

                if skip.insert(succ.clone()) {
                    worklist.push_back(succ);
                }
            }
        }

        skip
    }

    ////////////////////////// cfg related end //////////////////////////
}

/// Helper functions

fn direct_callee_name(op: &llvm_ir::Operand) -> Option<String> {
    match op {
        llvm_ir::Operand::ConstantOperand(cref) => direct_callee_name_from_constant(cref.as_ref()),

        // LocalOperand means indirect call through function pointer.
        llvm_ir::Operand::LocalOperand { .. } => None,

        _ => None,
    }
}

fn direct_callee_name_from_constant(c: &llvm_ir::Constant) -> Option<String> {
    match c {
        llvm_ir::Constant::GlobalReference { name, .. } => {
            Some(util::normalize_function_name(&format!("{}", name)).to_string())
        }

        llvm_ir::Constant::BitCast(bitcast) => {
            direct_callee_name_from_constant(bitcast.operand.as_ref())
        }

        llvm_ir::Constant::GetElementPtr(gep) => {
            direct_callee_name_from_constant(gep.address.as_ref())
        }

        _ => None,
    }
}

fn type_is_pointer_like(ty: &TypeRef) -> bool {
    return matches!(ty.as_ref(), Type::PointerType { .. });
}

fn call_function_operand(function: &either::Either<InlineAssembly, Operand>) -> Option<&Operand> {
    match function {
        either::Either::Right(op) => Some(op),
        either::Either::Left(_asm) => None,
    }
}

fn operand_type(op: &llvm_ir::Operand) -> Option<llvm_ir::TypeRef> {
    match op {
        llvm_ir::Operand::LocalOperand { ty, .. } => Some(ty.clone()),

        llvm_ir::Operand::ConstantOperand(c) => constant_type(c.as_ref()),

        _ => None,
    }
}

fn constant_type(c: &llvm_ir::Constant) -> Option<llvm_ir::TypeRef> {
    match c {
        llvm_ir::Constant::GlobalReference { ty, .. } => Some(ty.clone()),

        llvm_ir::Constant::Null(ty) => Some(ty.clone()),

        llvm_ir::Constant::BitCast(bitcast) => Some(bitcast.to_type.clone()),

        _ => None,
    }
}

fn type_key(ty: &llvm_ir::TypeRef) -> String {
    return format!("{:?}", ty);
}

fn collect_function_refs_from_constant(c: &ConstantRef, out: &mut Vec<String>) {
    match c.as_ref() {
        Constant::GlobalReference { name, .. } => {
            out.push(util::normalize_function_name(&format!("{}", name)).to_string());
        }

        Constant::Struct { values, .. } => {
            for value in values {
                collect_function_refs_from_constant(value, out);
            }
        }

        Constant::Array { elements, .. } => {
            for elem in elements {
                collect_function_refs_from_constant(elem, out);
            }
        }

        Constant::Vector(elements) => {
            for elem in elements {
                collect_function_refs_from_constant(elem, out);
            }
        }

        Constant::BitCast(bitcast) => {
            collect_function_refs_from_constant(&bitcast.operand, out);
        }

        Constant::GetElementPtr(gep) => {
            collect_function_refs_from_constant(&gep.address, out);

            for idx in &gep.indices {
                collect_function_refs_from_constant(idx, out);
            }
        }

        _ => {}
    }
}

fn global_name_from_operand(op: &llvm_ir::Operand) -> Option<String> {
    match op {
        llvm_ir::Operand::ConstantOperand(cref) => global_name_from_constant(cref.as_ref()),

        _ => None,
    }
}

fn global_name_from_constant(c: &llvm_ir::Constant) -> Option<String> {
    match c {
        llvm_ir::Constant::GlobalReference { name, .. } => Some(format!("{}", name)),

        llvm_ir::Constant::BitCast(bitcast) => global_name_from_constant(bitcast.operand.as_ref()),

        llvm_ir::Constant::GetElementPtr(gep) => global_name_from_constant(gep.address.as_ref()),

        _ => None,
    }
}

/// normalize_function_name here
/// Typical demangled from:
/// _ZN68_$LT$alloc..sync..Arc$LT$T$C$A$GT$$u20$as$u20$core..clone..Clone$GT$5clone17h1e76781a8c9a84acE
/// to:
/// <alloc::sync::Arc<T, A> as core::clone::Clone>::clone
/// and check whether it is a Arc clone
fn is_clone(function_name: &str) -> bool {
    let name = demangle(function_name).to_string();

    name.ends_with("as core::clone::Clone>::clone")
}

/// <T as core::ops::deref::Deref>::deref for the smart pointers we alias through
fn is_deref(function_name: &str) -> bool {
    let name = demangle(function_name).to_string();

    name.ends_with("as core::ops::deref::Deref>::deref")
        || name.ends_with("as core::ops::deref::DerefMut>::deref_mut")
    // && (name.starts_with("<alloc::string::String")
    //     || (name.starts_with("<alloc::sync::Arc<")
    //     || name.starts_with("<std::sync::mutex::MutexGuard<"))
}

/// <alloc::string::String as ...Deref>::deref returns { ptr, i64 }
fn is_string_deref(function_name: &str) -> bool {
    let name = demangle(function_name).to_string();

    name.starts_with("<alloc::string::String")
        && name.contains("as core::ops::deref::Deref>::deref")
}

/// core::option::Option<&T>::cloned
fn is_option_cloned(function_name: &str) -> bool {
    let name = demangle(function_name).to_string();

    name.starts_with("core::option::Option") && name.contains(">::cloned")
}

/// raw allocators we model as heap-object factories (their bodies are skipped)
fn is_heap_allocator(function_name: &str) -> bool {
    if function_name.contains("__rust_alloc") {
        return true;
    }

    let name = demangle(function_name).to_string();

    name.contains("alloc::alloc::exchange_malloc")
        || name.contains("alloc::alloc::alloc")
        || name.contains("::alloc_impl")
        || (name.contains("raw_vec::RawVec") && name.contains("allocate_in"))
}

fn named_struct_name(receiver_ty: &TypeRef) -> Option<String> {
    match receiver_ty.as_ref() {
        Type::NamedStructType { name } => Some(format!("{}", name)),

        _ => None,
    }
}

/// parse the crate name from a Rust legacy-mangled symbol: `_ZN<len><crate>...`.
/// e.g. `_ZN11llm_ac_demo4main17h..E` -> `llm_ac_demo`. returns "" if it does not
/// look like a `_ZN`-mangled symbol (selective-context gate then disables).
fn parse_app_crate(mangled: &str) -> String {
    let s = util::normalize_function_name(mangled).trim_start_matches('_');
    let Some(rest) = s.strip_prefix("ZN") else {
        return String::new();
    };

    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    let Ok(len) = digits.parse::<usize>() else {
        return String::new();
    };

    let after = &rest[digits.len()..];
    if after.len() >= len {
        after[..len].to_string()
    } else {
        String::new()
    }
}

/// compute indices for insertvalue/extractvalue (constant struct indices)
fn indices_as_u64(indices: &[u32]) -> Vec<u64> {
    indices.iter().map(|i| *i as u64).collect()
}

fn gep_single_constant_offset(indices: &[llvm_ir::Operand]) -> Option<i64> {
    if indices.len() == 1 {
        if let Some(idx) = indices.get(0) {
            if let Some(offset) = const_int_operand_as_u64(idx) {
                // u64 -> i64 as a two's-complement reinterpret: a negative byte
                // offset comes through as a large u64, so try_into().unwrap() would
                // panic (seen on LLVM-20 IR). `as i64` is the correct wrap here.
                return Some(offset as i64);
            }
        }
    }

    return None;
}

/// compute indices for GEP, can be unknown (empty)
fn gep_indices_as_u64(indices: &[llvm_ir::Operand]) -> Vec<u64> {
    let mut out = Vec::new();

    for idx in indices {
        if let Some(v) = const_int_operand_as_u64(idx) {
            out.push(v);
        } else {
            // Unknown dynamic index: collapse to field-insensitive.
            return Vec::new();
        }
    }

    out
}

fn const_int_operand_as_u64(op: &llvm_ir::Operand) -> Option<u64> {
    match op {
        llvm_ir::Operand::ConstantOperand(c) => match c.as_ref() {
            llvm_ir::Constant::Int { value, .. } => Some(*value),
            _ => None,
        },
        _ => None,
    }
}

fn normalize_gep_indices(indices: &[u64]) -> Vec<u64> {
    // LLVM GEP often starts with 0 to mean "within the same object".
    // For struct field sensitivity, [0, 1] usually means field 1.
    if indices.first() == Some(&0) {
        indices[1..].to_vec()
    } else {
        indices.to_vec()
    }
}

fn name_key(name: &llvm_ir::Name) -> String {
    format!("{}", name)
        .trim_start_matches('%')
        .trim_start_matches('@')
        .trim_matches('"')
        .to_string()
}

fn record_instruction_result_type(
    instr: &llvm_ir::instruction::Instruction,
    ssa_types: &mut BTreeMap<String, Option<llvm_ir::TypeRef>>,
) {
    use llvm_ir::instruction::Instruction;

    match instr {
        Instruction::Alloca(i) => {
            ssa_types.insert(name_key(&i.dest), None);
        }

        Instruction::Load(i) => {
            ssa_types.insert(name_key(&i.dest), Some(i.loaded_ty.clone()));
        }

        Instruction::GetElementPtr(i) => {
            ssa_types.insert(name_key(&i.dest), None);
        }

        Instruction::BitCast(i) => {
            ssa_types.insert(name_key(&i.dest), Some(i.to_type.clone()));
        }

        Instruction::AddrSpaceCast(i) => {
            ssa_types.insert(name_key(&i.dest), Some(i.to_type.clone()));
        }

        Instruction::IntToPtr(i) => {
            ssa_types.insert(name_key(&i.dest), Some(i.to_type.clone()));
        }

        Instruction::Phi(i) => {
            if let Some((op, _)) = i.incoming_values.first() {
                if let Some(ty) = operand_type(op) {
                    ssa_types.insert(name_key(&i.dest), Some(ty));
                }
            }
        }

        Instruction::Select(i) => {
            if let Some(ty) = operand_type(&i.true_value) {
                ssa_types.insert(name_key(&i.dest), Some(ty));
            }
        }

        Instruction::Call(i) => {
            if let Some(dest) = &i.dest {
                if let Some(ret_ty) = call_return_type(&i.function_ty) {
                    ssa_types.insert(name_key(dest), Some(ret_ty));
                }
            }
        }

        _ => {}
    }
}

fn record_terminator_result_type(
    term: &llvm_ir::terminator::Terminator,
    ssa_types: &mut BTreeMap<String, Option<llvm_ir::TypeRef>>,
) {
    use llvm_ir::terminator::Terminator;

    match term {
        Terminator::Invoke(i) => {
            if let Some(ret_ty) = call_return_type(&i.function_ty) {
                ssa_types.insert(name_key(&i.result), Some(ret_ty));
            }
        }

        _ => {}
    }
}

fn gep_result_object_type(base_ty: &llvm_ir::TypeRef, indices: &[u64]) -> Option<llvm_ir::TypeRef> {
    let mut cur_ty = base_ty.clone();

    for (pos, idx) in indices.iter().enumerate() {
        match cur_ty.as_ref() {
            // Struct field access.
            llvm_ir::Type::StructType { element_types, .. } => {
                let field_idx = *idx as usize;
                cur_ty = element_types.get(field_idx)?.clone();
            }

            // Array indexing.
            llvm_ir::Type::ArrayType { element_type, .. } => {
                cur_ty = element_type.clone();
            }

            // Vector indexing.
            llvm_ir::Type::VectorType { element_type, .. } => {
                cur_ty = element_type.clone();
            }

            // Pointer type.
            //
            // In typed-pointer LLVM, first GEP index steps through the pointee.
            // In opaque-pointer LLVM 15+, pointee type may not exist.
            llvm_ir::Type::PointerType { .. } => {
                // Usually if the base object type is already the allocated type,
                // you should not see PointerType here. If you do, skip the first
                // zero index if present.
                if pos == 0 && *idx == 0 {
                    continue;
                } else {
                    return None;
                }
            }

            _ => {
                return None;
            }
        }
    }

    Some(cur_ty)
}

fn call_return_type(function_ty: &llvm_ir::TypeRef) -> Option<llvm_ir::TypeRef> {
    match function_ty.as_ref() {
        llvm_ir::Type::FuncType { result_type, .. } => Some(result_type.clone()),
        _ => None,
    }
}

/// heuristically skip visiting and creating constraints for the functions with the following signatures
/// do not skip the following:
///  Arc, Mutex, RwLock, tokio, and futures
///  _ZN3std6thread5spawn17h22da0a742a9c3c20E
//   _ZN3std6thread7Builder15spawn_unchecked17h0182a1068d22239dE
//   _ZN3std6thread7Builder16spawn_unchecked_17hba2e176eb3c3af33E
//   _ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17h06bb21b8ede9b485E
fn should_skip_function_body(function_name: &str) -> bool {
    let name = util::normalize_function_name(function_name);

    if name.contains("hashbrown")
        || name.contains("alloc5alloc")
        || name.contains("alloc7raw_vec")
        || name.contains("alloc..raw_vec")
        || name.contains("core3fmt")
        || name.contains("core..fmt")
        || name.contains("panic")
        || name.contains("drop_in_place")
        || name.contains("CString")
        || name.contains("memchr")
    {
        return true;
    }

    if name.contains("panic")
        || name.contains("panicking")
        || name.contains("unwrap_failed")
        || name.contains("rust_begin_unwind")
        || name.contains("__rust_start_panic")
        || name.contains("_Unwind_")
    {
        return true;
    }

    if name.starts_with("llvm.")
        || name.contains("llvm.")
        // || name.contains("memcpy")
        || name.contains("memmove")
        || name.contains("memset")
    {
        return true;
    }

    false
}

/// heuristically skip creating new contexts for these functions,
/// just use Global
fn should_skip_function_context(function_name: &str) -> bool {
    let name = util::normalize_function_name(function_name);

    if name.contains("panic")
        || name.contains("panicking")
        || name.contains("unwrap_failed")
        || name.contains("rust_begin_unwind")
        || name.contains("__rust_start_panic")
        || name.contains("_Unwind_")
    {
        return true;
    }

    if name.starts_with("llvm.")
        || name.contains("llvm.")
        || name.contains("memcpy")
        || name.contains("memmove")
        || name.contains("memset")
    {
        return true;
    }

    false
}
/// only consider major llm service sdk apis here
fn is_llm_api_function(name: &str) -> bool {
    const CRATES: &[&str] = &[
        "async_openai",
        "ollama_rs",
        "anthropic",
        "mistral",
        "cohere",
        "genai",
    ];

    CRATES.iter().any(|crate_name| name.contains(crate_name))
}

/// process vtables from global variable to find function references in constant tables
fn collect_vtable_functions<'m>(
    modules: &[&'m llvm_ir::Module],
) -> (BTreeMap<String, Vec<String>>, BTreeMap<String, Vec<String>>) {
    let mut global_function_refs: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut function_referrers: BTreeMap<String, Vec<String>> = BTreeMap::new();

    for module in modules {
        for gv in &module.global_vars {
            let Some(init) = &gv.initializer else {
                continue;
            };
            let name = format!("{}", gv.name);
            let global_name = util::normalize_function_name(&name);

            if global_name.contains("vtable") // i have only seen this for now
                        || global_name.contains("VTABLE")
                        || global_name.contains("{{vtable}}")
            {
                debug!("find vtable: {}", name);

                let mut refs = Vec::new();
                collect_function_refs_from_constant(init, &mut refs);

                refs.sort();
                refs.dedup();

                if refs.is_empty() {
                    continue;
                }

                for func_ref in &refs {
                    function_referrers
                        .entry(func_ref.clone())
                        .or_default()
                        .push(global_name.to_string());
                }

                global_function_refs.insert(global_name.to_string(), refs);
            }
        }
    }

    for globals in function_referrers.values_mut() {
        globals.sort();
        globals.dedup();
    }

    (global_function_refs, function_referrers)
}

fn type_may_contain_pointer(ty: &llvm_ir::TypeRef) -> bool {
    type_may_contain_pointer_depth(ty, 0)
}

fn type_may_contain_pointer_depth(ty: &llvm_ir::TypeRef, depth: usize) -> bool {
    if depth > 4 {
        return true;
    }

    match ty.as_ref() {
        llvm_ir::Type::PointerType { .. } => true,

        llvm_ir::Type::StructType { element_types, .. } => element_types
            .iter()
            .any(|elem| type_may_contain_pointer_depth(elem, depth + 1)),

        llvm_ir::Type::ArrayType { element_type, .. } => {
            type_may_contain_pointer_depth(element_type, depth + 1)
        }

        llvm_ir::Type::VectorType { element_type, .. } => {
            type_may_contain_pointer_depth(element_type, depth + 1)
        }

        // Named structs may be opaque or recursive. Keep conservative.
        llvm_ir::Type::NamedStructType { .. } => true,

        _ => false,
    }
}

fn work_item_lhs(item: &PAWorkItem) -> PANodeId {
    match (&item.edge.kind, &item.delta) {
        // Store: *dst = src
        // If src changed, process as src-driven.
        (PAEdgeKind::Store, PAWorkDelta::Src(_)) => item.edge.src,

        // If dst changed, process as dst-driven.
        (PAEdgeKind::Store, PAWorkDelta::Dst(_)) => item.edge.dst,

        // Normal case.
        _ => item.edge.src,
    }
}

fn edge_kind_sort_key(kind: &PAEdgeKind) -> String {
    match kind {
        PAEdgeKind::AddressOf => "0_AddressOf".to_string(),
        PAEdgeKind::Copy => "1_Copy".to_string(),
        PAEdgeKind::Load => "2_Load".to_string(),
        PAEdgeKind::Store => "3_Store".to_string(),
        PAEdgeKind::GEP { indices } => format!("4_GEP_{:?}", indices),
        PAEdgeKind::ByteOffsetGEP { offset } => format!("4_ByteOffsetGEP_{:?}", offset),
        PAEdgeKind::IndirectCall { callsite_id } => {
            return format!("5_IndirectCall_{}", callsite_id)
        }
        PAEdgeKind::ReceiverCall { callsite_id } => {
            return format!("6_ReceiverCall_{}", callsite_id)
        }
        PAEdgeKind::ExtractCopy { field } => format!("2_ExtractCopy_{:?}", field),
        _ => "1_Copy".to_string(),
    }
}

fn delta_kind_rank(delta: &PAWorkDelta) -> u8 {
    match delta {
        PAWorkDelta::Src(_) => 0,
        PAWorkDelta::Dst(_) => 1,
        PAWorkDelta::Full => 2,
    }
}

fn merge_sorted_work_items(items: Vec<PAWorkItem>) -> Vec<PAWorkItem> {
    let mut out: Vec<PAWorkItem> = Vec::new();

    for item in items {
        if let Some(last) = out.last_mut() {
            if same_work_item_group(last, &item) {
                merge_work_delta(&mut last.delta, item.delta);
                continue;
            }
        }

        out.push(item);
    }

    out
}

fn same_work_item_group(a: &PAWorkItem, b: &PAWorkItem) -> bool {
    same_edge(&a.edge, &b.edge) && delta_kind_rank(&a.delta) == delta_kind_rank(&b.delta)
}

fn merge_work_delta(dst: &mut PAWorkDelta, src: PAWorkDelta) {
    match (dst, src) {
        (PAWorkDelta::Src(dst_set), PAWorkDelta::Src(src_set)) => {
            dst_set.extend(src_set);
        }

        (PAWorkDelta::Dst(dst_set), PAWorkDelta::Dst(src_set)) => {
            dst_set.extend(src_set);
        }

        (PAWorkDelta::Full, PAWorkDelta::Full) => {}

        _ => {}
    }
}

fn same_edge(a: &PAEdge, b: &PAEdge) -> bool {
    a.src == b.src && a.dst == b.dst && a.kind == b.kind
    // && a.function == b.function
    // && a.block == b.block
}

fn memcpy_object_types_compatible(src_ty: &llvm_ir::TypeRef, dst_ty: &llvm_ir::TypeRef) -> bool {
    // Same object type: definitely okay.
    if format!("{:?}", src_ty) == format!("{:?}", dst_ty) {
        return true;
    }

    // Opaque pointers make exact checking hard.
    // If both may contain pointers, allow conservatively.
    type_may_contain_pointer(src_ty) && type_may_contain_pointer(dst_ty)
}

fn is_global_reference_constant(op: &Operand) -> bool {
    match op {
        Operand::ConstantOperand(c) => {
            return matches!(c.as_ref(), Constant::GlobalReference { .. })
        }

        _ => false,
    }
}

/// return the first non sret pointer-like argument index
fn first_pointer_like_non_sret_arg_index(
    args: &[(llvm_ir::Operand, Vec<llvm_ir::function::ParameterAttribute>)],
) -> Option<(usize, &Operand)> {
    args.iter().enumerate().find_map(|(idx, (arg, attrs))| {
        if arg_has_sret_attr(attrs) {
            return None;
        }

        let ty = operand_type(arg)?;
        if type_is_pointer_like(&ty) {
            Some((idx, arg))
        } else {
            None
        }
    })
}

fn arg_has_sret_attr(attrs: &[llvm_ir::function::ParameterAttribute]) -> bool {
    attrs.iter().any(|attr| {
        format!("{:?}", attr).contains("SRet") || format!("{:?}", attr).contains("sret")
    })
}

fn first_pointer_like_sret_arg(
    arguments: &Vec<(Operand, Vec<ParameterAttribute>)>,
) -> Option<(usize, &Operand)> {
    arguments
        .iter()
        .enumerate()
        .find_map(|(idx, (operand, attributes))| {
            let is_sret = attributes
                .iter()
                .any(|attribute| return matches!(attribute, ParameterAttribute::SRet(_)));

            if is_sret {
                return Some((idx, operand));
            } else {
                return None;
            }
        })
}

/// return the index and parameter of the first function parameter that is named "self" and has a pointer-like type
fn first_pointer_like_self_parameter(function: &llvm_ir::Function) -> Option<(usize, &Parameter)> {
    function
        .parameters
        .iter()
        .enumerate()
        .find_map(|(idx, param)| {
            let is_self = name_key(&param.name) == "self";
            let is_ptr = type_is_pointer_like(&param.ty);

            if is_self && is_ptr {
                Some((idx, param))
            } else {
                None
            }
        })
}

fn first_pointer_like_sret_parameter(function: &llvm_ir::Function) -> Option<(usize, &Parameter)> {
    function
        .parameters
        .iter()
        .enumerate()
        .find_map(|(idx, param)| {
            let is_sret = arg_has_sret_attr(&param.attributes);
            let is_ptr = type_is_pointer_like(&param.ty);

            if is_sret && is_ptr {
                Some((idx, param))
            } else {
                None
            }
        })
}

fn instruction_debugloc(inst: &Instruction) -> Option<&DebugLoc> {
    match inst {
        Instruction::Add(i) => i.debugloc.as_ref(),
        Instruction::Sub(i) => i.debugloc.as_ref(),
        Instruction::Mul(i) => i.debugloc.as_ref(),
        Instruction::UDiv(i) => i.debugloc.as_ref(),
        Instruction::SDiv(i) => i.debugloc.as_ref(),
        Instruction::URem(i) => i.debugloc.as_ref(),
        Instruction::SRem(i) => i.debugloc.as_ref(),

        Instruction::And(i) => i.debugloc.as_ref(),
        Instruction::Or(i) => i.debugloc.as_ref(),
        Instruction::Xor(i) => i.debugloc.as_ref(),
        Instruction::Shl(i) => i.debugloc.as_ref(),
        Instruction::LShr(i) => i.debugloc.as_ref(),
        Instruction::AShr(i) => i.debugloc.as_ref(),

        Instruction::Alloca(i) => i.debugloc.as_ref(),
        Instruction::Load(i) => i.debugloc.as_ref(),
        Instruction::Store(i) => i.debugloc.as_ref(),
        Instruction::GetElementPtr(i) => i.debugloc.as_ref(),

        Instruction::Trunc(i) => i.debugloc.as_ref(),
        Instruction::ZExt(i) => i.debugloc.as_ref(),
        Instruction::SExt(i) => i.debugloc.as_ref(),
        Instruction::FPTrunc(i) => i.debugloc.as_ref(),
        Instruction::FPExt(i) => i.debugloc.as_ref(),
        Instruction::FPToUI(i) => i.debugloc.as_ref(),
        Instruction::FPToSI(i) => i.debugloc.as_ref(),
        Instruction::UIToFP(i) => i.debugloc.as_ref(),
        Instruction::SIToFP(i) => i.debugloc.as_ref(),
        Instruction::PtrToInt(i) => i.debugloc.as_ref(),
        Instruction::IntToPtr(i) => i.debugloc.as_ref(),
        Instruction::BitCast(i) => i.debugloc.as_ref(),
        Instruction::AddrSpaceCast(i) => i.debugloc.as_ref(),

        Instruction::ICmp(i) => i.debugloc.as_ref(),
        Instruction::FCmp(i) => i.debugloc.as_ref(),

        Instruction::Phi(i) => i.debugloc.as_ref(),
        Instruction::Select(i) => i.debugloc.as_ref(),
        Instruction::Call(i) => i.debugloc.as_ref(),

        Instruction::ExtractElement(i) => i.debugloc.as_ref(),
        Instruction::InsertElement(i) => i.debugloc.as_ref(),
        Instruction::ShuffleVector(i) => i.debugloc.as_ref(),
        Instruction::ExtractValue(i) => i.debugloc.as_ref(),
        Instruction::InsertValue(i) => i.debugloc.as_ref(),

        Instruction::LandingPad(i) => i.debugloc.as_ref(),
        Instruction::Freeze(i) => i.debugloc.as_ref(),

        Instruction::Fence(i) => i.debugloc.as_ref(),
        Instruction::CmpXchg(i) => i.debugloc.as_ref(),
        Instruction::AtomicRMW(i) => i.debugloc.as_ref(),

        Instruction::VAArg(i) => i.debugloc.as_ref(),

        _ => None,
    }
}
