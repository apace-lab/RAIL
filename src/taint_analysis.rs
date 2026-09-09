use crate::context::PAContext;
use crate::context::PAContextElem;
use crate::pointer_assignment_graph::PACallSite;
use crate::pointer_assignment_graph::PAEdgeKind;
use crate::pointer_assignment_graph::PANodeId;
use crate::signature::SecurityPoint;
use crate::util;
use crate::ControlFlowGraph;
use crate::PAEdge;
use crate::PANode;
use crate::PointerAssignmentGraph;
use llvm_ir::Name;
use log::debug;
use std::collections::BTreeMap;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::println;

type FunctionKey = (String, PAContext);
type ReturnPropagationKey = (String, PAContext, PAContextElem);

/// When propagate_return_to_callers() is first called from seed_authenticated_functions(),
///    the authentication has already completed inside the AC-containing function. When returned to its caller,
///    process only statements/calls after the call that just returned, so use pos + 1.
/// When propagate_return_to_callers() recursively climbs from one caller to its caller,
///    the current caller’s own return needs to remain part of the propagation chain. In that case,
///    including the current callsite with pos can be necessary to preserve the return path.
#[derive(Debug, Clone, Copy)]
enum ReturnPropagationMode {
    AfterReturnedCall,  // pos + 1
    IncludeCurrentCall, // pos
}

#[derive(Debug, Clone)]
pub enum SemanticPointKind {
    /// Password/JWT/token/etc. authentication check.
    AccessControl {
        category: String,
    },

    /// Authentication/session recovery, e.g. Session::get, JWT claims extraction.
    ///
    /// You can omit this variant initially if your JSON does not distinguish it.
    AccessControlRecovery {
        category: String,
    },

    LlmPrompt {
        category: String,
    },

    LlmCall {
        category: String,
        provider: Option<String>,
    },

    /// Read from or write to a shared data store (database, ORM, NoSQL/KV, or a
    /// cache library). The `category` string is "data-read" or "data-write"; a
    /// read exposes stored data (the leak direction), a write puts data in.
    DataAccess {
        category: String,
    },
}

#[derive(Debug, Clone)]
pub struct SemanticPoint {
    pub callsite_id: usize,
    pub kind: SemanticPointKind,
    pub security_point: SecurityPoint, // to save prompt_idx, request_idx, etc

    pub caller: String,
    pub block: String,
    pub callee: Option<String>,
    pub caller_context: PAContext,

    // Actual argument nodes at the callsite.
    pub argument_nodes: Vec<PANodeId>,

    // Actual caller-side result, including normalized sret.
    pub result_node: Option<PANodeId>, // maybe sret
}

impl fmt::Display for SemanticPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return write!(
            f,
            // "SemanticPoint {{ callsite_id={}, kind={:?}, caller={}, block={}, callee={}, args={:?}, result={:?}, context={:?} }}",
            "SemanticPoint {{ callsite_id={}, kind={:?}, caller={}, args={:?}, result={:?} }}",
            self.callsite_id,
            self.kind,
            self.caller,
            // self.block,
            // self.callee.as_deref().unwrap_or("<unknown>"),
            self.argument_nodes,
            self.result_node,
            // self.caller_context,
        );
    }
}

pub struct TaintAnalysis<'m> {
    callsites: BTreeMap<usize, PACallSite<'m>>,
    pub functions_by_name: BTreeMap<String, &'m llvm_ir::Function>,
    pub semantic_points: Vec<SemanticPoint>,
    pub nodes: HashMap<PANodeId, PANode<'m>>,

    /// caller -> block -> set of callsite_ids
    pub callsites_by_block: HashMap<String, HashMap<String, Vec<usize>>>,

    /// Semantic contexts carried by PAG nodes.
    pub node_contexts: HashMap<PANodeId, HashSet<PAContextElem>>,

    /// Principal controlling authenticated execution blocks.
    pub active_principals: HashMap<FunctionKey, HashSet<PAContextElem>>,

    /// Fast outgoing PAG adjacency.
    outgoing: HashMap<PANodeId, Vec<(PANodeId, PAEdgeKind)>>,

    /// A node used as an input to a semantic point.
    ///     node_id -> indices into pag.semantic_points
    semantic_points_by_input: HashMap<PANodeId, Vec<usize>>,

    /// Semantic points whose result corresponds to a node.
    semantic_points_by_result: HashMap<PANodeId, Vec<usize>>,

    /// Application crate prefix (e.g. "llm_ac_demo"), derived from the module's
    /// `main`. Used to decide which callees are application code.
    pub app_crate: String,
}

impl<'m> TaintAnalysis<'m> {
    // pub fn new(pag: &'m PointerAssignmentGraph<'m>) -> Self {
    //     let outgoing = Self::build_outgoing_edges(&pag.edges);
    //     let (callsites_by_block, _callee2callsites) = Self::build_calls(&pag.callsites);

    //     let mut engine = Self {
    //         pag,
    //         callsites: pag.callsites.clone(),
    //         callsites_by_block,
    //         node_contexts: HashMap::new(),
    //         active_principals: HashMap::new(),
    //         outgoing,
    //         semantic_points_by_input: HashMap::new(),
    //         semantic_points_by_result: HashMap::new(),
    //     };

    //     engine.build_semantic_point_index();
    //     engine
    // }

    pub fn new() -> Self {
        let mut engine = Self {
            callsites: BTreeMap::new(),
            nodes: HashMap::new(),
            functions_by_name: BTreeMap::new(),
            semantic_points: Vec::new(),
            callsites_by_block: HashMap::new(),
            node_contexts: HashMap::new(),
            active_principals: HashMap::new(),
            outgoing: HashMap::new(),
            semantic_points_by_input: HashMap::new(),
            semantic_points_by_result: HashMap::new(),
            app_crate: String::new(),
        };

        engine
    }

    pub fn init(&mut self, pag: &PointerAssignmentGraph<'m>) {
        self.outgoing = Self::build_outgoing_edges(&pag.edges);
        let (callsites_by_block, _callee2callsites) = Self::build_calls(&pag.callsites);
        self.callsites_by_block = callsites_by_block;
        self.callsites = pag.callsites.clone();
        self.functions_by_name = pag.functions_by_name.clone();
        self.semantic_points = pag.semantic_points.clone();
        self.nodes = pag.nodes.clone();
        self.app_crate = pag.app_crate.clone();

        self.build_semantic_point_index();
    }

    pub fn run(&mut self) {
        // 1. Use CFG locally around authentication points,
        //    then seed application-level callees.
        self.seed_authenticated_functions();

        // 2. Propagate principal through application call graph.
        self.propagate_function_principals();

        // 3. Seed prompt/LLM arguments based on active functions.
        let mut worklist = VecDeque::new();

        self.seed_semantic_nodes_from_active_functions(&mut worklist);

        // 4. Propagate semantic/data contexts through PAG.
        self.propagate_data_contexts(&mut worklist);
    }

    ///////// preparing taint analysis from pag /////////////

    fn build_semantic_point_index(&mut self) {
        for (point_index, point) in self.semantic_points.iter().enumerate() {
            for arg in &point.argument_nodes {
                self.semantic_points_by_input
                    .entry(*arg)
                    .or_default()
                    .push(point_index);
            }

            if let Some(result) = point.result_node {
                self.semantic_points_by_result
                    .entry(result)
                    .or_default()
                    .push(point_index);
            }
        }
    }

    fn build_outgoing_edges(edges: &[PAEdge]) -> HashMap<PANodeId, Vec<(PANodeId, PAEdgeKind)>> {
        let mut outgoing = HashMap::new();

        for edge in edges {
            if Self::propagates_context(&edge.kind) {
                outgoing
                    .entry(edge.src)
                    .or_insert_with(Vec::new)
                    .push((edge.dst, edge.kind.clone()));
            }
        }

        outgoing
    }

    fn propagates_context(kind: &PAEdgeKind) -> bool {
        return matches!(
            kind,
            PAEdgeKind::Copy
                | PAEdgeKind::Store
                | PAEdgeKind::Load
                | PAEdgeKind::Select
                | PAEdgeKind::MemCopy
                | PAEdgeKind::ExtractCopy { .. }
                | PAEdgeKind::AggregateCopy
                | PAEdgeKind::GEP { .. }
                | PAEdgeKind::ByteOffsetGEP { .. }
                | PAEdgeKind::BitCast
        );
    }

    fn build_calls(
        callsites: &BTreeMap<usize, PACallSite<'m>>,
    ) -> (
        HashMap<String, HashMap<String, Vec<usize>>>,
        HashMap<String, Vec<usize>>,
    ) {
        let mut callsites_by_block: HashMap<String, HashMap<String, Vec<usize>>> = HashMap::new();
        let mut callee2callsites: HashMap<String, Vec<usize>> = HashMap::new();

        for (id, callsite) in callsites {
            let caller = callsite.caller.clone();
            // Normalize the block label (strip leading '%') so lookups keyed by
            // CFG-normalized block names (from normal_reachable_blocks) match.
            let block = util::normalize_block_label(&callsite.block);
            let callee = callsite.direct_callee.clone();

            callsites_by_block
                .entry(caller.clone())
                .or_default()
                .entry(block.clone())
                .or_default()
                .push(*id);

            if let Some(callee) = callee {
                callee2callsites.entry(callee).or_default().push(*id);
            }
        }

        (callsites_by_block, callee2callsites)
    }

    fn get_callsites_by_ids(&self, ids: Vec<usize>) -> Vec<PACallSite<'m>> {
        let mut callsites = Vec::new();
        for id in ids {
            let callsite = self.callsites.get(&id);
            if let Some(cs) = callsite {
                callsites.push(cs.clone());
            }
        }

        callsites
    }

    pub fn get_callsites_in_block(
        &self,
        caller: &str,
        block: &str,
        caller_context: &PAContext,
    ) -> Vec<PACallSite<'m>> {
        let ids: Vec<usize> = self
            .callsites_by_block
            .get(caller)
            .and_then(|blocks| blocks.get(&util::normalize_block_label(block)))
            .into_iter()
            .flatten()
            .copied()
            .filter(|id| {
                self.callsites
                    .get(id)
                    .map(|cs| cs.context == *caller_context)
                    .unwrap_or(false)
            })
            .collect();

        self.get_callsites_by_ids(ids)
    }

    pub fn get_callsites_of_function(
        &self,
        caller: &str,
        caller_context: &PAContext,
    ) -> Vec<PACallSite<'m>> {
        let ids: Vec<usize> = self
            .callsites_by_block
            .get(caller)
            .map(|blocks| {
                blocks
                    .values()
                    .flatten()
                    .copied()
                    .filter(|id| {
                        self.callsites
                            .get(id)
                            .map(|cs| &cs.context == caller_context)
                            .unwrap_or(false)
                    })
                    .collect()
            })
            .unwrap_or_default();

        self.get_callsites_by_ids(ids)
    }

    pub fn get_callers_of_function(
        &self,
        callee: &str,
        callee_context: &PAContext,
    ) -> Vec<PACallSite> {
        let ids: Vec<usize> = self
            .callsites
            .values()
            .filter(|callsite| callsite.direct_callee.as_deref() == Some(callee))
            .filter(|callsite| {
                let generated_callee_ctx = self.get_callee_context(callsite);
                &generated_callee_ctx == callee_context
            })
            .map(|callsite| callsite.id)
            .collect();

        return self.get_callsites_by_ids(ids.to_vec());
    }

    fn get_callsites_after_in_block(
        &self,
        caller: &str,
        block: &str,
        callsite_id: usize,
        pos_mode: ReturnPropagationMode,
    ) -> Vec<PACallSite<'m>> {
        debug!(
            "[AFG] get callsites for caller = {}, block = {}, callsite_id = {}",
            caller, block, callsite_id
        );

        let Some(blocks) = self.callsites_by_block.get(caller) else {
            return Vec::new();
        };

        let Some(callsites) = blocks.get(block) else {
            return Vec::new();
        };

        debug!(
            "[AFG] get_callsites_after_in_block: current callsites = {:?}",
            callsites
        );
        for cs in callsites {
            // also debug
            if let Some(cs) = self.callsites.get(cs) {
                debug!("[AFG]     {:?}", cs);
            }
        }

        let Some(pos) = callsites.iter().position(|idx| {
            self.callsites
                .get(idx)
                .map(|cs| cs.id == callsite_id)
                .unwrap_or(false)
        }) else {
            return Vec::new();
        };

        let start_pos = match pos_mode {
            ReturnPropagationMode::AfterReturnedCall => pos + 1,
            ReturnPropagationMode::IncludeCurrentCall => pos,
        };
        debug!("[AFG] find pos = {}, start_pos = {}", pos, start_pos);

        let ids = callsites.iter().skip(start_pos).copied().collect();

        return self.get_callsites_by_ids(ids);
    }

    /// return all bbs after start_block in function following normal execution
    fn normal_reachable_blocks(&self, function: &str, start_block: &str) -> HashSet<String> {
        let mut visited = HashSet::new();
        let mut worklist = VecDeque::new();

        worklist.push_back(start_block.to_string());

        while let Some(block) = worklist.pop_front() {
            if !visited.insert(block.clone()) {
                continue;
            }

            // TODO: if two successsors, one is for true branch, and the other for false branch
            // we should only do the true branch,
            for successor in self.get_normal_success_blocks(function, &block) {
                if !visited.contains(&successor) {
                    worklist.push_back(successor);
                }
            }
        }

        visited
    }

    /// return all successor bbs of block in function following normal execution
    pub fn get_normal_success_blocks(&self, function: &str, block: &str) -> Vec<String> {
        let func = self
            .functions_by_name
            .get(util::normalize_function_name(function))
            .copied();

        let Some(func) = func else {
            debug!(
                "[PAG] get_normal_cfg_successors: cannot find function body with name = {}",
                function
            );
            return Vec::new();
        };

        let cfg: ControlFlowGraph<'_> = ControlFlowGraph::new(&func);
        let mut successors = Vec::new();
        let name = util::normalize_block_label(&format!("{}", block));
        let block_name = Name::Name(Box::new(name.to_string()));

        for succ in cfg.succs(&block_name) {
            let succ = util::normalize_block_label(&format!("{}", succ));
            if !util::is_cleanup_block_name(&succ) {
                successors.push(succ.clone())
            }
        }

        debug!(
            "[PAG] get_normal_cfg_successors: find normal bb successors = {:?} for bb = {}",
            successors, block
        );

        successors
    }

    /// return one true path successor bb of block in function following normal execution
    fn get_normal_success_block(&self, function: &str, block: &str) -> Option<String> {
        let bbs = self.get_normal_success_blocks(function, block);
        debug!("[AFG] get_normal_success_block: find {} success blocks ({:?}) for function = {}, bb = {}", bbs.len(), bbs, function, block);

        if bbs.is_empty() {
            return None;
        }

        let successor = bbs[0].clone();
        if bbs.len() > 1 {
            // special, i've only seen 1 successor so far
            println!(
                "[AFG] get_normal_success_block: only return the 1st successor block = {} but found {}: {:?}",
                successor, bbs.len(), bbs,
            );
        }

        return Some(successor);
    }

    /// TODO: global for now
    fn get_callee_context(&self, callsite: &'m PACallSite) -> PAContext {
        return PAContext::Global;
    }

    ///////////// logic of taint analysis /////////////////

    fn seed_authenticated_functions(&mut self) {
        let mut seeds = Vec::new();
        let mut return_visited: HashSet<ReturnPropagationKey> = HashSet::new();

        for point in &self.semantic_points {
            if !matches!(point.kind, SemanticPointKind::AccessControl { .. }) {
                continue;
            }

            let principal = PAContextElem::Principal {
                auth_callsite: point.callsite_id,
            };

            println!("[AFG] pricipal = {:?}", principal);

            let Some(success_block) = self.get_normal_success_block(&point.caller, &point.block)
            else {
                debug!(
                    "[AFG] seed_authenticated_functions: auth_callsite = {}: no success block",
                    point.callsite_id
                );
                continue;
            };

            debug!(
                "[AFG] seed_authenticated_functions: auth_callsite = {} success continuation: {}::{}",
                point.callsite_id, point.caller, success_block
            );

            let reachable_blocks = self.normal_reachable_blocks(&point.caller, &success_block);

            debug!(
                "[AFG] seed_authenticated_functions: auth_callsite = {} reachable authenticated blocks = {:?}",
                point.callsite_id, reachable_blocks
            );

            let reaches_return = reachable_blocks.contains("Return");

            // ---------------------------------------------------------
            // A. Calls directly after the AC point inside this function
            // ---------------------------------------------------------
            for block in reachable_blocks {
                let callsites =
                    self.get_callsites_in_block(&point.caller, &block, &point.caller_context);

                debug!(
                    "[AFG] seed_authenticated_functions: find {} callsites in function = {}, block = {}, context = {:?}",
                    callsites.len(),
                    &point.caller,
                    &block,
                    &point.caller_context,
                );

                for callsite in callsites {
                    // Avoid processing the authentication call
                    // itself again.
                    if callsite.id == point.callsite_id {
                        continue;
                    }

                    self.seed_callsite_callee(callsite, &principal, &mut seeds);
                }
            }

            // ---------------------------------------------------------
            // B. Authenticated function returns:
            //    continue in its caller.
            // ---------------------------------------------------------

            if reaches_return {
                debug!("[AFG] seed_authenticated_functions: reach return block");
                self.propagate_return_to_callers(
                    &point.caller,
                    &point.caller_context,
                    &principal,
                    &mut seeds,
                    &mut return_visited,
                    ReturnPropagationMode::AfterReturnedCall,
                );
            }
        }

        for (function_key, principal) in seeds {
            self.active_principals
                .entry(function_key)
                .or_default()
                .insert(principal);
        }
    }

    fn propagate_return_to_callers(
        &self,
        returned_function: &str,      // caller
        returned_context: &PAContext, // caller context
        principal: &PAContextElem,
        seeds: &mut Vec<(FunctionKey, PAContextElem)>,
        visited: &mut HashSet<ReturnPropagationKey>,
        pos_mode: ReturnPropagationMode,
    ) {
        let visit_key = (
            returned_function.to_string(),
            returned_context.clone(),
            principal.clone(),
        );

        if !visited.insert(visit_key) {
            return;
        }

        debug!(
            "[AFG] propagate_return_to_callers: propagate return from function={} ctx={:?} principal={:?}",
            returned_function, returned_context, principal,
        );

        let callsites = self.get_callers_of_function(returned_function, returned_context);

        // No callers => reached root, e.g. main.
        if callsites.is_empty() {
            debug!(
                "[AFG] propagate_return_to_callers: reached root function {}",
                returned_function
            );
            return;
        }

        for caller_callsite in callsites {
            self.process_return_into_caller(caller_callsite, principal, seeds, visited, pos_mode);
        }
    }

    fn process_return_into_caller(
        &self,
        callsite: PACallSite<'m>,
        principal: &PAContextElem,
        seeds: &mut Vec<(FunctionKey, PAContextElem)>,
        visited: &mut HashSet<ReturnPropagationKey>,
        pos_mode: ReturnPropagationMode,
    ) {
        // Extract owned information first.
        let (caller, caller_block, caller_context) = {
            (
                callsite.caller.clone(),
                callsite.block.clone(),
                callsite.context.clone(),
            )
        };

        debug!(
            "[AFG] process_return_into_caller: caller={} block={} after callsite={:?}",
            caller, caller_block, callsite,
        );

        // ---------------------------------------------------------
        // A. Remaining calls in SAME block after returning call
        // ---------------------------------------------------------

        let later_callsites: Vec<PACallSite<'_>> =
            self.get_callsites_after_in_block(&caller, &caller_block, callsite.id, pos_mode);

        debug!(
            "[AFG] process_return_into_caller: find {} later_callsites = {:?}",
            later_callsites.len(),
            later_callsites
        );

        for callsite in later_callsites {
            self.seed_authenticated_callsite(callsite, principal, seeds);
        }

        // ---------------------------------------------------------
        // B. Successor blocks
        // ---------------------------------------------------------

        let mut reachable_blocks = HashSet::new();
        debug!(
            "[AFG] process_return_into_caller: caller = {}, reachable blocks = {:?}",
            caller, reachable_blocks,
        );

        if let Some(successor) = self.get_normal_success_block(&caller, &caller_block) {
            reachable_blocks.extend(self.normal_reachable_blocks(&caller, &successor));
        }

        // ---------------------------------------------------------
        // C. Seed calls in those blocks
        // ---------------------------------------------------------

        for block in &reachable_blocks {
            if block == "Return" {
                continue;
            }

            let callsites = self.get_callsites_in_block(&caller, &block, &caller_context);
            debug!(
                "[AFG] process_return_into_caller: find {} callsites = {:?}",
                callsites.len(),
                callsites
            );

            for callsite in callsites {
                self.seed_authenticated_callsite(callsite, principal, seeds);
            }
        }

        // ---------------------------------------------------------
        // D. If caller itself reaches Return, recurse upward
        // ---------------------------------------------------------

        if reachable_blocks.contains("Return") {
            debug!(
                "[AFG] process_return_into_caller: authenticated continuation reaches return of {}",
                caller
            );

            self.propagate_return_to_callers(
                &caller,
                &caller_context,
                principal,
                seeds,
                visited,
                ReturnPropagationMode::IncludeCurrentCall,
            );
        }
    }

    fn seed_authenticated_callsite(
        &self,
        callsite: PACallSite<'m>,
        principal: &PAContextElem,
        seeds: &mut Vec<(FunctionKey, PAContextElem)>,
    ) {
        let callee_info = {
            let Some(callee) = callsite.direct_callee.as_ref() else {
                return;
            };

            if !self.should_propagate_execution_into(callee) {
                return;
            }

            let callee_context = self.get_callee_context(&callsite);

            (callee.to_string(), callee_context)
        };

        debug!(
            "[AFG] authenticated callsite {:?} seeds callee {}",
            callsite, callee_info.0,
        );

        seeds.push((callee_info, principal.clone()));
    }

    fn seed_callsite_callee(
        &self,
        callsite: PACallSite<'_>,
        principal: &PAContextElem,
        seeds: &mut Vec<(FunctionKey, PAContextElem)>,
    ) {
        let Some(callee) = callsite.direct_callee.as_ref() else {
            return;
        };

        if !self.should_propagate_execution_into(callee) {
            return;
        }

        let callee_context = self.get_callee_context(&callsite);

        debug!(
            "[AFG] authenticated continuation seeds {} at callsite {:?}",
            callee, callsite,
        );

        seeds.push(((callee.to_string(), callee_context), principal.clone()));
    }

    fn should_propagate_execution_into(&self, callee: &str) -> bool {
        // Only propagate into functions belonging to the application, identified
        // by the app-crate prefix derived from the module's `main` (e.g.
        // "llm_ac_demo"). This replaces the earlier hardcoded crate name.
        if !self.app_crate.is_empty() && callee.contains(&self.app_crate) {
            return true;
        }

        false
    }

    fn propagate_function_principals(&mut self) {
        let mut worklist = VecDeque::new();

        for (function_key, principals) in &self.active_principals {
            for principal in principals {
                worklist.push_back((function_key.clone(), principal.clone()));
            }
        }

        debug!(
            "[AFG] propagate_function_principals (initial): #worklist = {}",
            worklist.len()
        );

        while let Some(((function, context), principal)) = worklist.pop_front() {
            let callsites = self.get_callsites_of_function(&function, &context);

            debug!(
                "[AFG] find {} callsites in function = {}, context = {:?}",
                callsites.len(),
                &function,
                &context,
            );

            for callsite in callsites {
                let Some(callee) = callsite.direct_callee.as_ref() else {
                    continue;
                };

                if !self.should_propagate_execution_into(callee) {
                    continue;
                }

                // Make everything owned before mutating self.
                let callee = callee.to_string();
                let callee_context = self.get_callee_context(&callsite).clone();
                let key = (callee, callee_context);

                let inserted = self
                    .active_principals
                    .entry(key.clone())
                    .or_default()
                    .insert(principal.clone());

                if inserted {
                    debug!(
                        "[AFG] propagate principal {:?}: {} -> {:?}",
                        principal, function, key.1
                    );

                    worklist.push_back((key, principal.clone()));
                }
            }
        }
    }

    fn active_principals_at_point(&self, point: &SemanticPoint) -> Vec<PAContextElem> {
        self.active_principals
            .get(&(point.caller.clone(), point.caller_context.clone()))
            .map(|principals| principals.iter().cloned().collect())
            .unwrap_or_default()
    }

    fn seed_semantic_nodes_from_active_functions(
        &mut self,
        worklist: &mut VecDeque<(PANodeId, PAContextElem)>,
    ) {
        /*
         * Collect first because calling insert_context()
         * mutably borrows self.
         */
        let mut seeds: Vec<(PANodeId, PAContextElem)> = Vec::new();

        for point in &self.semantic_points {
            let principals = self.active_principals_at_point(point);

            if principals.is_empty() {
                continue;
            }

            println!(
                "[AFG] semantic point {} {} has principals {:?}",
                point.callsite_id,
                point.callee.as_deref().unwrap_or("<unknown>"),
                principals,
            );

            match &point.kind {
                SemanticPointKind::LlmPrompt { .. } => {
                    /*
                     * Ideally use the prompt argument roles from your JSON.
                     *
                     * For now, seed arguments.
                     */
                    for arg in &point.argument_nodes {
                        for principal in &principals {
                            seeds.push((*arg, principal.clone()));
                        }
                    }
                }

                SemanticPointKind::LlmCall { .. } => {
                    /*
                     * Same comment: eventually seed only the request/prompt
                     * argument identified by the JSON signature.
                     */
                    for arg in &point.argument_nodes {
                        for principal in &principals {
                            seeds.push((*arg, principal.clone()));
                        }
                    }
                }

                SemanticPointKind::DataAccess { .. } => {
                    /*
                     * Shared data store. Seed the principal onto the written data
                     * (argument_nodes, for a write) and onto the result (for a
                     * read). Store/Load edges then carry the principal through the
                     * shared store object, so two principals reaching the same
                     * store node surface as a cross-user overlap (a write by one
                     * then a read by another is the leak).
                     */
                    for principal in &principals {
                        for arg in &point.argument_nodes {
                            seeds.push((*arg, principal.clone()));
                        }
                        if let Some(result) = point.result_node {
                            seeds.push((result, principal.clone()));
                        }
                    }
                }

                _ => {}
            }
        }

        for (node, principal) in seeds {
            self.insert_context(node, principal, worklist);
        }
    }

    fn propagate_data_contexts(&mut self, worklist: &mut VecDeque<(PANodeId, PAContextElem)>) {
        while let Some((src, ctx)) = worklist.pop_front() {
            /*
             * Normal PAG flow.
             */
            if let Some(edges) = self.outgoing.get(&src).cloned() {
                for (dst, _kind) in edges {
                    self.insert_context(dst, ctx.clone(), worklist);
                }
            }

            /*
             * Special behavior when the node is an input to
             * prompt/LLM semantic points.
             */
            self.apply_semantic_rules(src, &ctx, worklist);
        }
    }

    fn insert_context(
        &mut self,
        node: PANodeId,
        context: PAContextElem,
        worklist: &mut VecDeque<(PANodeId, PAContextElem)>,
    ) -> bool {
        let inserted = self
            .node_contexts
            .entry(node)
            .or_default()
            .insert(context.clone());

        if inserted {
            worklist.push_back((node, context));
        }

        inserted
    }

    fn apply_llm_prompt_rule(
        &mut self,
        point: &SemanticPoint,
        incoming: &PAContextElem,
        worklist: &mut VecDeque<(PANodeId, PAContextElem)>,
    ) {
        if !matches!(incoming, PAContextElem::Principal { .. }) {
            return;
        }

        let Some(result) = point.result_node else {
            return;
        };

        self.insert_context(result, incoming.clone(), worklist);
    }

    fn apply_llm_call_rule(
        &mut self,
        point: &SemanticPoint,
        provider: Option<&str>,
        incoming: &PAContextElem,
        worklist: &mut VecDeque<(PANodeId, PAContextElem)>,
    ) {
        let PAContextElem::Principal { .. } = incoming else {
            return;
        };

        let Some(result) = point.result_node else {
            return;
        };

        /*
         * LLM result belongs to the same principal.
         */
        self.insert_context(result, incoming.clone(), worklist);

        /*
         * And record which LLM produced it.
         */
        self.insert_context(
            result,
            PAContextElem::LlmApi {
                callsite_id: point.callsite_id,

                provider: provider.unwrap_or("unknown").to_string(),

                function: point
                    .callee
                    .clone()
                    .unwrap_or_else(|| "<unknown>".to_string()),
            },
            worklist,
        );
    }

    fn apply_semantic_rules(
        &mut self,
        src: PANodeId,
        incoming: &PAContextElem,
        worklist: &mut VecDeque<(PANodeId, PAContextElem)>,
    ) {
        let Some(indices) = self.semantic_points_by_input.get(&src).cloned() else {
            return;
        };

        for index in indices {
            /*
             * Clone to avoid immutable/mutable borrow conflict.
             */
            let point = self.semantic_points[index].clone();

            match &point.kind {
                SemanticPointKind::LlmPrompt { .. } => {
                    self.apply_llm_prompt_rule(&point, incoming, worklist);
                }

                SemanticPointKind::LlmCall { provider, .. } => {
                    self.apply_llm_call_rule(&point, provider.as_deref(), incoming, worklist);
                }

                _ => {}
            }
        }
    }

    // =========================================================================
    // Debugging / printing
    // =========================================================================

    pub fn get_node_by_id(&self, id: PANodeId) -> Option<PANode> {
        let node = self.nodes.get(&id);
        let Some(node) = node else {
            debug!("[PAG] get_node_by_id: cannot find node with id = {}", id);
            return None;
        };

        debug!("[PAG] get_node_by_id: find id = {} -> node = {}", id, node);

        Some(node.clone())
    }

    pub fn print_result(&self) {
        println!("\n========== Static Taint Analysis ==========");

        let mut node_ids: Vec<PANodeId> = self.node_contexts.keys().copied().collect();

        node_ids.sort();

        for node_id in node_ids {
            let Some(contexts) = self.node_contexts.get(&node_id) else {
                continue;
            };

            let has_interesting_context = contexts.iter().any(|ctx| {
                return matches!(
                    ctx,
                    PAContextElem::Principal { .. } | PAContextElem::LlmApi { .. }
                );
            });

            if !has_interesting_context {
                continue;
            }

            if let Some(node) = self.get_node_by_id(node_id) {
                println!("n{} = {:?}", node_id, node);
            } else {
                println!("n{} cannot find node by id", node_id);
            }

            for ctx in contexts {
                match ctx {
                    PAContextElem::Principal { auth_callsite } => {
                        println!("  principal: auth_callsite={}", auth_callsite);
                    }

                    PAContextElem::LlmApi {
                        callsite_id,
                        provider,
                        function,
                    } => {
                        println!(
                            "  llm: callsite_id={} provider={} function={}",
                            callsite_id, provider, function
                        );
                    }

                    _ => {}
                }
            }
        }

        self.print_llm_flows();
    }

    fn print_llm_flows(&self) {
        println!("\n========== LLM API FLOWS ==========");

        for point in &self.semantic_points {
            let SemanticPointKind::LlmCall { provider, .. } = &point.kind else {
                continue;
            };

            println!(
                "LLM callsite id = {}, callee = {}",
                point.callsite_id,
                point.callee.as_deref().unwrap_or("<unknown>")
            );

            println!("  provider: {}", provider.as_deref().unwrap_or("unknown"));
            println!("  arguments:");

            for arg_id in &point.argument_nodes {
                print!("    n{:?}: ", arg_id);

                let principals = self.principals_for_node(*arg_id);

                if principals.is_empty() {
                    println!("no principal");
                } else {
                    println!("Principal(s) auth_callsite id(s) = {:?}", principals);
                }
            }

            match point.result_node {
                Some(result) => {
                    println!("  result: n{:?}", result);

                    if let Some(contexts) = self.node_contexts.get(&result) {
                        for ctx in contexts {
                            match ctx {
                                PAContextElem::Principal { auth_callsite } => {
                                    println!("    <- Principal(auth_callsite={})", auth_callsite);
                                }

                                PAContextElem::LlmApi {
                                    callsite_id,
                                    provider,
                                    function,
                                } => {
                                    println!(
                                        "    <- LlmApi(callsite={}, provider={}, function={})",
                                        callsite_id, provider, function
                                    );
                                }

                                _ => {}
                            }
                        }
                    }
                }

                None => {
                    println!("  result: <none>");
                }
            }
        }

        println!("\n=========================================");
    }

    fn principals_for_node(&self, node_id: PANodeId) -> Vec<usize> {
        let Some(contexts) = self.node_contexts.get(&node_id) else {
            return Vec::new();
        };

        let mut principals: Vec<usize> = contexts
            .iter()
            .filter_map(|ctx| match ctx {
                PAContextElem::Principal { auth_callsite } => Some(*auth_callsite),

                _ => None,
            })
            .collect();

        principals.sort_unstable();
        principals.dedup();

        principals
    }
}
