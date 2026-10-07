//! Structural inference of application access-control checks, so they need not be listed in
//! the catalog by hand.
//!
//! A library catalog (sqlx, diesel, argon2, casbin, ...) generalizes across apps, but an
//! application's own access-control check is bespoke (e.g. vaultwarden's
//! `Cipher::is_accessible_to_user`) and no library catalog can know it. Such a check has a
//! recognizable shape: a call whose boolean (or `Result`/`Option` discriminant) result
//! **controls a conditional branch** -- it gates subsequent code. This module finds those
//! calls and returns the inferred check **function names** (in catalog `Type::method` short
//! form). Feeding them to the normal matcher as synthetic access-control signatures means the
//! rest of the pipeline (construction-call argument binding, async-method matching, dominance)
//! handles them exactly like cataloged checks.
//!
//! This is a heuristic: a non-authorization predicate on a resource (e.g. `is_empty`) used in
//! a guard can be mistaken for a check, which could clear an access it dominates and binds. It
//! is therefore opt-in (the producer gates it behind a flag) and restricted to the application
//! crate, and the dynamic stage remains the authoritative verdict. It recovers the app-level
//! checks that would otherwise be a manual per-app catalog entry.

use either::Either;
use llvm_ir::instruction::Instruction;
use llvm_ir::{Module, Name, Operand, Terminator};
use std::collections::{BTreeSet, HashMap};

use crate::signature::{callee_short_name, path_crate};

/// Infer application access-control check functions from guard-shaped control flow across the
/// given modules. Returns catalog `Type::method` short names, restricted to `app_crate` (empty
/// = no restriction). These are meant to be added as synthetic `authorization` signatures.
pub fn inferred_check_functions<'a>(
    modules: impl IntoIterator<Item = &'a Module>,
    app_crate: &str,
    data_access: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for m in modules {
        for f in &m.functions {
            // result SSA name -> callee symbol, for both Call instructions and Invoke
            // terminators (async calls lower to invokes); and the defining instruction of each
            // value we may need to trace a branch condition back through.
            let mut result_callee: HashMap<String, String> = HashMap::new();
            let mut defs: HashMap<String, &Instruction> = HashMap::new();
            // stack-slot address -> value(s) stored into it (so a load can follow the store;
            // at -O0 a call result is spilled to a slot and reloaded before the branch).
            let mut stored: HashMap<String, Vec<String>> = HashMap::new();
            // blocks that contain a call to a cataloged data-access (the protected operation):
            // a real access-control check gates one of these.
            let mut data_blocks: BTreeSet<String> = BTreeSet::new();

            for bb in &f.basic_blocks {
                let blk = bb.name.to_string();
                let mut block_calls_data = |sym: &str| {
                    if !data_access.is_empty() && data_access.contains(&callee_short_name(sym)) {
                        data_blocks.insert(blk.clone());
                    }
                };
                for inst in &bb.instrs {
                    if let Some(d) = dest_name(inst) {
                        defs.insert(d, inst);
                    }
                    match inst {
                        Instruction::Call(c) => {
                            if let Some(sym) = direct_callee(&c.function) {
                                block_calls_data(&sym);
                                if let Some(dest) = &c.dest {
                                    result_callee.insert(dest.to_string(), sym);
                                }
                            }
                        }
                        Instruction::Store(s) => {
                            if let (Some(val), Some(addr)) =
                                (operand_name(&s.value), operand_name(&s.address))
                            {
                                stored.entry(addr).or_default().push(val);
                            }
                        }
                        _ => {}
                    }
                }
                if let Terminator::Invoke(inv) = &bb.term {
                    if let Some(sym) = direct_callee(&inv.function) {
                        block_calls_data(&sym);
                        result_callee.insert(inv.result.to_string(), sym);
                    }
                }
            }

            // CFG successors + the set of blocks that return, for the deny-path test.
            let mut succ: HashMap<String, Vec<String>> = HashMap::new();
            let mut ret_blocks: BTreeSet<String> = BTreeSet::new();
            for bb in &f.basic_blocks {
                let name = bb.name.to_string();
                succ.insert(name.clone(), term_successors(&bb.term));
                if matches!(bb.term, Terminator::Ret(_)) {
                    ret_blocks.insert(name);
                }
            }

            // Every conditional-branch condition: trace it back to the call whose result it is,
            // and require the branch to be a real guard: one arm must be a short early-return
            // (the deny/error path) and the other must continue (the protected path). This
            // filters out comparisons/predicates that merely steer logic, and serves whose
            // result is matched, which would otherwise be inferred as checks.
            for bb in &f.basic_blocks {
                if let Terminator::CondBr(cb) = &bb.term {
                    let Some(cond) = operand_name(&cb.condition) else { continue };
                    let mut seen = BTreeSet::new();
                    let Some(sym) =
                        trace_to_call(&cond, &defs, &result_callee, &stored, &mut seen, 0)
                    else {
                        continue;
                    };
                    if !(app_crate.is_empty() || path_crate(&sym) == app_crate) {
                        continue;
                    }
                    let short = callee_short_name(&sym);
                    // Exclude comparison / collection predicates: they return bool and gate
                    // branches but are not access control.
                    if is_operator_method(&short) {
                        continue;
                    }
                    // A real access-control check gates a resource access: one arm reaches a
                    // cataloged data-access (the protected path) and the other returns without it
                    // (the deny path). This captures "the check decides whether the access runs"
                    // robustly (no path-length heuristic, so async error paths of any length are
                    // fine) and excludes predicates whose branch does not gate a data-access.
                    if guards_data_access(
                        &cb.true_dest.to_string(),
                        &cb.false_dest.to_string(),
                        &succ,
                        &ret_blocks,
                        &data_blocks,
                    ) {
                        out.insert(short);
                    }
                }
            }
        }
    }
    out
}

/// Trace an SSA value back through boolean/discriminant-shaping instructions to the call whose
/// result it originates from. Returns the callee symbol if found. Depth-limited and cycle-safe.
fn trace_to_call(
    name: &str,
    defs: &HashMap<String, &Instruction>,
    result_callee: &HashMap<String, String>,
    stored: &HashMap<String, Vec<String>>,
    seen: &mut BTreeSet<String>,
    depth: usize,
) -> Option<String> {
    if depth > 16 || !seen.insert(name.to_string()) {
        return None;
    }
    if let Some(sym) = result_callee.get(name) {
        return Some(sym.clone());
    }
    let inst = defs.get(name)?;
    // A load follows the value(s) stored into its address (the spill/reload of a call result).
    if let Instruction::Load(l) = inst {
        if let Some(addr) = operand_name(&l.address) {
            if let Some(vals) = stored.get(&addr) {
                for v in vals {
                    if let Some(sym) = trace_to_call(v, defs, result_callee, stored, seen, depth + 1) {
                        return Some(sym);
                    }
                }
            }
        }
        return None;
    }
    for op in cond_operands(inst) {
        if let Some(sym) = trace_to_call(&op, defs, result_callee, stored, seen, depth + 1) {
            return Some(sym);
        }
    }
    None
}

/// The operands worth following when tracing a branch condition back to a call result. We
/// deliberately do NOT traverse `icmp`: an access-control check returns a boolean that is
/// branched on directly (via `trunc .. to i1` / boolean ops), whereas an `icmp` on a branch
/// condition is almost always an enum-discriminant comparison -- a `Poll`/`Option`/`Result`
/// match from the async poll loop or a `let-else`, not a check. Skipping `icmp` filters those
/// out and keeps the boolean-value guards that are the access-control idiom.
fn cond_operands(inst: &Instruction) -> Vec<String> {
    let mut v = Vec::new();
    let mut push = |o: &Operand| {
        if let Some(n) = operand_name(o) {
            v.push(n);
        }
    };
    match inst {
        Instruction::Xor(x) => {
            push(&x.operand0);
            push(&x.operand1);
        }
        Instruction::And(a) => {
            push(&a.operand0);
            push(&a.operand1);
        }
        Instruction::Or(o) => {
            push(&o.operand0);
            push(&o.operand1);
        }
        Instruction::ZExt(z) => push(&z.operand),
        Instruction::SExt(s) => push(&s.operand),
        Instruction::Trunc(t) => push(&t.operand),
        Instruction::Freeze(fr) => push(&fr.operand),
        Instruction::ExtractValue(e) => push(&e.aggregate),
        Instruction::Phi(p) => {
            for (val, _) in &p.incoming_values {
                push(val);
            }
        }
        // Load is handled specially in trace_to_call (it follows the store into the address).
        _ => {}
    }
    v
}

/// The SSA destination an instruction defines, for the trace-back map.
fn dest_name(inst: &Instruction) -> Option<String> {
    match inst {
        Instruction::ICmp(i) => Some(i.dest.to_string()),
        Instruction::Xor(x) => Some(x.dest.to_string()),
        Instruction::And(a) => Some(a.dest.to_string()),
        Instruction::Or(o) => Some(o.dest.to_string()),
        Instruction::ZExt(z) => Some(z.dest.to_string()),
        Instruction::SExt(s) => Some(s.dest.to_string()),
        Instruction::Trunc(t) => Some(t.dest.to_string()),
        Instruction::Freeze(fr) => Some(fr.dest.to_string()),
        Instruction::ExtractValue(e) => Some(e.dest.to_string()),
        Instruction::Phi(p) => Some(p.dest.to_string()),
        Instruction::Load(l) => Some(l.dest.to_string()),
        _ => None,
    }
}

fn operand_name(op: &Operand) -> Option<String> {
    match op {
        Operand::LocalOperand { name, .. } => Some(name.to_string()),
        _ => None,
    }
}

/// A branch is an access-control guard over a data-access iff exactly one arm reaches a
/// cataloged data-access block (the protected path) and the other arm reaches a `ret` without
/// reaching that data-access (the deny/error path that skips the resource access). This is the
/// semantic "the check decides whether the access runs," independent of path length, so it is
/// robust to async error paths of any length and excludes predicates whose branch does not gate
/// a data-access. Requires a data-access catalog (empty catalog => no guards).
fn guards_data_access(
    t: &str,
    f: &str,
    succ: &HashMap<String, Vec<String>>,
    ret_blocks: &BTreeSet<String>,
    data_blocks: &BTreeSet<String>,
) -> bool {
    if data_blocks.is_empty() {
        return false;
    }
    let t_data = arm_reaches_block(t, succ, data_blocks);
    let f_data = arm_reaches_block(f, succ, data_blocks);
    // exactly one arm performs the protected data-access
    if t_data == f_data {
        return false;
    }
    // the other (deny) arm must return (exit without the access), not merge back into it
    let deny = if t_data { f } else { t };
    arm_reaches_block(deny, succ, ret_blocks)
}

/// Method names that return bool and gate branches but are comparisons / collection predicates,
/// never access control.
fn is_operator_method(short: &str) -> bool {
    let method = short.rsplit("::").next().unwrap_or(short);
    matches!(
        method,
        "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "cmp" | "partial_cmp" | "hash"
            | "is_empty" | "is_some" | "is_none" | "is_ok" | "is_err" | "contains"
            | "contains_key" | "starts_with" | "ends_with" | "eq_ignore_ascii_case"
            | "equivalent" | "equal" | "clone"
    )
}

/// Whether `start` can reach a block in `targets` within a bounded BFS.
fn arm_reaches_block(
    start: &str,
    succ: &HashMap<String, Vec<String>>,
    targets: &BTreeSet<String>,
) -> bool {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut frontier = vec![start.to_string()];
    seen.insert(start.to_string());
    let mut steps = 0usize;
    while !frontier.is_empty() && steps < 4096 {
        let mut next = Vec::new();
        for b in &frontier {
            if targets.contains(b) {
                return true;
            }
            if let Some(ss) = succ.get(b) {
                for s in ss {
                    if seen.insert(s.clone()) {
                        next.push(s.clone());
                    }
                }
            }
            steps += 1;
        }
        frontier = next;
    }
    false
}

/// The successor block names of a terminator.
fn term_successors(term: &Terminator) -> Vec<String> {
    match term {
        Terminator::Br(b) => vec![b.dest.to_string()],
        Terminator::CondBr(c) => vec![c.true_dest.to_string(), c.false_dest.to_string()],
        Terminator::Switch(s) => {
            let mut v: Vec<String> = s.dests.iter().map(|(_, n)| n.to_string()).collect();
            v.push(s.default_dest.to_string());
            v
        }
        Terminator::Invoke(i) => {
            vec![i.return_label.to_string(), i.exception_label.to_string()]
        }
        _ => Vec::new(),
    }
}

/// The raw symbol of a direct call/invoke callee (a global function reference).
fn direct_callee(function: &Either<llvm_ir::instruction::InlineAssembly, Operand>) -> Option<String> {
    let Either::Right(Operand::ConstantOperand(c)) = function else {
        return None;
    };
    match c.as_ref() {
        llvm_ir::Constant::GlobalReference { name, .. } => Some(name.to_string()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(env_var: &str, name: &str) -> String {
        std::env::var(env_var)
            .unwrap_or_else(|_| format!("{}/tests/fixtures/{}", env!("CARGO_MANIFEST_DIR"), name))
    }

    #[test]
    fn infers_the_app_check_from_guard_shape() {
        // In the complex async demo, `if !is_accessible(&c).await { return }` is a guard, so
        // `is_accessible` must be inferred as a check; `to_json` (not used in a branch) must not.
        let path = fixture("AFG_COMPLEX_LL", "complex_dbg.ll");
        let m = llvm_ir::Module::from_ir_path(&path).expect("parse complex fixture");
        let data: BTreeSet<String> = ["complex::to_json".to_string()].into_iter().collect();
        let inferred = inferred_check_functions([&m], "complex", &data);
        assert!(
            inferred.iter().any(|s| s.contains("is_accessible")),
            "expected is_accessible to be inferred as a check, got {inferred:?}"
        );
        assert!(
            !inferred.iter().any(|s| s.contains("to_json")),
            "to_json is a serve, not a guard, and must not be inferred: {inferred:?}"
        );
    }
}
