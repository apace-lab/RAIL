//! Access-control dominance analysis (the automated enforcement pass).
//!
//! AFG's correctness property is the *dominance invariant*: every access to a shared
//! resource must be dominated, on all paths, by an access-control check bound to that
//! resource. This module computes the negation automatically: a data-access site is a
//! *candidate* (a potential cross-user leak) when there exists a path from an entry point
//! to it along which no *covering* check occurs. A check covers an access iff
//!   1. the check's basic block **dominates** the access's basic block (block-level, via
//!      the per-function dominator tree), and
//!   2. the check is **bound to the same resource** as the access (their argument
//!      points-to sets intersect).
//!
//! Condition (1) is the block-level precision (a check in a sibling branch, or after the
//! access, does not count). Condition (2) is the resource binding (a check that is present
//! but guards a *different* resource, for example an organization-membership check where a
//! per-collection check was required, does not count). Together they catch both the
//! total-absence class (no check at all, e.g. lemmy, tabby) and the insufficient-check
//! class (a present but wrong check, e.g. vaultwarden).
//!
//! The control-flow dominance is supplied by a [`DominanceOracle`] (backed by rail-rs's
//! per-function dominator trees in the real pipeline, and by an explicit relation in
//! tests). Resource binding degrades gracefully: when a check or access has no known
//! resource set, binding is assumed (the analysis falls back to pure block-level control
//! dominance for that pair), so missing points-to information never silently clears an
//! access it should not.

use either::Either;
use llvm_ir::instruction::Instruction;
use llvm_ir::{Constant, Module, Name, Operand};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub type FnName = String;
pub type BlockId = String;
/// A resource identity (a points-to target id in the real pipeline).
pub type ResourceId = u64;

/// Answers "does block `a` dominate block `b` within `function`?" (reflexive: a==b true).
pub trait DominanceOracle {
    fn dominates(&self, function: &str, a: &str, b: &str) -> bool;
}

/// A dominance oracle backed by a precomputed set of true (function, dominator, dominated)
/// block pairs. The real pipeline fills this from rail-rs's per-function dominator trees;
/// it is reflexive by construction (a == b is always dominated).
#[derive(Debug, Clone, Default)]
pub struct PrecomputedOracle {
    pub pairs: BTreeSet<(String, String, String)>,
}

impl DominanceOracle for PrecomputedOracle {
    fn dominates(&self, function: &str, a: &str, b: &str) -> bool {
        a == b
            || self
                .pairs
                .contains(&(function.to_string(), a.to_string(), b.to_string()))
    }
}

#[derive(Debug, Clone)]
pub struct CheckSite {
    pub function: FnName,
    pub block: BlockId,
    pub resources: BTreeSet<ResourceId>,
    /// Debug-info-recovered type signatures of this site's pointer arguments (hashed
    /// `Struct` / `Struct.field` names). Empty when no debug info is available. Used to
    /// keep resources of different concrete types from binding when the points-to sets
    /// over-merge under opaque pointers. See [`type_disjoint`].
    pub type_tag: BTreeSet<ResourceId>,
}

#[derive(Debug, Clone)]
pub struct AccessSite {
    pub id: usize,
    pub function: FnName,
    pub block: BlockId,
    pub resources: BTreeSet<ResourceId>,
    /// Debug-info-recovered type signatures of this access's pointer arguments (see
    /// [`CheckSite::type_tag`]).
    pub type_tag: BTreeSet<ResourceId>,
}

#[derive(Debug, Clone)]
pub struct CallSite {
    pub caller: FnName,
    pub callee: FnName,
    pub block: BlockId,
}

#[derive(Debug, Clone, Default)]
pub struct DominanceFacts {
    pub checks: Vec<CheckSite>,
    pub accesses: Vec<AccessSite>,
    pub calls: Vec<CallSite>,
    pub entries: BTreeSet<FnName>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    pub access_id: usize,
    pub function: FnName,
    pub reason: String,
}

#[derive(Debug, Clone, Default)]
pub struct DominanceReport {
    pub candidates: Vec<Candidate>,
    pub total_accesses: usize,
    pub dominated_accesses: usize,
    pub unreachable_accesses: usize,
}

/// Resource binding: two sites are bound to the same resource iff their resource sets
/// intersect. An empty set means "unknown", in which case binding is assumed so the
/// analysis degrades to pure control-flow dominance (never clears an access on the basis
/// of missing points-to information).
fn bound(a: &BTreeSet<ResourceId>, b: &BTreeSet<ResourceId>) -> bool {
    a.is_empty() || b.is_empty() || !a.is_disjoint(b)
}

/// Two debug-type tags are disjoint iff both are known (non-empty) and share no type
/// signature. When either is unknown this is `false` (no evidence of a type mismatch).
/// Debug types come from DWARF metadata and are precise, so when they disagree the two
/// sites touch different concrete types; treating that as "not bound" can only add
/// candidates (it never clears an access), so it is sound.
fn type_disjoint(a: &BTreeSet<ResourceId>, b: &BTreeSet<ResourceId>) -> bool {
    !a.is_empty() && !b.is_empty() && a.is_disjoint(b)
}

/// A check covers an access's resource iff the points-to resource sets bind AND their
/// debug types are not provably disjoint. The debug-type gate refines the points-to
/// binding where opaque pointers over-merge distinct resources of different types.
fn covers(
    check_res: &BTreeSet<ResourceId>,
    check_type: &BTreeSet<ResourceId>,
    acc_res: &BTreeSet<ResourceId>,
    acc_type: &BTreeSet<ResourceId>,
) -> bool {
    bound(check_res, acc_res) && !type_disjoint(check_type, acc_type)
}

/// Extract every direct call site with its basic block, from LLVM modules. Callee names
/// are the raw mangled names (matching `SemanticPoint::caller` and `Function::name`); block
/// names use `Name`'s display (matching `SemanticPoint::block`). Indirect calls are skipped.
pub fn call_sites_with_blocks<'a>(modules: impl IntoIterator<Item = &'a Module>) -> Vec<CallSite> {
    let mut out = Vec::new();
    for m in modules {
        for f in &m.functions {
            for bb in &f.basic_blocks {
                let block = bb.name.to_string();
                for inst in &bb.instrs {
                    if let Instruction::Call(call) = inst {
                        if let Either::Right(Operand::ConstantOperand(cref)) = &call.function {
                            if let Constant::GlobalReference { name: Name::Name(n), .. } =
                                cref.as_ref()
                            {
                                out.push(CallSite {
                                    caller: f.name.clone(),
                                    callee: n.to_string(),
                                    block: block.clone(),
                                });
                            }
                        }
                    }
                }
            }
        }
    }
    out
}

fn reachable(facts: &DominanceFacts) -> BTreeSet<FnName> {
    let mut succ: BTreeMap<&FnName, Vec<&FnName>> = BTreeMap::new();
    for c in &facts.calls {
        succ.entry(&c.caller).or_default().push(&c.callee);
    }
    let mut seen: BTreeSet<FnName> = facts.entries.clone();
    let mut q: VecDeque<FnName> = facts.entries.iter().cloned().collect();
    while let Some(f) = q.pop_front() {
        if let Some(cs) = succ.get(&f) {
            for callee in cs {
                if seen.insert((*callee).clone()) {
                    q.push_back((*callee).clone());
                }
            }
        }
    }
    seen
}

/// Functions reachable from some entry along a path with no check *bound to `res`*
/// dominating the relevant call site. Computed to a fixed point.
fn entered_unchecked_for(
    facts: &DominanceFacts,
    dom: &dyn DominanceOracle,
    res: &BTreeSet<ResourceId>,
    res_type: &BTreeSet<ResourceId>,
) -> BTreeSet<FnName> {
    // sanitized(C, bb): some check in C, bound to `res` (resource and type), dominates `bb`.
    let sanitized = |caller: &str, block: &str| -> bool {
        facts.checks.iter().any(|c| {
            c.function == caller
                && covers(&c.resources, &c.type_tag, res, res_type)
                && dom.dominates(caller, &c.block, block)
        })
    };
    let mut eu: BTreeSet<FnName> = facts.entries.clone();
    let mut changed = true;
    while changed {
        changed = false;
        for call in &facts.calls {
            if eu.contains(&call.caller)
                && !sanitized(&call.caller, &call.block)
                && !eu.contains(&call.callee)
            {
                eu.insert(call.callee.clone());
                changed = true;
            }
        }
    }
    eu
}

/// Run the dominance analysis. An access is a candidate iff it is reachable, no check in
/// its own function covers it (block-dominates and is resource-bound), and there is an
/// unchecked-for-its-resource path to its function.
pub fn analyze(facts: &DominanceFacts, dom: &dyn DominanceOracle) -> DominanceReport {
    let reach = reachable(facts);
    let mut report = DominanceReport {
        total_accesses: facts.accesses.len(),
        ..Default::default()
    };
    for a in &facts.accesses {
        if !reach.contains(&a.function) {
            report.unreachable_accesses += 1;
            continue;
        }
        let locally_covered = facts.checks.iter().any(|c| {
            c.function == a.function
                && covers(&c.resources, &c.type_tag, &a.resources, &a.type_tag)
                && dom.dominates(&a.function, &c.block, &a.block)
        });
        if locally_covered {
            report.dominated_accesses += 1;
            continue;
        }
        let eu = entered_unchecked_for(facts, dom, &a.resources, &a.type_tag);
        if eu.contains(&a.function) {
            report.candidates.push(Candidate {
                access_id: a.id,
                function: a.function.clone(),
                reason: format!(
                    "data-access#{} in {} has a path from an entry with no access-control check bound to its resource dominating it",
                    a.id, a.function
                ),
            });
        } else {
            report.dominated_accesses += 1;
        }
    }
    report
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A dominance oracle backed by an explicit set of (function, dominator, dominated)
    /// pairs. Reflexive by construction.
    struct MapOracle {
        pairs: BTreeSet<(String, String, String)>,
    }
    impl MapOracle {
        fn new(pairs: &[(&str, &str, &str)]) -> Self {
            MapOracle {
                pairs: pairs.iter().map(|(f, a, b)| (f.to_string(), a.to_string(), b.to_string())).collect(),
            }
        }
    }
    impl DominanceOracle for MapOracle {
        fn dominates(&self, function: &str, a: &str, b: &str) -> bool {
            a == b || self.pairs.contains(&(function.to_string(), a.to_string(), b.to_string()))
        }
    }

    fn res(ids: &[u64]) -> BTreeSet<ResourceId> {
        ids.iter().copied().collect()
    }
    fn chk(f: &str, b: &str, r: &[u64]) -> CheckSite {
        CheckSite { function: f.into(), block: b.into(), resources: res(r), type_tag: res(&[]) }
    }
    fn acc(id: usize, f: &str, b: &str, r: &[u64]) -> AccessSite {
        AccessSite { id, function: f.into(), block: b.into(), resources: res(r), type_tag: res(&[]) }
    }
    /// check with an explicit debug-type tag
    fn chk_t(f: &str, b: &str, r: &[u64], t: &[u64]) -> CheckSite {
        CheckSite { function: f.into(), block: b.into(), resources: res(r), type_tag: res(t) }
    }
    /// access with an explicit debug-type tag
    fn acc_t(id: usize, f: &str, b: &str, r: &[u64], t: &[u64]) -> AccessSite {
        AccessSite { id, function: f.into(), block: b.into(), resources: res(r), type_tag: res(t) }
    }
    fn call(c: &str, e: &str, b: &str) -> CallSite {
        CallSite { caller: c.into(), callee: e.into(), block: b.into() }
    }
    fn facts(
        checks: Vec<CheckSite>,
        accesses: Vec<AccessSite>,
        calls: Vec<CallSite>,
        entries: &[&str],
    ) -> DominanceFacts {
        DominanceFacts {
            checks,
            accesses,
            calls,
            entries: entries.iter().map(|s| s.to_string()).collect(),
        }
    }

    // A bound check that dominates the access, in the same function, covers it.
    #[test]
    fn intra_dominating_bound_check_covers() {
        let f = facts(vec![chk("h", "bb0", &[1])], vec![acc(1, "h", "bb1", &[1])], vec![], &["h"]);
        let dom = MapOracle::new(&[("h", "bb0", "bb1")]);
        assert!(analyze(&f, &dom).candidates.is_empty());
    }

    // RESOURCE BINDING FIX: a check that dominates the access but guards a DIFFERENT
    // resource does not cover it (vaultwarden intra shape).
    #[test]
    fn intra_dominating_check_wrong_resource_is_candidate() {
        let f = facts(vec![chk("h", "bb0", &[2])], vec![acc(1, "h", "bb1", &[1])], vec![], &["h"]);
        let dom = MapOracle::new(&[("h", "bb0", "bb1")]);
        let r = analyze(&f, &dom);
        assert_eq!(r.candidates.len(), 1, "wrong-resource check must not clear the access");
    }

    // DEBUG-TYPE FIX: the points-to resource sets over-merge (they share pointee 9, so
    // `bound` is true) and the check dominates the access, but the debug types are disjoint
    // (check guards type 100, access touches type 200). This is the vaultwarden shape under
    // opaque pointers: points-to collapsed the Organization and the Cipher, but the DWARF
    // types still tell them apart, so the access remains a candidate.
    #[test]
    fn type_disjoint_check_is_candidate() {
        let f = facts(
            vec![chk_t("h", "bb0", &[9], &[100])],
            vec![acc_t(1, "h", "bb1", &[9], &[200])],
            vec![],
            &["h"],
        );
        let dom = MapOracle::new(&[("h", "bb0", "bb1")]);
        let r = analyze(&f, &dom);
        assert_eq!(r.candidates.len(), 1, "type-disjoint check must not clear the access");
    }

    // The debug-type gate does not over-restrict: when the resources bind AND the debug
    // types match, a dominating check still covers the access (no false candidate).
    #[test]
    fn type_matching_check_still_covers() {
        let f = facts(
            vec![chk_t("h", "bb0", &[9], &[100])],
            vec![acc_t(1, "h", "bb1", &[9], &[100])],
            vec![],
            &["h"],
        );
        let dom = MapOracle::new(&[("h", "bb0", "bb1")]);
        assert!(analyze(&f, &dom).candidates.is_empty(), "matching type must still clear");
    }

    // Degradation safety: when one side has no debug type (empty tag), the type gate is
    // inert and the pass falls back to pure points-to binding (here it covers).
    #[test]
    fn type_unknown_falls_back_to_resource_binding() {
        let f = facts(
            vec![chk("h", "bb0", &[9])],                 // no type tag on the check
            vec![acc_t(1, "h", "bb1", &[9], &[200])],    // access has a type tag
            vec![],
            &["h"],
        );
        let dom = MapOracle::new(&[("h", "bb0", "bb1")]);
        assert!(
            analyze(&f, &dom).candidates.is_empty(),
            "unknown type must not fabricate a mismatch"
        );
    }

    // BLOCK-LEVEL FIX: a check for the right resource that does NOT dominate the access
    // (it sits in a sibling branch) does not cover it.
    #[test]
    fn intra_check_not_dominating_is_candidate() {
        let f = facts(vec![chk("h", "bbT", &[1])], vec![acc(1, "h", "bbF", &[1])], vec![], &["h"]);
        // bbT does not dominate bbF (they are two arms of a branch).
        let dom = MapOracle::new(&[]);
        let r = analyze(&f, &dom);
        assert_eq!(r.candidates.len(), 1, "a check that does not dominate must not clear the access");
    }

    // No check at all (lemmy shape): candidate.
    #[test]
    fn no_check_is_candidate() {
        let f = facts(vec![], vec![acc(1, "report", "bb0", &[1])], vec![], &["report"]);
        let dom = MapOracle::new(&[]);
        assert_eq!(analyze(&f, &dom).candidates.len(), 1);
    }

    // Sibling unchecked path (tabby shape): the same read is reached from a guarded
    // resolver and an unguarded conversion path; the unguarded path makes it a candidate.
    #[test]
    fn sibling_unchecked_path_is_candidate() {
        let f = facts(
            vec![chk("resolver", "bb0", &[1])],
            vec![acc(1, "read", "bb0", &[1])],
            vec![call("resolver", "read", "bb0"), call("convert", "read", "bb0")],
            &["resolver", "convert"],
        );
        // In resolver, the check (bb0) dominates the call (bb0): reflexive.
        let dom = MapOracle::new(&[]);
        let r = analyze(&f, &dom);
        assert_eq!(r.candidates.len(), 1, "the unguarded sibling path must be flagged");
    }

    // Interprocedural: a bound check in the caller dominating the call covers the callee's
    // access (dufs shape: guard then serve).
    #[test]
    fn interproc_bound_check_covers_callee() {
        let f = facts(
            vec![chk("handler", "bb0", &[1])],
            vec![acc(1, "serve", "bb0", &[1])],
            vec![call("handler", "serve", "bb1")],
            &["handler"],
        );
        // In handler, the check block bb0 dominates the call block bb1.
        let dom = MapOracle::new(&[("handler", "bb0", "bb1")]);
        assert!(analyze(&f, &dom).candidates.is_empty(), "guarded call must clear the callee access");
    }

    // VAULTWARDEN interprocedural: the caller performs a check that dominates the call,
    // but it is bound to a different resource (membership, not the collection), so the
    // callee's cipher access is still a candidate.
    #[test]
    fn interproc_wrong_resource_is_candidate() {
        let f = facts(
            vec![chk("get_org_details", "bb0", &[9])], // checks the org (resource 9)
            vec![acc(1, "_get_org_details", "bb0", &[1])], // reads a cipher (resource 1)
            vec![call("get_org_details", "_get_org_details", "bb1")],
            &["get_org_details"],
        );
        let dom = MapOracle::new(&[("get_org_details", "bb0", "bb1")]);
        let r = analyze(&f, &dom);
        assert_eq!(r.candidates.len(), 1, "a check for a different resource must not clear the access");
    }

    // A call cycle must not hang the fixpoint.
    #[test]
    fn cycle_terminates() {
        let f = facts(
            vec![],
            vec![acc(1, "b", "bb0", &[1])],
            vec![call("a", "b", "bb0"), call("b", "a", "bb0")],
            &["a"],
        );
        let dom = MapOracle::new(&[]);
        assert_eq!(analyze(&f, &dom).candidates.len(), 1);
    }

    // Dead code (unreachable from any entry) is not a candidate.
    #[test]
    fn unreachable_is_not_candidate() {
        let f = facts(vec![], vec![acc(1, "orphan", "bb0", &[1])], vec![call("entry", "other", "bb0")], &["entry"]);
        let dom = MapOracle::new(&[]);
        let r = analyze(&f, &dom);
        assert!(r.candidates.is_empty());
        assert_eq!(r.unreachable_accesses, 1);
    }

    // Missing resource info degrades to control-only dominance: an unknown-resource check
    // that dominates still covers an unknown-resource access.
    #[test]
    fn unknown_resource_degrades_to_control_dominance() {
        let f = facts(vec![chk("h", "bb0", &[])], vec![acc(1, "h", "bb1", &[])], vec![], &["h"]);
        let dom = MapOracle::new(&[("h", "bb0", "bb1")]);
        assert!(analyze(&f, &dom).candidates.is_empty());
    }
}
