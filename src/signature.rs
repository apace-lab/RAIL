//! LLVM-side finder for SIG context points: reads the SIG catalogs
//! (llm_api_functions.json, ac_functions.json) and locates call sites in the
//! module whose demangled callee matches a catalog fn_name. This is the LLVM
//! counterpart to SIG's MIR-text find_llm_calls / find_ac_points; matching runs
//! on demangled symbols (suffix / short-name) instead of MIR-text regexes.

use either::Either;
use llvm_ir::instruction::Instruction;
use llvm_ir::terminator::Terminator;
use llvm_ir::{Constant, Module, Operand};
use log::debug;
use rustc_demangle::demangle;
use std::collections::HashMap;
use std::error::Error;
use std::path::Path;
use std::println;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SecurityTag {
    LLMAPIPrompt,
    LLMAPICalls,
    AccessControl,
    DataAccess,
}

#[derive(Debug, Clone)]
pub struct Signature {
    pub fn_name: String,
    pub category: Option<String>,

    /// for AFG use
    pub prompt_arg_index: Option<usize>, // TODO: there might be multiple prompt args, but for now we only support one
    pub prompt_role: Option<String>,
    pub result_index: Option<usize>,
    pub request_index: Option<usize>, // TODO: there might be multiple request args, but for now we only support one

    /// for DCG use
    pub behavior: Option<String>,
}

#[derive(Debug, Clone)]
pub struct SecurityPoint {
    pub kind: SecurityTag,
    pub caller: String, // for debugging purpose
    pub block: String,  // caller's basic block, for debugging purpose
    pub callee: String,
    pub matched_fn_name: String,

    pub category: Option<String>,
    pub prompt_arg_index: Option<usize>, // for llm-api-prompt, the index of the argument that is the prompt
    pub prompt_role: Option<String>, // for llm-api-prompt, the role of the prompt (system/user/developer)
    pub request_index: Option<usize>, // for llm-api-chat, the index of the argument that is the request (should include prompt)
    pub strategy: &'static str,
}

/// load fn_name signatures from an SIG catalog json, skipping the _schema_notes key
pub fn load_signatures(path: &Path) -> Result<Vec<Signature>, Box<dyn Error>> {
    let content = std::fs::read_to_string(path)?;
    let data: HashMap<String, serde_json::Value> = serde_json::from_str(&content)?;

    let mut signatures = Vec::new();

    for (lib, entries) in &data {
        if lib == "_schema_notes" {
            continue;
        }

        let Some(array) = entries.as_array() else {
            continue;
        };

        for entry in array {
            let fn_name = entry["fn_name"].as_str().unwrap_or("").to_string();
            if fn_name.is_empty() {
                continue;
            }

            debug!("[SIG] load_signatures: entry={:?}", entry);

            let category = entry
                .get("category")
                .and_then(|c| c.as_str())
                .map(|s| s.to_string());

            let prompt_arg_index = entry
                .get("prompt_arg_index")
                .and_then(|i| i.as_u64())
                .map(|i| i as usize);

            let prompt_role = entry
                .get("prompt_role")
                .and_then(|r| r.as_str())
                .map(|s| s.to_string());

            let result_index = entry
                .get("result_index")
                .and_then(|i| i.as_u64())
                .map(|i| i as usize);

            let request_index: Option<usize> = entry
                .get("request_index")
                .and_then(|i| i.as_u64())
                .map(|i| i as usize);

            let behavior: Option<String> = entry
                .get("behavior")
                .and_then(|b| b.as_str())
                .map(|s| s.to_string());

            debug!("[SIG] load_signatures: fn_name={}, category={:?}, prompt_arg_index={:?}, prompt_role={:?}, result_index={:?}, request_index={:?}, behavior={:?}",
                    fn_name, category, prompt_arg_index, prompt_role, result_index, request_index, behavior
                );

            signatures.push(Signature {
                fn_name,
                category,
                prompt_arg_index,
                prompt_role,
                result_index,
                request_index,
                behavior,
            });
        }
    }

    Ok(signatures)
}

/// scan every call/invoke in the module and record catalog matches
pub fn find_security_points(
    module: &Module,
    llm: &[Signature],
    ac: &[Signature],
    data: &[Signature],
) -> Vec<SecurityPoint> {
    let mut points = Vec::new();

    for func in &module.functions {
        let caller = &func.name;

        for block in &func.basic_blocks {
            let block_name = format!("{}", block.name);

            for instr in &block.instrs {
                if let Instruction::Call(call) = instr {
                    if let Some(callee) = callee_symbol(&call.function) {
                        if let Some(point) =
                            match_callsite(&callee, caller, &block_name, llm, ac, data)
                        {
                            points.push(point);
                        }
                    }
                }
            }

            if let Terminator::Invoke(invoke) = &block.term {
                if let Some(callee) = callee_symbol(&invoke.function) {
                    if let Some(point) = match_callsite(&callee, caller, &block_name, llm, ac, data)
                    {
                        points.push(point);
                    }
                }
            }
        }
    }

    points
}

/// match a single call site's callee against the catalogs (used both by the
/// standalone scan above and from the pointer analysis while it visits calls)
pub fn match_callsite(
    callee_mangled: &str,
    caller: &str,
    block: &str,
    llm: &[Signature],
    ac: &[Signature],
    data: &[Signature],
) -> Option<SecurityPoint> {
    let demangled = format!("{:#}", demangle(&strip_symbol(callee_mangled)));
    let candidates = candidate_paths(&demangled);

    // Match order: LLM, then access-control, then data-store. First hit wins, so a
    // symbol claimed by an earlier catalog (e.g. the reqwest::send catch-all) is
    // attributed there.
    let (kind, (sig, strategy)) = if let Some(hit) = match_any(&candidates, llm) {
        (SecurityTag::LLMAPICalls, hit)
    } else if let Some(hit) = match_any(&candidates, ac) {
        (SecurityTag::AccessControl, hit)
    } else if let Some(hit) = match_any(&candidates, data) {
        (SecurityTag::DataAccess, hit)
    } else {
        return None;
    };

    debug!(
        "[SIG] match_callsite: sig.request_index={:?}",
        sig.request_index
    );

    Some(SecurityPoint {
        kind,
        caller: format!("{:#}", demangle(&strip_symbol(caller))),
        block: block.to_string(),
        callee: demangled.to_string(),
        matched_fn_name: sig.fn_name.clone(),
        category: sig.category.clone(),
        prompt_arg_index: sig.prompt_arg_index,
        prompt_role: sig.prompt_role.clone(),
        request_index: sig.request_index,
        strategy,
    })
}

/// the callee symbol of a call/invoke, if it is a direct global reference
fn callee_symbol(
    function: &Either<llvm_ir::instruction::InlineAssembly, Operand>,
) -> Option<String> {
    let Either::Right(Operand::ConstantOperand(constant)) = function else {
        return None;
    };

    match constant.as_ref() {
        Constant::GlobalReference { name, .. } => Some(strip_symbol(&format!("{}", name))),
        _ => None,
    }
}

/// candidate paths to match a demangled callee against the catalogs. covers
/// direct calls / inherent methods (with generics stripped) and, for trait
/// dispatch `<Type as Trait>::method`, both `Type::method` and `Trait::method`.
fn candidate_paths(demangled: &str) -> Vec<String> {
    let mut out = vec![strip_turbofish(demangled)];

    if let Some(gt) = matching_angle(demangled) {
        let inner = &demangled[1..gt]; // "Type as Trait"
        let rest = &demangled[gt + 1..]; // "::method..."
        if let Some((ty, tr)) = split_as_top_level(inner) {
            out.push(strip_turbofish(&format!("{}{}", ty, rest)));
            out.push(strip_turbofish(&format!("{}{}", tr, rest)));
        }
    }

    out
}

/// split `Type as Trait` at the top-level ` as ` (ignoring any inside nested `<...>`)
fn split_as_top_level(inner: &str) -> Option<(&str, &str)> {
    let bytes = inner.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;

    while i < bytes.len() {
        match bytes[i] {
            b'<' => depth += 1,
            b'>' => depth -= 1,
            b' ' if depth == 0 && inner[i..].starts_with(" as ") => {
                return Some((&inner[..i], &inner[i + 4..]));
            }
            _ => {}
        }
        i += 1;
    }

    None
}

/// if `s` starts with '<', return the byte index of its matching '>'
fn matching_angle(s: &str) -> Option<usize> {
    if !s.starts_with('<') {
        return None;
    }

    let mut depth = 0usize;
    for (i, c) in s.char_indices() {
        match c {
            '<' => depth += 1,
            '>' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }

    None
}

fn strip_symbol(name: &str) -> String {
    name.trim_start_matches('@')
        .trim_start_matches('%')
        .trim_matches('"')
        .to_string()
}

/// remove balanced `<...>` segments (turbofish / trait-object qualifiers)
fn strip_turbofish(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut depth = 0usize;

    for c in s.chars() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(c),
            _ => {}
        }
    }

    out
}

/// try each candidate against the catalog: suffix match (handles the crate
/// prefix) first across all candidates, then last-two-segment short-name
fn match_any<'a>(
    candidates: &[String],
    signatures: &'a [Signature],
) -> Option<(&'a Signature, &'static str)> {
    for cand in candidates {
        for sig in signatures {
            if cand == &sig.fn_name || cand.ends_with(&format!("::{}", sig.fn_name)) {
                return Some((sig, "suffix"));
            }
        }
    }

    for cand in candidates {
        for sig in signatures {
            if last_two(cand) == last_two(&sig.fn_name) {
                return Some((sig, "short-name"));
            }
        }
    }

    None
}

fn last_two(path: &str) -> &str {
    match path.rmatch_indices("::").nth(1) {
        Some((idx, _)) => &path[idx + 2..],
        None => path,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sig(fn_name: &str) -> Signature {
        Signature {
            fn_name: fn_name.to_string(),
            category: None,
            prompt_arg_index: None,
            prompt_role: None,
            result_index: None,
            request_index: None,
            behavior: None,
        }
    }

    /// does any candidate for `demangled` match a catalog of just `fn_name`?
    fn matches(demangled: &str, fn_name: &str) -> bool {
        match_any(&candidate_paths(demangled), &[sig(fn_name)]).is_some()
    }

    // ---- direct calls / inherent methods ----

    #[test]
    fn direct_free_function() {
        assert!(matches("app::bcrypt::verify", "bcrypt::verify"));
    }

    #[test]
    fn inherent_method() {
        assert!(matches(
            "app::ldap3::LdapConn::simple_bind",
            "ldap3::LdapConn::simple_bind"
        ));
    }

    #[test]
    fn strips_generics_on_type() {
        assert!(matches(
            "app::oauth2::Client<Config>::exchange_code",
            "oauth2::Client::exchange_code"
        ));
    }

    #[test]
    fn strips_method_level_generics() {
        assert!(matches("app::foo::Bar::baz<i32>", "foo::Bar::baz"));
    }

    // ---- trait dispatch `<Type as Trait>::method` ----

    #[test]
    fn trait_dispatch_yields_both_type_and_trait_paths() {
        let cands = candidate_paths(
            "<app::argon2::Argon2 as app::argon2::PasswordVerifier>::verify_password",
        );
        assert!(
            cands
                .iter()
                .any(|c| c.ends_with("argon2::Argon2::verify_password")),
            "{:?}",
            cands
        );
        assert!(
            cands
                .iter()
                .any(|c| c.ends_with("argon2::PasswordVerifier::verify_password")),
            "{:?}",
            cands
        );
    }

    #[test]
    fn trait_dispatch_matches_trait_entry() {
        assert!(matches(
            "<app::argon2::Argon2 as app::argon2::PasswordVerifier>::verify_password",
            "argon2::PasswordVerifier::verify_password"
        ));
    }

    #[test]
    fn trait_dispatch_matches_type_entry() {
        // catalog entry keyed on the concrete type instead of the trait
        assert!(matches(
            "<app::casbin::Enforcer as app::casbin::CoreApi>::enforce",
            "casbin::Enforcer::enforce"
        ));
        // and on the trait (how our catalog actually keys casbin)
        assert!(matches(
            "<app::casbin::Enforcer as app::casbin::CoreApi>::enforce",
            "casbin::CoreApi::enforce"
        ));
    }

    // ---- nesting / generics on both sides ----

    #[test]
    fn nested_generics_on_type() {
        assert!(matches(
            "<app::Foo<app::Bar<i32>> as app::Trait>::method",
            "Trait::method"
        ));
        assert!(matches(
            "<app::Foo<app::Bar<i32>> as app::Trait>::method",
            "Foo::method"
        ));
    }

    #[test]
    fn generics_on_both_type_and_trait() {
        assert!(matches(
            "<app::Client<Config> as app::TokenExchange<Foo>>::exchange_code",
            "TokenExchange::exchange_code"
        ));
        assert!(matches(
            "<app::Client<Config> as app::TokenExchange<Foo>>::exchange_code",
            "Client::exchange_code"
        ));
    }

    #[test]
    fn nested_trait_projection_splits_at_outer_as() {
        // `<<T as A>::B as C>::method` must split at the OUTER ` as ` (C), not A
        let cands = candidate_paths("<<app::T as app::A>::B as app::C>::method");
        assert!(
            cands.iter().any(|c| c.ends_with("app::C::method")),
            "{:?}",
            cands
        );
        // must NOT wrongly treat A as the trait
        assert!(
            !cands.iter().any(|c| c.ends_with("app::A::method")),
            "{:?}",
            cands
        );
    }

    // ---- negatives ----

    #[test]
    fn no_match_for_unrelated_callee() {
        assert!(!matches(
            "app::alloc::vec::Vec::push",
            "jsonwebtoken::decode"
        ));
    }

    #[test]
    fn no_match_on_partial_segment() {
        // `decode_header` must not match a `decode` entry (segment boundary)
        assert!(!matches(
            "app::jsonwebtoken::decode_header",
            "jsonwebtoken::decode"
        ));
    }

    #[test]
    fn matching_angle_requires_leading_bracket() {
        assert_eq!(matching_angle("app::foo::bar"), None);
        assert!(matching_angle("<a as b>::c").is_some());
    }

    // ---- data-store catalog ----

    fn sig_cat(fn_name: &str, category: &str) -> Signature {
        Signature {
            fn_name: fn_name.to_string(),
            category: Some(category.to_string()),
            prompt_arg_index: None,
            prompt_role: None,
            result_index: None,
            request_index: None,
            behavior: None,
        }
    }

    #[test]
    fn data_access_matches_and_is_tagged() {
        let data = vec![sig_cat("sqlx::query::Query::fetch_one", "data-read")];
        // real symbols carry a crate prefix; the short-name (Query::fetch_one) match handles it
        let point = match_callsite(
            "app::sqlx_core::query::Query::fetch_one",
            "caller",
            "bb0",
            &[],
            &[],
            &data,
        )
        .expect("data-store callsite should match");
        assert_eq!(point.kind, SecurityTag::DataAccess);
        assert_eq!(point.category.as_deref(), Some("data-read"));
    }

    #[test]
    fn earlier_catalog_wins_over_data() {
        // the same symbol listed in AC and data: AC is checked first, so it wins
        let ac = vec![sig_cat("x::Store::get", "authentication")];
        let data = vec![sig_cat("x::Store::get", "data-read")];
        let point = match_callsite("app::x::Store::get", "c", "bb0", &[], &ac, &data).unwrap();
        assert_eq!(point.kind, SecurityTag::AccessControl);
    }
}
