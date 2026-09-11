use std::{format, panic};

use crate::signature::Signature;

/// our context-sensitive can be:
///     k-callsite only
///     k-object only
///     mixed callsite + object, total length k
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PAContextElem {
    CallSite {
        caller: String,
        block: String,
        callsite_id: usize,
    },

    Object {
        kind: PAObjectContextKind,
        /// where obj is allocated
        function: String,
        block: String,
        /// receiver obj node id
        id: usize,
    },

    /// AFG used for tracking principal authorization callsites
    Principal { auth_callsite: usize },

    /// AFG used for tracking LLM API callsites
    LlmApi {
        callsite_id: usize,
        provider: String,
        function: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PAObjectContextKind {
    Allocation,
    Summary,
    // ArcNew,
    // BoxNew,
    // RcNew,
    // MutexNew,
    // MutexLock,
    // ThreadSpawn,
    // ChannelCreate,
}

/// we can have:
/// k-callsite:
///   [CallSite(c1), CallSite(c2)]
/// k-object:
///   [Object(ArcNew@bb3), Object(MutexLock@bb9)]
/// mixed callsite+object:
///   [CallSite(c1), Object(ArcNew@bb3), CallSite(c2)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PAContext {
    Global,
    Elements(Vec<PAContextElem>),
    Semantics(Vec<PAContextElem>), // for AFG, not bounded by k
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PAContextMode {
    Insensitive,

    /// Keep only callsite elements, bounded by k.
    KCallSite,

    /// Keep only object elements, bounded by k.
    KObject,

    /// Keep both callsite and object elements, bounded by total k.
    KMixed,
}

impl PAContext {
    pub fn global() -> Self {
        PAContext::Global
    }

    pub fn len(&self) -> usize {
        match self {
            PAContext::Global => 0,
            PAContext::Elements(elems) => elems.len(),
            PAContext::Semantics(elems) => elems.len(),
        }
    }

    pub fn elems(&self) -> &[PAContextElem] {
        match self {
            PAContext::Global => &[],
            PAContext::Elements(elems) => elems.as_slice(),
            PAContext::Semantics(_) => &[],
        }
    }

    pub fn semantics(&self) -> &[PAContextElem] {
        match self {
            PAContext::Global => &[],
            PAContext::Elements(_) => &[],
            PAContext::Semantics(elems) => elems.as_slice(),
        }
    }

    pub fn principals(&self) -> impl Iterator<Item = &PAContextElem> {
        self.semantics()
            .iter()
            .filter(|e| matches!(e, PAContextElem::Principal { .. }))
    }

    pub fn has_principal(&self) -> bool {
        self.principals().next().is_some()
    }

    pub fn filtered_for_mode(&self, config: &PAConfig) -> Self {
        if config.context_mode == PAContextMode::Insensitive || config.default_k == 0 {
            return PAContext::Global;
        }

        let mut elems: Vec<PAContextElem> = self
            .elems()
            .iter()
            .filter(|e| match config.context_mode {
                PAContextMode::KCallSite => matches!(e, PAContextElem::CallSite { .. }),
                PAContextMode::KObject => matches!(e, PAContextElem::Object { .. }),
                PAContextMode::KMixed => true,
                PAContextMode::Insensitive => false,
            })
            .cloned()
            .collect();

        if elems.is_empty() {
            return PAContext::Global;
        }

        if elems.len() > config.default_k {
            elems = elems[elems.len() - config.default_k..].to_vec();
        }

        PAContext::Elements(elems)
    }

    pub fn push_with_config(&self, elem: PAContextElem, config: &PAConfig) -> Self {
        if config.context_mode == PAContextMode::Insensitive || config.default_k == 0 {
            return PAContext::Global;
        }

        let allowed = match (&config.context_mode, &elem) {
            (PAContextMode::KCallSite, PAContextElem::CallSite { .. }) => true,
            (PAContextMode::KObject, PAContextElem::Object { .. }) => true,
            (PAContextMode::KMixed, _) => true,
            _ => false,
        };

        if !allowed {
            return self.filtered_for_mode(config);
        }

        let mut elems: Vec<PAContextElem> = self
            .elems()
            .iter()
            .filter(|old| match config.context_mode {
                PAContextMode::KCallSite => matches!(old, PAContextElem::CallSite { .. }),
                PAContextMode::KObject => matches!(old, PAContextElem::Object { .. }),
                PAContextMode::KMixed => true,
                PAContextMode::Insensitive => false,
            })
            .cloned()
            .collect();

        elems.push(elem);

        if elems.len() > config.default_k {
            elems = elems[elems.len() - config.default_k..].to_vec();
        }

        if elems.is_empty() {
            PAContext::Global
        } else {
            PAContext::Elements(elems)
        }
    }

    pub fn key(&self) -> String {
        match self {
            PAContext::Global => "Global".to_string(),

            PAContext::Elements(elems) => elems
                .iter()
                .map(|e| match e {
                    PAContextElem::CallSite {
                        caller,
                        block,
                        callsite_id,
                    } => {
                        format!("Callsite({}:{}:{})", caller, block, callsite_id)
                    }

                    PAContextElem::Object {
                        kind,
                        function: caller,
                        block,
                        id,
                    } => {
                        format!("Obj({:?}:{}:{}:{})", kind, caller, block, id)
                    }

                    _ => panic!(
                        "Seeing wrong type of PAContext element in Elements: {:?}",
                        e
                    ),
                })
                .collect::<Vec<_>>()
                .join("/"),

            PAContext::Semantics(elems) => elems
                .iter()
                .map(|e| match e {
                    PAContextElem::LlmApi {
                        callsite_id,
                        provider,
                        function,
                    } => {
                        format!("LlmApi({}:{}:{})", callsite_id, provider, function)
                    }

                    PAContextElem::Principal { auth_callsite } => {
                        format!("Principal({})", auth_callsite)
                    }

                    _ => panic!(
                        "Seeing wrong type of PAContext element in Semantic: {:?}",
                        e
                    ),
                })
                .collect::<Vec<_>>()
                .join("/"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PAContextSelectPolicy {
    /// use our default exclusion list and only apply Global to those functions
    Default,
    /// only application (app_crate) functions carry a
    /// call context; library/runtime plumbing stays Global. this bounds the
    /// (function, context) instantiation blow-up (std/core/tokio would otherwise
    /// be re-analyzed under every distinct caller context) while keeping context
    /// where per-user precision actually matters. no-op when app_crate is empty.
    AppOnly,
    /// when (llm, access-control, data-access) catalogs are provided;
    /// then create context when seeing these functions
    AFG,

    /// when (concurrency-related) catalogs are provided;
    /// use origin-sensitive algorithm: create context when seeing thread creation/task creation
    CONCURRENCY,
}

#[derive(Debug, Clone)]
pub struct PAConfig {
    /// true when skip the analysis on basicblocks with "cleanup" and their successors
    /// these are mostly unwind paths, panic cleanup, and destructor paths.
    /// our goal is normal execution pointer flow rather than unwind/destructor behavior.
    /// default = true
    pub skip_cleanup_blocks: bool,
    /// true when we do on-the-fly to compute reachable functions
    /// default = true
    pub on_the_fly: bool,

    /// kcfa, kobj, mixed, insensitive?
    /// default = insensitive
    pub context_mode: PAContextMode,
    /// max length of context elements in a context
    /// default = 0
    pub default_k: usize,

    /// which functions we apply context-sensitivity on
    pub policy: PAContextSelectPolicy,

    /// together with AFG:
    /// (llm, access-control, data-store) catalogs; when set, matched call sites are
    /// recorded as context points while the analysis visits calls
    /// default = None
    pub context_signatures: Option<(Vec<Signature>, Vec<Signature>, Vec<Signature>)>,
}

impl Default for PAConfig {
    fn default() -> Self {
        Self {
            skip_cleanup_blocks: true,
            on_the_fly: true,
            context_mode: PAContextMode::Insensitive,
            default_k: 0,
            policy: PAContextSelectPolicy::Default,
            context_signatures: None,
        }
    }
}

impl PAConfig {
    pub fn insensitive() -> Self {
        Self {
            skip_cleanup_blocks: true,
            on_the_fly: true,
            context_mode: PAContextMode::Insensitive,
            default_k: 0,
            policy: PAContextSelectPolicy::Default,
            context_signatures: None,
        }
    }

    pub fn k_callsite(k: usize) -> Self {
        Self {
            skip_cleanup_blocks: true,
            on_the_fly: true,
            context_mode: PAContextMode::KCallSite,
            default_k: k,
            policy: PAContextSelectPolicy::Default,
            context_signatures: None,
        }
    }

    pub fn k_object(k: usize) -> Self {
        Self {
            skip_cleanup_blocks: true,
            on_the_fly: true,
            context_mode: PAContextMode::KObject,
            default_k: k,
            policy: PAContextSelectPolicy::Default,
            context_signatures: None,
        }
    }

    pub fn k_mixed(k: usize) -> Self {
        Self {
            skip_cleanup_blocks: true,
            on_the_fly: true,
            context_mode: PAContextMode::KMixed,
            default_k: k,
            policy: PAContextSelectPolicy::Default,
            context_signatures: None,
        }
    }

    pub fn afg(
        context_signatures: Option<(Vec<Signature>, Vec<Signature>, Vec<Signature>)>,
    ) -> Self {
        Self {
            skip_cleanup_blocks: true,
            on_the_fly: true,
            context_mode: PAContextMode::KCallSite, // TODO: need to update
            default_k: 1,                           // TODO: need to update
            policy: PAContextSelectPolicy::AFG,
            context_signatures: context_signatures,
        }
    }
}
