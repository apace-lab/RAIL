// Single-user demo for the scheduler's synthesized second user.
//
// Only ONE real user (alice) is ever observed, so the static analysis sees a
// single principal and `afg_scheduler` SYNTHESIZES a second user
// (`afg-synthetic`). This app makes that synthesis executable: at REPLAY time,
// and only then (detected via `schedule_contains_principal`, since the schedule
// is empty during observation), it injects the synthetic user, who re-issues
// alice's prompt, hits the shared prompt-keyed cache, and reads alice's answer.
// The replay trace then shows alice WRITE and afg-synthetic READ the shared node,
// which `verify_replay` confirms as a reproduced cross-user leak.
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use afg_runtime::{schedule_contains_principal, with_afg_context, AfgContext, SYNTHETIC_PRINCIPAL};

// Bearer-token auth stand-in; AFG matches jsonwebtoken::decode and (via the
// producer) takes its first argument as the principal.
mod jsonwebtoken {
    pub struct DecodingKey;
    pub struct Validation;
    pub struct Claims {
        pub sub: String,
    }
    pub struct TokenData<T> {
        pub claims: T,
    }
    #[inline(never)]
    pub fn decode(
        token: &str,
        _key: &DecodingKey,
        _validation: &Validation,
    ) -> Result<TokenData<Claims>, ()> {
        if token.is_empty() {
            return Err(());
        }
        Ok(TokenData {
            claims: Claims {
                sub: token.to_string(),
            },
        })
    }
}

// LLM stand-in matched by the catalog.
mod async_openai {
    pub struct Client;
    impl Client {
        pub fn new() -> Self {
            Client
        }
        pub fn chat(&self) -> chat::Chat {
            chat::Chat
        }
    }
    pub mod chat {
        pub struct Chat;
        impl Chat {
            #[inline(never)]
            pub fn create(&self, request: &str) -> String {
                format!("(answer for '{request}')")
            }
        }
    }
}

// Developer-marked shared-cache accesses (not a cataloged call).
const CACHE_NODE: u64 = 5000;
const CACHE_FN: u64 = 424242;

#[derive(Clone)]
struct CacheEntry {
    owner: String,
    answer: String,
}

// VULNERABILITY: cache keyed by prompt only, shared across users.
static CACHE: OnceLock<Mutex<HashMap<String, CacheEntry>>> = OnceLock::new();
fn cache() -> &'static Mutex<HashMap<String, CacheEntry>> {
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

struct Request {
    token: String,
    prompt: String,
}

async fn handle(req: Request) -> String {
    let sub = match jsonwebtoken::decode(req.token.as_str(), &jsonwebtoken::DecodingKey, &jsonwebtoken::Validation) {
        Ok(data) => data.claims.sub,
        Err(_) => return String::new(),
    };

    if let Some(entry) = cache().lock().unwrap().get(&req.prompt).cloned() {
        afg_runtime::afg_monitor!(function = CACHE_FN);
        afg_runtime::afg_access!(node = CACHE_NODE, kind = afg_runtime::AccessKind::Read, function = CACHE_FN);
        if entry.owner != sub {
            println!("[leak] {sub} served a cached answer owned by {}", entry.owner);
        }
        return entry.answer;
    }

    let client = async_openai::Client::new();
    let answer = client.chat().create(&req.prompt);
    afg_runtime::afg_monitor!(function = CACHE_FN);
    afg_runtime::afg_access!(node = CACHE_NODE, kind = afg_runtime::AccessKind::Write, function = CACHE_FN);
    cache().lock().unwrap().insert(
        req.prompt.clone(),
        CacheEntry {
            owner: sub.clone(),
            answer: answer.clone(),
        },
    );
    answer
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let prompt = "summarize alice's private notes".to_string();

    // The one real user: writes the shared cache. In an observed run this is the
    // only principal, so the scheduler synthesizes a second user.
    let _ = with_afg_context(
        AfgContext::default(),
        handle(Request {
            token: "alice".to_string(),
            prompt: prompt.clone(),
        }),
    )
    .await;

    // Synthetic probe: only during a replay whose schedule injects the
    // synthesized user (the schedule is empty during observation, so this is
    // skipped then). The synthetic user re-issues alice's prompt and is served
    // alice's cached answer, the leak the synthesized schedule tests.
    if schedule_contains_principal(SYNTHETIC_PRINCIPAL) {
        let leaked = with_afg_context(
            AfgContext::default(),
            handle(Request {
                token: SYNTHETIC_PRINCIPAL.to_string(),
                prompt,
            }),
        )
        .await;
        println!("afg-synthetic received: {leaked}");
    }
}
