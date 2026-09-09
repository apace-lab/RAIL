// A compact, single-file multi-user LLM service that exhibits a cross-user data
// leak in the real-app shape. Users sign in with a password (argon2) and receive
// a bearer token; every request is authenticated from that token and served
// against one shared, non-user-scoped cache. Two users flow through the SAME
// handler and one token-decode call site, so the static model can't tell them
// apart. This exercises AFG's dynamic per-user path end to end. (See
// `mini-chat-service` for the same service split across modules.)
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use afg_runtime::{with_afg_context, AfgContext};
use argon2::{
    password_hash::{rand_core::OsRng, PasswordHash, PasswordHasher, PasswordVerifier, SaltString},
    Argon2,
};

// -----------------------------------------------------------------------------
// Authentication
// -----------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Role {
    User,
    Admin,
}

#[derive(Debug, Clone)]
struct User {
    id: u64,
    username: String,
    password_hash: String,
    role: Role,
}

#[derive(Debug, Clone)]
struct Session {
    user_id: u64,
    username: String,
    role: Role,
}

fn hash_password(password: &str) -> String {
    let salt = SaltString::generate(&mut OsRng);
    Argon2::default()
        .hash_password(password.as_bytes(), &salt)
        .expect("argon2 hashing failed")
        .to_string()
}

fn verify_password(password: &str, password_hash: &str) -> bool {
    let Ok(parsed) = PasswordHash::new(password_hash) else {
        return false;
    };
    Argon2::default()
        .verify_password(password.as_bytes(), &parsed)
        .is_ok()
}

// Bearer-token authentication. `jsonwebtoken` is a deterministic stand-in for the
// real crate so the demo runs under MadSim; AFG matches jsonwebtoken::decode
// (authentication) and takes its first argument, the token, as the principal.
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

// -----------------------------------------------------------------------------
// LLM endpoint (deterministic stand-in for async_openai)
// -----------------------------------------------------------------------------

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

// -----------------------------------------------------------------------------
// User directory and shared cache
// -----------------------------------------------------------------------------

static USERS: OnceLock<HashMap<String, User>> = OnceLock::new();

fn users() -> &'static HashMap<String, User> {
    USERS.get_or_init(|| {
        let alice = User {
            id: 1,
            username: "alice".to_string(),
            password_hash: hash_password("alice-password"),
            role: Role::Admin,
        };
        let bob = User {
            id: 2,
            username: "bob".to_string(),
            password_hash: hash_password("bob-password"),
            role: Role::User,
        };
        HashMap::from([(alice.username.clone(), alice), (bob.username.clone(), bob)])
    })
}

#[derive(Debug, Clone)]
struct CacheEntry {
    owner_user_id: u64,
    owner_username: String,
    answer: String,
}

// VULNERABILITY: one global cache keyed by prompt only. The requesting user is
// not part of the key, so one user's answer can be served to another.
static CACHE: OnceLock<Mutex<HashMap<String, CacheEntry>>> = OnceLock::new();

fn cache() -> &'static Mutex<HashMap<String, CacheEntry>> {
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

// -----------------------------------------------------------------------------
// Service
// -----------------------------------------------------------------------------

struct Request {
    token: String,
    prompt: String,
}

// Sign in with a password (argon2) and receive a bearer token for later
// requests. The token stands in for a signed JWT whose subject is the username.
fn login(username: &str, password: &str) -> Option<String> {
    let user = users().get(username)?;
    if verify_password(password, &user.password_hash) {
        Some(user.username.clone())
    } else {
        None
    }
}

// Developer-marked accesses to the app's shared cache (not a cataloged call, so
// the pipeline can't find it): a Write when caching, a Read when serving a hit.
const CACHE_NODE: u64 = 5000;
const CACHE_FN: u64 = 424242;

async fn handle(req: Request) -> String {
    // Per-request authentication: decode the bearer token to get the principal.
    let session = match jsonwebtoken::decode(req.token.as_str(), &jsonwebtoken::DecodingKey, &jsonwebtoken::Validation) {
        Ok(data) => match users().get(&data.claims.sub) {
            Some(user) => Session {
                user_id: user.id,
                username: user.username.clone(),
                role: user.role,
            },
            None => return String::new(),
        },
        Err(_) => return String::new(),
    };
    let _ = session.role;

    if let Some(entry) = cache().lock().unwrap().get(&req.prompt).cloned() {
        afg_runtime::afg_monitor!(function = CACHE_FN);
        afg_runtime::afg_access!(node = CACHE_NODE, kind = afg_runtime::AccessKind::Read, function = CACHE_FN);
        if entry.owner_user_id != session.user_id {
            println!(
                "[leak] {} served a cached answer owned by {}",
                session.username, entry.owner_username
            );
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
            owner_user_id: session.user_id,
            owner_username: session.username,
            answer: answer.clone(),
        },
    );
    answer
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    // 1) Password sign-in mints a per-user bearer token.
    let alice_token = login("alice", "alice-password").expect("alice sign-in");
    let bob_token = login("bob", "bob-password").expect("bob sign-in");

    // 2) Two users issue requests through the same handler.
    let a = tokio::spawn(with_afg_context(
        AfgContext::default(),
        handle(Request {
            token: alice_token,
            prompt: "summarize alice's notes".to_string(),
        }),
    ));
    let b = tokio::spawn(with_afg_context(
        AfgContext::default(),
        handle(Request {
            token: bob_token.clone(),
            prompt: "summarize bob's notes".to_string(),
        }),
    ));
    let _ = tokio::join!(a, b);

    // 3) bob re-issues alice's earlier request and is served alice's cached
    //    answer. This is the cross-user leak.
    let leaked = with_afg_context(
        AfgContext::default(),
        handle(Request {
            token: bob_token,
            prompt: "summarize alice's notes".to_string(),
        }),
    )
    .await;
    println!("bob received: {leaked}");
}
