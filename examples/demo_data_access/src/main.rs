// A compact, single-file multi-user service whose cross-user leak sits in a
// shared DATABASE, not a hand-marked cache. Users sign in with a password
// (argon2) and get a bearer token; every request is authenticated and served
// against one table that is keyed by prompt only (not by user), so one user's
// stored row can be served to another. Two users flow through the SAME handler
// and one token-decode call site, so the static model can't tell them apart.
//
// The difference from demo_dynamic: the store access carries NO hand-written AFG
// macros. It goes through catalog-matching stubs (`sqlx::query::Query::execute`
// = data-write, `sqlx::query::Query::fetch_one` = data-read) so AFG's producer
// finds them via data_access_functions.json and inserts afg_access! itself, with
// the real PANode. This exercises the data-access catalog + dynamic per-user path
// end to end. `with_afg_context` is the only AFG piece added by hand.
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

#[derive(Debug, Clone)]
struct User {
    id: u64,
    username: String,
    password_hash: String,
}

#[derive(Debug, Clone)]
struct Session {
    user_id: u64,
    username: String,
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
// Shared database (deterministic stand-in for sqlx)
// -----------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct AnswerRow {
    owner_user_id: u64,
    owner_username: String,
    answer: String,
}

// VULNERABILITY: one shared table keyed by prompt only. The requesting user is
// not part of the key, so one user's row can be returned to another. This is the
// backing store the sqlx stub reads and writes; a real app would hand sqlx a
// connection pool instead.
static TABLE: OnceLock<Mutex<HashMap<String, AnswerRow>>> = OnceLock::new();

fn table() -> &'static Mutex<HashMap<String, AnswerRow>> {
    TABLE.get_or_init(|| Mutex::new(HashMap::new()))
}

// A minimal sqlx-shaped API. AFG matches `Query::fetch_one` (data-read) and
// `Query::execute` (data-write) by name; the builder steps around them are not
// cataloged. The shared TABLE stands in for the connection pool's database.
mod sqlx {
    use super::{table, AnswerRow};

    pub mod query {
        use super::{table, AnswerRow};

        pub struct Query {
            pub key: String,
            pub row: Option<AnswerRow>,
        }

        impl Query {
            /// Bind the row to store (the write path's builder step).
            pub fn with_row(mut self, row: AnswerRow) -> Self {
                self.row = Some(row);
                self
            }

            /// data-read: return the stored row for this key, if any.
            #[inline(never)]
            pub fn fetch_one(&self, _pool: &str) -> Option<AnswerRow> {
                table().lock().unwrap().get(&self.key).cloned()
            }

            /// data-write: store the bound row under this key.
            #[inline(never)]
            pub fn execute(&self, _pool: &str) -> u64 {
                let Some(row) = self.row.clone() else {
                    return 0;
                };
                table().lock().unwrap().insert(self.key.clone(), row);
                1
            }
        }
    }

    #[inline(never)]
    pub fn query(key: &str) -> query::Query {
        query::Query {
            key: key.to_string(),
            row: None,
        }
    }
}

// -----------------------------------------------------------------------------
// User directory and service
// -----------------------------------------------------------------------------

static USERS: OnceLock<HashMap<String, User>> = OnceLock::new();

fn users() -> &'static HashMap<String, User> {
    USERS.get_or_init(|| {
        let alice = User {
            id: 1,
            username: "alice".to_string(),
            password_hash: hash_password("alice-password"),
        };
        let bob = User {
            id: 2,
            username: "bob".to_string(),
            password_hash: hash_password("bob-password"),
        };
        HashMap::from([(alice.username.clone(), alice), (bob.username.clone(), bob)])
    })
}

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

// The connection pool handle; a real app threads this through from app state.
const POOL: &str = "postgres://app";

async fn handle(req: Request) -> String {
    // Per-request authentication: decode the bearer token to get the principal.
    let session = match jsonwebtoken::decode(req.token.as_str(), &jsonwebtoken::DecodingKey, &jsonwebtoken::Validation) {
        Ok(data) => match users().get(&data.claims.sub) {
            Some(user) => Session {
                user_id: user.id,
                username: user.username.clone(),
            },
            None => return String::new(),
        },
        Err(_) => return String::new(),
    };

    // data-read: query the shared table for this prompt (AFG inserts afg_access
    // here from the catalog; there is no hand-written macro).
    let hit = sqlx::query(&req.prompt).fetch_one(POOL);
    if let Some(row) = hit {
        if row.owner_user_id != session.user_id {
            println!(
                "[leak] {} was served a row owned by {}",
                session.username, row.owner_username
            );
        }
        return row.answer;
    }

    // Miss: compute an answer, then store it under the prompt for anyone.
    let client = async_openai::Client::new();
    let answer = client.chat().create(&req.prompt);
    let row = AnswerRow {
        owner_user_id: session.user_id,
        owner_username: session.username,
        answer: answer.clone(),
    };
    // data-write: insert the row (AFG inserts afg_access here from the catalog).
    let _ = sqlx::query(&req.prompt).with_row(row).execute(POOL);
    answer
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    // 1) Password sign-in mints a per-user bearer token.
    let alice_token = login("alice", "alice-password").expect("alice sign-in");
    let bob_token = login("bob", "bob-password").expect("bob sign-in");

    // 2) Two users issue requests through the same handler. Both read the shared
    //    table, so the two principals meet at the same data-access node.
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

    // 3) bob re-issues alice's earlier request and is served alice's stored row.
    //    This is the cross-user leak through the shared table.
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
