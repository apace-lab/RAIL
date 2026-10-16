// Self-contained demo for the context finder: the two-user shared-cache leak,
// plus stubbed LLM and access-control calls whose paths match the CRUX catalogs
// (signatures/llm_api_functions.json, signatures/ac_functions.json) by suffix /
// last-two-segment short-name. Stubbed so it compiles with no external crates.
// Compile with an LLVM-19 rustc (see README's "how to config"):
//   cd examples/llm_ac_demo/
//   rustc main.rs --crate-name llm_ac_demo --emit=llvm-ir -o llm_ac_demo.ll

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;

// ---- LLM SDK stubs (match llm_api_functions.json) ----
pub mod async_openai {
    pub mod chat {
        pub struct Chat;
        impl Chat {
            #[inline(never)]
            pub fn create(&self, request: &str) -> String {
                format!("(openai answer for '{}')", request)
            }
        }
    }
}

pub mod ollama_rs {
    pub struct Ollama;
    impl Ollama {
        #[inline(never)]
        pub fn generate(&self, request: &str) -> String {
            format!("(ollama answer for '{}')", request)
        }
    }
}

// ---- access-control stubs (match ac_functions.json) ----
pub mod actix_identity {
    pub struct Identity {
        pub id: String,
    }
    impl Identity {
        #[inline(never)]
        pub fn id(&self) -> Result<String, ()> {
            Ok(self.id.clone())
        }
    }
}

pub mod jsonwebtoken {
    #[inline(never)]
    pub fn decode(token: &str) -> bool {
        !token.is_empty()
    }
}

pub mod casbin {
    pub struct CoreApi;
    impl CoreApi {
        #[inline(never)]
        pub fn enforce(&self, sub: &str, act: &str) -> bool {
            !sub.is_empty() && !act.is_empty()
        }
    }
}

pub mod bcrypt {
    #[inline(never)]
    pub fn verify(password: &str, hash: &str) -> bool {
        password == hash
    }
}

pub mod argon2 {
    pub struct Argon2;
    // real argon2 exposes verify_password via the PasswordVerifier trait
    pub trait PasswordVerifier {
        fn verify_password(&self, password: &str, hash: &str) -> bool;
    }
    impl PasswordVerifier for Argon2 {
        #[inline(never)]
        fn verify_password(&self, password: &str, hash: &str) -> bool {
            password == hash
        }
    }
}

pub mod ldap3 {
    pub struct LdapConn;
    impl LdapConn {
        #[inline(never)]
        pub fn simple_bind(&self, dn: &str, password: &str) -> bool {
            !dn.is_empty() && !password.is_empty()
        }
    }
}

pub mod oauth2 {
    // real oauth2 defines exchange_code on Client (BasicClient delegates to it)
    pub struct Client;
    impl Client {
        #[inline(never)]
        pub fn exchange_code(&self, code: &str) -> String {
            format!("token-for-{}", code)
        }
    }
}

#[inline(never)]
fn call_llm(question: &str) -> String {
    let openai = async_openai::chat::Chat;
    let ollama = ollama_rs::Ollama;
    let a = openai.create(question);
    let b = ollama.generate(question);
    if a.len() >= b.len() {
        a
    } else {
        b
    }
}

#[inline(never)]
fn authenticate(user: &str, token: &str, password: &str) -> Option<String> {
    use argon2::PasswordVerifier;

    if !jsonwebtoken::decode(token) {
        return None;
    }
    if !bcrypt::verify(password, "hash") {
        return None;
    }
    let argon = argon2::Argon2;
    if !argon.verify_password(password, "hash") {
        return None;
    }
    let conn = ldap3::LdapConn;
    if !conn.simple_bind(user, password) {
        return None;
    }
    let oauth = oauth2::Client;
    let _token = oauth.exchange_code("code");
    let identity = actix_identity::Identity {
        id: user.to_string(),
    };
    identity.id().ok()
}

#[inline(never)]
fn authorize(uid: &str, action: &str) -> bool {
    let enforcer = casbin::CoreApi;
    enforcer.enforce(uid, action)
}

fn spawn_user_query(
    shared_map: Arc<Mutex<HashMap<String, String>>>,
    question: &str,
    user: &str,
) -> thread::JoinHandle<()> {
    let question = question.to_string();
    let user = user.to_string();

    thread::spawn(move || {
        let uid = match authenticate(&user, "token", "hash") {
            Some(uid) => uid,
            None => return,
        };
        if !authorize(&uid, "query") {
            return;
        }

        let key = format!("query:{}", question);

        let cached_answer = {
            let map = shared_map.lock().unwrap();
            map.get(&key).cloned()
        };

        if let Some(answer) = cached_answer {
            println!("{} ({}) got cached answer: {}", user, uid, answer);
        } else {
            let answer = call_llm(&question);
            println!("{} got new answer: {}", user, answer);

            let mut map = shared_map.lock().unwrap();
            map.insert(key, answer);
        }
    })
}

fn main() {
    let shared_map = Arc::new(Mutex::new(HashMap::new()));

    let handle1 = spawn_user_query(shared_map.clone(), "What is my first event today?", "UserA");
    let handle2 = spawn_user_query(shared_map.clone(), "What is my first event today?", "UserB");

    handle1.join().unwrap();
    handle2.join().unwrap();
}
