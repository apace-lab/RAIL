mod auth;
mod llm;
mod server;
mod store;

use crux_runtime::{with_crux_context, CruxContext};
use server::Request;

// A small multi-user LLM service. Users sign in with a password (argon2) and
// receive a bearer token; each request is authenticated from that token and
// served against one shared, non-user-scoped cache. Two users run the same
// handler, so the dynamic run observes both principals reaching the shared LLM
// access. A later request then shows the cache serving one user another's data.
#[tokio::main(flavor = "current_thread")]
async fn main() {
    // 1) Password sign-in mints a per-user bearer token.
    let alice_token = server::login("alice", "alice-password").expect("alice sign-in");
    let bob_token = server::login("bob", "bob-password").expect("bob sign-in");

    // 2) Two users issue requests against the shared service.
    let inbox = vec![
        Request {
            token: alice_token,
            model: "llama3".to_string(),
            prompt: "summarize alice's notes".to_string(),
        },
        Request {
            token: bob_token.clone(),
            model: "llama3".to_string(),
            prompt: "summarize bob's notes".to_string(),
        },
    ];

    let mut handles = Vec::new();
    for req in inbox {
        handles.push(tokio::spawn(with_crux_context(
            CruxContext::default(),
            server::handle(req),
        )));
    }
    for handle in handles {
        let _ = handle.await;
    }

    // 3) bob re-issues alice's earlier request. The shared cache key omits the
    //    user, so bob is served alice's cached answer. This is the cross-user leak.
    let leaked = with_crux_context(
        CruxContext::default(),
        server::handle(Request {
            token: bob_token,
            model: "llama3".to_string(),
            prompt: "summarize alice's notes".to_string(),
        }),
    )
    .await;
    println!("bob received: {leaked}");
}
