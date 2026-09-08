# mini-chat-service

A small, real-app-shaped multi-user LLM service, used to check the AFG pipeline
end to end. Users sign in with a password (argon2) and receive a bearer token;
each request is authenticated from that token and served against one shared
answer cache. The cache key omits the requesting user, so one user's answer can
be served to another. This is the cross-user leak AFG is meant to surface.

The code is split across modules the way a real service would be:

| file | role | AFG relevance |
|------|------|---------------|
| `src/auth.rs`   | argon2 `hash_password`/`verify_password`, `User`/`Session`/`Role`, and a `jsonwebtoken::decode` bearer-token check | credential check (argon2) + the per-request principal source (`decode`) |
| `src/store.rs`  | the user directory and the global, non-user-scoped cache (`CacheKey` without the user; `CacheEntry` records the owner) | the shared resource the leak flows through |
| `src/llm.rs`    | `async_openai::chat::Chat::create` | LLM call -> per-user access node |
| `src/server.rs` | `login()` (password -> token) and `handle()` (decode -> authorize -> cache -> LLM) | the single handler every user runs through |
| `src/main.rs`   | mints tokens for alice/bob, serves their requests, then replays alice's request as bob | users come from request data, not hardcoded spawns |

`argon2` is the real crate. `jsonwebtoken` and `async_openai` are deterministic
stand-ins for their real counterparts so the example runs under MadSim; AFG
matches all three by name (last two path segments), exactly as it would the real
SDKs.

Two auth mechanisms appear, on purpose: argon2 `verify_password` is the
credential check at sign-in, and `jsonwebtoken::decode` establishes the principal
on each request. AFG derives the principal from an auth call's first argument,
which is the token for `decode` but the *password bytes* for argon2, so the
instrumenter uses `decode` for the principal and leaves the argon2 site alone.
Both users run the same handler and the same token-decode call site, so the
static model sees a single principal; the dynamic run is what tells them apart.

## Run the full AFG pipeline on it

```sh
# 1) compile the example to LLVM IR with debug info
cd ../rail_rs/examples/mini-chat-service
cargo +1.85.0 rustc --bin mini_chat_service -- --emit=llvm-ir -Cdebuginfo=2 -Ccodegen-units=1
LL=$(ls -t target/debug/deps/mini_chat_service-*.ll | head -1)

# 2) producer -> instrument -> observe(MadSim) -> analyze -> schedule -> replay
cd ../../../afg_prototype
LLVM_SYS_191_PREFIX=/opt/homebrew/opt/llvm@19 \
  ./target/debug/afg --llvm-ir "../rail_rs/examples/mini-chat-service/$LL" \
  --project ../rail_rs/examples/mini-chat-service \
  --run-dir /tmp/afg_mini --cargo-cmd run --seeds 1 --replay
```

Expected:

- `instrumentation sites: 1 auth, 1 llm-access` (argon2's `verify_password` is
  detected but not used as the principal source)
- the app prints `[leak] bob served a cached answer owned by alice`
- `observe/scopes.json` -> `overlaps: [{left: alice, right: bob, shared_nodes: [..]}]`
- `schedule/schedule-000.json` -> a two-user replay schedule on the shared node

AFG auto-inserts `afg_auth!` (principal from the token-decode call's first
argument) and `afg_monitor!`/`afg_access!` at the LLM call; the example source
itself is uninstrumented.
