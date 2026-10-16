# crux_dyn_demo

A compact, single-file MadSim demo of a cross-user data leak in the real-app
shape. Users sign in with a password (argon2) and receive a bearer token; every
request is authenticated from that token and served against one shared,
non-user-scoped cache. Two users (alice, bob) flow through the **same** handler
and one token-decode call site, so the static model can't tell them apart. This
exercises CRUX's **dynamic per-user** path end to end.

It is the single-file counterpart to `mini-chat-service` (same service, split
across modules there). `argon2` is the real crate; `jsonwebtoken` and
`async_openai` are deterministic stand-ins so the demo runs under MadSim, matched
by name exactly as the real SDKs would be. argon2's `verify_password` is the
credential check; `jsonwebtoken::decode` establishes the per-request principal.

## Run the full CRUX pipeline on it

```sh
# 1) compile the demo to LLVM IR with debug info
cd ../rail_rs/examples/demo_dynamic
cargo +1.85.0 rustc --bin crux_dyn_demo -- --emit=llvm-ir -Cdebuginfo=2 -Ccodegen-units=1
LL=$(ls -t target/debug/deps/crux_dyn_demo-*.ll | head -1)

# 2) producer -> instrument -> observe(MadSim) -> analyze -> schedule -> replay
cd ../../../crux
LLVM_SYS_191_PREFIX=/opt/homebrew/opt/llvm@19 \
  ./target/debug/afg --llvm-ir "../rail_rs/examples/demo_dynamic/$LL" \
  --project ../rail_rs/examples/demo_dynamic \
  --run-dir /tmp/crux_dyn --cargo-cmd run --seeds 1 --replay
```

Expected:

- `instrumentation sites: 1 auth, 1 llm-access` (argon2's `verify_password` is
  detected but not used as the principal source)
- the app prints `[leak] bob served a cached answer owned by alice`
- `observe/scopes.json` -> `overlaps: [{left: alice, right: bob, shared_nodes: [..]}]`
- `schedule/schedule-000.json` -> a two-user replay schedule on the shared node

CRUX auto-inserts `crux_auth!` (principal from the token-decode call's first
argument) and `crux_monitor!`/`crux_access!` at the LLM call; the app itself is
uninstrumented.
