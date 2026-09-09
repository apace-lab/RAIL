# afg_data_demo

A compact, single-file MadSim demo of a cross-user data leak whose shared state
is a **database**, not a hand-marked cache. It is the data-store counterpart to
`demo_dynamic`: same multi-user shape (argon2 password sign-in, a bearer token
decoded per request, two users through one handler), but the leak lives in one
table keyed by prompt only, so one user's stored row is served to another.

The point of this demo is the **data-access catalog**. The store access carries
NO hand-written AFG macros. It goes through catalog-matching stubs:

- `sqlx::query::Query::execute` -> matched as **data-write**
- `sqlx::query::Query::fetch_one` -> matched as **data-read**

so AFG's producer finds them via `rail-rs/signatures/data_access_functions.json`
and inserts `afg_access!` itself, with the real PANode. `argon2` is the real
crate; `jsonwebtoken` and `async_openai` are the same deterministic stand-ins used
in `demo_dynamic`. The only AFG piece added by hand is `with_afg_context` (per
request context, which the instrumenter does not yet insert).

## Run the full AFG pipeline on it

```sh
# 1) compile the demo to LLVM IR with debug info
cd rail-rs/examples/demo_data_access
cargo +1.85.0 rustc --bin afg_data_demo -- --emit=llvm-ir -Cdebuginfo=2 -Ccodegen-units=1
LL=$(ls -t target/debug/deps/afg_data_demo-*.ll | head -1)

# 2) producer -> instrument -> observe(MadSim) -> analyze -> schedule -> replay
#    (pass absolute catalog paths; the defaults are relative to afg_prototype)
SIGS=$(cd ../../signatures && pwd)
cd ../../../afg_prototype
LLVM_SYS_191_PREFIX=/opt/homebrew/opt/llvm@19 \
  ./target/debug/afg --llvm-ir "../rail-rs/examples/demo_data_access/$LL" \
  --project ../rail-rs/examples/demo_data_access \
  --llm-api "$SIGS/llm_api_functions.json" \
  --ac "$SIGS/ac_functions.json" \
  --data-access "$SIGS/data_access_functions.json" \
  --run-dir /tmp/afg_data_run --cargo-cmd run --seeds 1 --replay
```

To see what AFG inserted (none of it is in this source):

```sh
grep -n 'afg_runtime::' /tmp/afg_data_run/instrumented/app/src/main.rs
```

## What it demonstrates

The producer reports `1 auth, 1 llm-access, 2 data-access` sites: the two
data-access sites are the auto-discovered DB read and write. On the trace, both
principals reach the shared table, so `analyze_traces` reports a cross-user
overlap on the data-access nodes:

- node for `fetch_one` (data-read): both alice and bob read the same table -> the
  classic unscoped-read (IDOR) shape.
- node for `execute` (data-write): both write the same table.

and the run prints the actual leak: `[leak] bob was served a row owned by alice`.

Point the dashboard at the run to see it:

```sh
cd ../afg_prototype/afg-dashboard
cargo run -- --run-dir /tmp/afg_data_run   # then open http://127.0.0.1:8090
```

## Note on the replay verdict

The replay verdicts here are `not reproduced`, and that is correct. AFG's
write-then-read verdict looks for a write and a read on the **same** PANode. For
a real database the write (`execute`) and the read (`fetch_one`) are different
methods, so they are different nodes; the leak spans two nodes (write on the
execute node, read on the fetch_one node) linked through the shared table. The
single-node write-then-read verdict is what `demo_dynamic` shows with its one
hand-marked cache node. Here the cross-user overlap on the shared table and the
runtime leak are the signal.
