# RAIL — Rust Analysis over IR Layers

RAIL is a static-analysis framework for Rust programs, built on their compiled
LLVM IR. It inherits control-flow/dominance/control-dependence graphs from
[`llvm-ir-analysis`](https://github.com/cdisselkoen/llvm-ir-analysis) and
extends its call graph. We add our own family of pointer (points-to)
analyses — context-insensitive, k-CFA, k-object-sensitive, k-mix — plus a taint analysis purpose-built to find cross-user data leaks between
LLM API calls and access-control checks in a Rust service. See
[Attribution](#attribution) for the per-file breakdown.

RAIL can be run as a CLI tool or used as a library (`rail-rs`, `rail_rs`
crate). As a library it is the static analysis stage of the larger AFG
pipeline: [afg_prototype](https://github.com/apace-lab/afg_prototype.git) (a sibling project, not in this repo) consumes
`rail_rs`'s `TaintAnalysis` output to instrument a target app, replay it with
MadSim, and confirm cross-user leaks dynamically. See
[TAINT_ANALYSIS.md](TAINT_ANALYSIS.md) for that library API.

## Features

<!-- - **Graph analyses**: control-flow graph, dominator/post-dominator trees, and
  control dependence graph, inherited from `llvm-ir-analysis` essentially
  unmodified; the call graph is inherited too but extended in RAIL with
  reachability queries, common-ancestor lookup, and on-the-fly edge insertion
  for the pointer analysis below. -->
- **Pointer analysis** (`--pag=`): builds a pointer assignment graph (PAG) and
  solves it to a fixed point, in several modes:
  - `insensitive` — context-insensitive.
  - `kcfa` — k-call-site-sensitive.
  - `kobj` — k-object-sensitive (see [Known issues](#known-issues)).
  - `kmix` — k-object-sensitive + k-CFA hybrid (see [Known issues](#known-issues)).
  - `afg` — same solver, but also matches call sites against the LLM-API /
    access-control signature catalogs and records where they land in the
    points-to graph.
- **static taint analysis** (`taint_analysis` module): given the `afg`-mode
  PAG, propagates a *principal* (a static auth call site) from each
  access-control check through the graph, and reports every node reachable
  from two or more principals — a static candidate for a cross-user leak —
  plus the LLM/auth call sites (`SemanticPoint`s) it matched along the way.

## Project layout

```
src/
  main.rs                     CLI entry point
  lib.rs                      ModuleAnalysis / CrossModuleAnalysis (public API)
  call_graph.rs                call graph construction
  control_flow_graph.rs        per-function CFG
  dominator_tree.rs             (post-)dominator trees
  control_dep_graph.rs         control dependence graph
  functions_by_type.rs          index of functions by signature
  pointer_assignment_graph.rs  PAG construction + solver (all --pag modes)
  context.rs                   principal / context propagation for AFG
  taint_analysis.rs            AFG taint analysis engine (public: taint_analysis)
  signature.rs                 loads the LLM-API / access-control JSON catalogs
  util.rs                      CLI flag parsing, file output helpers

signatures/                   default LLM API / access-control / input-source
                               catalogs (Rust and JS/TS variants) used by --api=/--ac=
examples/                     sample Rust crates used as analysis fixtures
tests/                        pre-compiled .ll fixtures + PAG integration tests
```
Provenance (what's inherited from `llvm-ir-analysis` vs. original to RAIL) is
covered per-file in [Attribution](#attribution); this section is just what
each file is for.


## Prerequisites

RAIL parses real LLVM IR, so its LLVM version must match the toolchain that
produced the `.ll` file:

- LLVM **19.1.7**, via rustc **1.82.0** -- rustc **1.86.0**. 
- `zlib1g-dev` (`sudo apt install zlib1g-dev`).

Check what you have:

```bash
llvm-config --version      # should print 19.x.x
rustc -vV | grep LLVM      # confirms the rustc <-> LLVM mapping above
```

If you're not on LLVM 19, either install it (see
[Troubleshooting](#troubleshooting)) or use `switch-version.sh` to switch, and
set the matching `features = ["llvm-19"]` (or the appropriate version) on the
`llvm-ir` dependency in `Cargo.toml`.

## Build

```bash
cargo build
```

## Usage

RAIL takes one or more `.ll` files (produced by `rustc --emit=llvm-ir`) and a
set of flags selecting which analyses to run and where to write them:

```
cargo run -- <input.ll> [more.ll ...] [--pag=<mode>] [--k=N] [--api=..] [--ac=..] [--info] [--cfg] [--cg]
```

| flag | effect |
|---|---|
| `--info` | dump parsed module info to `parsed_module.txt` |
| `--cfg` | dump each function's CFG to `cfg.txt` |
| `--cg` | dump the (cross-module) call graph to `cg.txt` |
| `--pag=<mode>` | build a PAG; `mode` is `insensitive`, `kcfa`, `kobj`, `kmix`, or `afg`. Writes points-to constraints to `pag.txt`, points-to sets to `points_to.txt`, and statistics to the console |
| `--k=N` | max context length, required for `kcfa` / `kobj` / `kmix` |
| `--api=<path>` | LLM-API signature catalog (`afg` mode); defaults to `signatures/llm_api_functions.json` |
| `--ac=<path>` | access-control signature catalog (`afg` mode); defaults to `signatures/ac_functions.json` |

Multiple input files are analyzed together as one cross-module program (e.g.
a crate's `lib` + `bin`, where `main` lives in the bin but most code is in the
lib).

### Generate a `.ll` input

```bash
cd examples/hello_world
rustc src/main.rs --emit=llvm-ir -o hello.ll
```

or, for a full cargo project (needed for AFG's source-location mapping, which
requires debug info):

```bash
cargo rustc -- --emit=llvm-ir -C debuginfo=2
```

### Example commands

```bash
# silence build warnings while running
RUSTFLAGS=-Awarnings cargo run -q -- tests/hello.ll

# full debug logging
RUST_LOG=rail_rs=debug cargo run -- tests/demo.ll 2> debug.log

# k-CFA pointer analysis, context depth 3
RUSTFLAGS=-Awarnings cargo run -q -- tests/llm_ac_demo.ll --pag=kcfa --k=3

# AFG mode with the default catalogs
RUSTFLAGS=-Awarnings cargo run -q -- tests/llm_api_ac.ll --pag=afg

# AFG mode with explicit catalogs
RUSTFLAGS=-Awarnings cargo run -q -- \
    tests/llm_api_ac.ll --pag=afg \
    --api=signatures/llm_api_functions.json \
    --ac=signatures/ac_functions.json
```

### AFG: finding LLM API / access-control context points

When both `--api=` and `--ac=` are given (or `afg` mode falls back to the
defaults), the analysis also locates LLM-API and access-control call sites: it
matches the demangled callee against the `fn_name`s in
`signatures/llm_api_functions.json` and `signatures/ac_functions.json`
(suffix match, then last-two-segment short name). Results go to
`context_points.txt`, with each matched call site listed alongside the
points-to sets of its arguments and result (resolved after the fixed point) —
tying the catalog match back into the pointer analysis.

`examples/llm_ac_demo/` is a small self-contained fixture for this: a
two-user shared-cache demo plus stubbed LLM calls (`async-openai`, `ollama`)
and access-control calls (`jsonwebtoken`, `bcrypt`, `argon2`, `ldap3`,
`oauth2`, `actix-identity`, `casbin`) whose paths match the catalogs.
Regenerate its `.ll` with an LLVM-19 rustc:

```bash
cd examples/llm_ac_demo/
rustc main.rs --crate-name llm_ac_demo --emit=llvm-ir -o llm_ac_demo.ll
```

### Using `rail_rs` as a library

The static taint analysis is also exposed as a library API (`ModuleAnalysis` /
`CrossModuleAnalysis::taint_analysis`), for consumers like `afg_prototype` that
need the `TaintAnalysis` result (semantic points, principal contexts, node
source locations) directly rather than the text dump the CLI writes. See
[TAINT_ANALYSIS.md](TAINT_ANALYSIS.md) for the full API, including a minimal
working example and field reference.

## Examples

| example | what it demonstrates |
|---|---|
| `hello_world` | minimal fixture for exercising the CLI end to end |
| `demo`, `tokio-demo`, `channel-test` | small fixtures for specific IR shapes (async, channels) |
| `llm-api-demo` | intentionally vulnerable interactive CLI: multi-user auth, OpenAI/Ollama SDK calls, an in-memory cache keyed without the user ID — so one user can receive another's cached LLM response |
| `llm-api-ac` | backend-only variant: Argon2 password auth, JWT bearer tokens, role-based authorization |
| `llm_ac_demo` | fixture matching the default LLM-API / access-control signature catalogs, for exercising `--pag=afg` |
| `mini-chat-service` | real-app-shaped multi-user LLM service (argon2 auth, bearer tokens, shared cache) used to validate the full AFG pipeline end to end |
| `demo_dynamic` (`afg_dyn_demo`) | single-file MadSim counterpart to `mini-chat-service`, for exercising AFG's dynamic per-user replay stage |

## Known issues

- **`kobj`**: direct calls are recorded as `DirectCall` edges and resolved
  lazily by the solver from `pts(receiver_arg)`. For most cases that points-to
  set never gets populated, so the callee is never analyzed — this loses
  reachability (missing functions/nodes/edges) and needs revisiting.
- **`kmix`**: built on `kobj`, so it inherits the same issue.
- `insensitive` and `kcfa` are solid; `afg` (which uses call-site context) is
  the mode exercised most.

## Special-cased handling

To keep the pointer analysis tractable, a few LLVM/Rust constructs get
dedicated handling rather than generic modeling:

- Solver-level: `on_the_fly` call resolution, `skip_cleanup_blocks`, `vtable`
  dispatch.
- Special Rust functions (`handle_special_rust_functions`): `llvm.memcpy`,
  heap allocation (`__rust_alloc`, `alloc::alloc::alloc`, `raw_vec::RawVec`),
  `Deref::deref`, `Arc::clone`.

## Running on a real-world crate (`lencx/ChatGPT`)

```bash
git clone https://github.com/lencx/ChatGPT.git
cd ChatGPT/src-tauri
rustup run nightly-2025-02-01 cargo rustc --bin chatgpt --release -- \
    -C codegen-units=1 --emit=llvm-ir=/tmp/chatgpt_lencx.ll

cd <rail>
RUSTFLAGS=-Awarnings cargo run -q --release -- /tmp/chatgpt_lencx.ll --pag=afg \
  --api=signatures/llm_api_functions.json \
  --ac=signatures/ac_functions.json
```

## Troubleshooting

**`openssl-sys` / `javascriptcore-rs-sys` build errors mentioning `pkg-config`**
— install `pkg-config` and the missing system dev packages (these come from
transitive dependencies of example crates, not from `rail-rs` itself).

**`could not find native static library 'Polly'`** — install the matching
LLVM version and its Polly dev package:

```bash
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh <version>
sudo apt update
sudo apt install libpolly-19-dev
```

**`indexmap` requires Cargo feature 'edition2024'`** — your cargo is older
than the crate needs; pin an older `indexmap`:

```bash
cargo update -p indexmap --precise 2.7.1
```

## Attribution

Built on [`llvm-ir`](https://github.com/cdisselkoen/llvm-ir) as a library.
Several files started from
[`llvm-ir-analysis`](https://github.com/cdisselkoen/llvm-ir-analysis), to
varying degrees:

| file | from `llvm-ir-analysis` | original to RAIL |
|---|---|---|
| `src/dominator_tree.rs` | copied verbatim | — |
| `src/control_dep_graph.rs` | copied verbatim | — |
| `src/functions_by_type.rs` | copied, +1 derive attribute | — |
| `src/control_flow_graph.rs` | `ControlFlowGraph`/`CFGNode` construction | `print_cfg()` |
| `src/call_graph.rs` | `CallGraph::new()` and the basic `callers`/`callees` accessors | `pub` graph field, `empty()`, `has_call_edge`/`add_call_edge`, `is_reachable`, `find_closest_common_root` (+ helpers), `print_call_graph()` |
| `src/lib.rs` | the `ModuleAnalysis`/`CrossModuleAnalysis`/`FunctionAnalysis`/`SimpleCache` structure and its existing call-graph/CFG accessors | all wiring for `pointer_assignment_graph`, `taint_analysis`, `signature`, `context`, `util` |

### Original to RAIL (no upstream equivalent, not derived from anything)
- `src/pointer_assignment_graph.rs` — the PAG construction and all pointer-analysis solver modes (`insensitive`/`kcfa`/`kobj`/`kmix`/`afg`)
- `src/context.rs` — the `PAContext`/`PAContextElem` principal/context model
- `src/signature.rs` — the LLM-API/access-control catalog matching
- `src/taint_analysis.rs` — the AFG taint-propagation engine
- `src/util.rs` — CLI flag/file helpers
- `src/main.rs` — the CLI itself
- everything under `signatures/`, `examples/`, `tests/`