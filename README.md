# RAIL: Rust Analysis over IR Layers

RAIL is a whole-program static analysis framework for Rust applications built over compiled LLVM IR. It inherits control-flow, dominator-tree, and control-dependence graph infrastructure from [`llvm-ir-analysis`](https://github.com/cdisselkoen/llvm-ir-analysis) and extends call-graph construction with on-the-fly indirect call resolution. On top of these representations, RAIL implements context-insensitive and context-sensitive pointer analyses alongside **Principal-Sensitive Analysis (PSA)** and **Access-Control Enforcement (ACE)** to detect cross-user data-isolation bugs in concurrent and asynchronous Rust services. See [Attribution](#attribution) for the per-file breakdown.

RAIL can be run as a standalone CLI binary or linked as a Rust library (`rail-rs` / `rail_rs`). As a library, RAIL provides the static analysis stages of **CRUX**: [`crux`](https://github.com/apace-lab/crux.git) consumes RAIL's PSA and ACE results to construct an instrumentation plan, instrument candidate Rust call sites with R4, and verify cross-user data leaks at runtime. See [PSA.md](PSA.md) for library API documentation.

## Features

- **Pointer analysis** (`--pag=`): constructs a pointer assignment graph (PAG) with on-the-fly call-graph updates and solves points-to constraints to a fixed point in several modes:
  - `insensitive` - context-insensitive Andersen-style solver.
  - `kcfa` - k-call-site-sensitive solver.
  - `kobj` - k-object-sensitive solver (see [Known issues](#known-issues)).
  - `kmix` - hybrid k-object-sensitive + k-CFA solver (see [Known issues](#known-issues)).
  - `crux` - builds the PAG while matching demangled call sites against the authentication/authorization, resource-access, and LLM service signature catalogs.
- **Principal-Sensitive Analysis (PSA)** (`psa` module): given a `crux`-mode PAG, introduces a distinct principal context at each authentication or authorization check site and propagates principal contexts upward across helper returns, downward across callees, and along value-carrying PAG edges to identify multi-principal nodes and governing checks.
- **Access-Control Enforcement (ACE)** (`ace`, `guard_inference`, and `debuginfo` modules): recovers Rust composite types from DWARF debug metadata over opaque LLVM pointers (`ptr`), infers boolean check functions, and checks intraprocedural dominance, resource binding, and resource-type matching across call-graph paths.

## Project Layout

```text
src/
  main.rs                      CLI entry point
  lib.rs                       ModuleAnalysis / CrossModuleAnalysis (public API)
  call_graph.rs                Call graph construction and reachability queries
  control_flow_graph.rs        Per-function CFG
  dominator_tree.rs            (Post-)dominator trees
  control_dep_graph.rs         Control dependence graph
  functions_by_type.rs         Index of functions by LLVM signature
  pointer_assignment_graph.rs  PAG construction and solver (all --pag modes)
  context.rs                   Principal and call-site context domains (PAContext)
  psa.rs                       Principal-Sensitive Analysis (PSA) engine
  ace.rs                       Access-Control Enforcement (ACE) dominance/binding pass
  guard_inference.rs           Structural inference of boolean authorization functions
  debuginfo.rs                 DWARF composite/member type and source-location recovery
  signature.rs                 JSON API signature catalog loader and symbol matcher
  util.rs                      CLI flag parsing and output helpers

signatures/                    Declarative JSON API signature catalogs
examples/                      Sample Rust crates used as analysis and end-to-end fixtures
tests/                         Pre-compiled .ll fixtures and PAG integration tests
```

## Prerequisites

RAIL parses LLVM IR bitcode/text directly, so its LLVM library version must match the Rust toolchain used to emit `.ll` files:

- LLVM **19.1.7**, via `rustc` **1.82.0** to **1.86.0** (e.g., `1.85.0`).
- `zlib1g-dev` (`sudo apt install zlib1g-dev` on Ubuntu/Debian).

Verify your local toolchain:

```bash
llvm-config --version      # should print 19.x.x
rustc -vV | grep LLVM      # confirms rustc's bundled LLVM version
```

If needed, use `switch-version.sh` or set `LLVM_SYS_191_PREFIX` to point to your LLVM 19 installation.

## Build

```bash
cargo build
```

## Usage

RAIL accepts one or more `.ll` files (emitted via `rustc --emit=llvm-ir`) and flags selecting which analyses to run:

```text
cargo run -- <input.ll> [more.ll ...] [--pag=<mode>] [--k=N] [--api=..] [--ac=..] [--data=..] [--info] [--cfg] [--cg]
```

| Flag | Effect |
|---|---|
| `--info` | Write parsed module summary to `parsed_module.txt` |
| `--cfg` | Write each function's CFG to `cfg.txt` |
| `--cg` | Write the cross-module call graph to `cg.txt` |
| `--pag=<mode>` | Build a PAG (`insensitive`, `kcfa`, `kobj`, `kmix`, or `crux`), writing constraints to `pag.txt` and points-to sets to `points_to.txt` |
| `--k=N` | Maximum context depth (required for `kcfa`, `kobj`, and `kmix`) |
| `--api=<path>` | Sensitive LLM service catalog (`crux` mode); defaults to `signatures/llm_api_functions.json` |
| `--ac=<path>` | Authentication/authorization catalog (`crux` mode); defaults to `signatures/ac_functions.json` |
| `--data=<path>` | Resource-access catalog (`crux` mode); defaults to `signatures/data_access_functions.json` |

Multiple `.ll` files passed on the command line are analyzed together as one cross-module program (e.g., workspace crates or a crate's `lib` + `bin` targets).

### Generating `.ll` Inputs

Single file:

```bash
cd examples/hello_world
rustc src/main.rs --emit=llvm-ir -o hello.ll
```

Full Cargo crate with DWARF debug metadata (used by CRUX for source-location and struct-type recovery):

```bash
cargo rustc -- --emit=llvm-ir -C debuginfo=2 -C codegen-units=1
```

### Example Commands

```bash
# Basic run without warnings
RUSTFLAGS=-Awarnings cargo run -q -- tests/hello.ll

# Verbose debug logging
RUST_LOG=rail_rs=debug cargo run -- tests/demo.ll 2> debug.log

# k-CFA pointer analysis with k=3
RUSTFLAGS=-Awarnings cargo run -q -- tests/llm_ac_demo.ll --pag=kcfa --k=3

# CRUX mode with default signature catalogs
RUSTFLAGS=-Awarnings cargo run -q -- tests/llm_api_ac.ll --pag=crux

# CRUX mode with explicit catalog paths
RUSTFLAGS=-Awarnings cargo run -q -- \
    tests/llm_api_ac.ll --pag=crux \
    --api=signatures/llm_api_functions.json \
    --ac=signatures/ac_functions.json \
    --data=signatures/data_access_functions.json
```

### Catalog Matching in `crux` Mode

In `--pag=crux` mode, RAIL matches demangled call targets against the `fn_name` entries in `signatures/llm_api_functions.json`, `signatures/ac_functions.json`, and `signatures/data_access_functions.json` (by full suffix match, then last-two-segment `Type::method` match). Matched sites are written to `context_points.txt` alongside the resolved points-to sets of their arguments and return values.

`examples/llm_ac_demo/` provides a self-contained two-user shared-cache fixture with stubbed LLM (`async-openai`, `ollama`) and authentication/authorization (`jsonwebtoken`, `bcrypt`, `argon2`, `ldap3`, `oauth2`, `actix-identity`, `casbin`) calls:

```bash
cd examples/llm_ac_demo/
rustc main.rs --crate-name llm_ac_demo --emit=llvm-ir -o llm_ac_demo.ll
```

### Using `rail_rs` as a Library

PSA and ACE are exposed through `ModuleAnalysis` and `CrossModuleAnalysis` (e.g., `CrossModuleAnalysis::psa("crux", None)` returning `PrincipalSensitiveAnalysis`, plus `rail_rs::ace` and `rail_rs::debuginfo`) for downstream tools such as [`crux`](https://github.com/apace-lab/crux.git). See [PSA.md](PSA.md) for a complete working example and API reference.

## Examples

| Example | Description |
|---|---|
| `hello_world` | Minimal fixture exercising the CLI end to end |
| `demo`, `tokio-demo`, `channel-test` | Small fixtures covering async tasks and channel IR patterns |
| `llm-api-demo` | Multi-user CLI fixture with OpenAI/Ollama calls and a non-user-scoped shared cache |
| `llm-api-ac` | Backend fixture with Argon2 password checks, JWT bearer tokens, and role checks |
| `llm_ac_demo` | Fixture matching the default signature catalogs under `--pag=crux` |
| `mini-chat-service` | Multi-module multi-user LLM chat service (Argon2 auth, JWT tokens, shared cache) for end-to-end CRUX validation |
| `demo_dynamic` (`crux_dyn_demo`) | Single-file MadSim counterpart to `mini-chat-service` exercising CRUX's dynamic replay stage |
| `demo_data_access` (`crux_data_demo`) | Database-backed multi-user fixture exercising catalog-driven SQL read/write discovery |

## Known Issues

- **`kobj`**: direct calls are recorded as `DirectCall` edges and resolved lazily from `pts(receiver_arg)`; when receiver points-to sets remain empty, callees are skipped.
- **`kmix`**: inherits the same limitation from `kobj`.
- `insensitive`, `kcfa`, and `crux` modes are well-tested; `crux` is the primary mode used by CRUX.

## Special-Cased Rust/LLVM Constructs

- Solver-level: on-the-fly indirect call resolution, cleanup/unwind block filtering (`skip_cleanup_blocks`), and trait-object vtable dispatch.
- Rust intrinsics and standard allocations (`handle_special_rust_functions`): `llvm.memcpy`, heap allocation (`__rust_alloc`, `alloc::alloc::alloc`, `raw_vec::RawVec`), `Deref::deref`, and `Arc::clone`.

## Running on an External Rust Crate

```bash
git clone https://github.com/lencx/ChatGPT.git
cd ChatGPT/src-tauri
rustup run nightly-2025-02-01 cargo rustc --bin chatgpt --release -- \
    -C codegen-units=1 --emit=llvm-ir=/tmp/chatgpt_lencx.ll

cd <rail>
RUSTFLAGS=-Awarnings cargo run -q --release -- /tmp/chatgpt_lencx.ll --pag=crux \
  --api=signatures/llm_api_functions.json \
  --ac=signatures/ac_functions.json
```

## Troubleshooting

**`openssl-sys` / `javascriptcore-rs-sys` build errors mentioning `pkg-config`**: install `pkg-config` and the corresponding system development libraries (used by example crates, not by `rail-rs` itself).

**`could not find native static library 'Polly'`**: install LLVM 19's Polly development package:

```bash
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh 19
sudo apt update
sudo apt install libpolly-19-dev
```

**`indexmap` requires Cargo feature `edition2024`**: pin an older `indexmap` on older Cargo versions:

```bash
cargo update -p indexmap --precise 2.7.1
```

## Attribution

Built on [`llvm-ir`](https://github.com/cdisselkoen/llvm-ir). Several foundational graph modules were adapted from [`llvm-ir-analysis`](https://github.com/cdisselkoen/llvm-ir-analysis):

| File | From `llvm-ir-analysis` | Original to RAIL |
|---|---|---|
| `src/dominator_tree.rs` | Copied verbatim | - |
| `src/control_dep_graph.rs` | Copied verbatim | - |
| `src/functions_by_type.rs` | Copied (+1 derive attribute) | - |
| `src/control_flow_graph.rs` | `ControlFlowGraph` / `CFGNode` construction | `print_cfg()` |
| `src/call_graph.rs` | `CallGraph::new()` and basic `callers`/`callees` accessors | `pub` graph field, `empty()`, `has_call_edge`/`add_call_edge`, `is_reachable`, `find_closest_common_root`, `print_call_graph()` |
| `src/lib.rs` | `ModuleAnalysis` / `CrossModuleAnalysis` / `FunctionAnalysis` / `SimpleCache` skeleton | Wiring for `pointer_assignment_graph`, `psa`, `ace`, `guard_inference`, `debuginfo`, `signature`, `context`, `util` |

### Original to RAIL

- `src/pointer_assignment_graph.rs` - PAG construction and pointer-analysis solvers (`insensitive`, `kcfa`, `kobj`, `kmix`, `crux`)
- `src/context.rs` - `PAContext` / `PAContextElem` principal and call-site context domains
- `src/psa.rs` - Principal-Sensitive Analysis (PSA) propagation engine
- `src/ace.rs` - Access-Control Enforcement (ACE) dominance, resource-binding, and type-disjointness pass
- `src/guard_inference.rs` - Structural inference of boolean access-control functions
- `src/debuginfo.rs` - DWARF composite/member type and source-location recovery
- `src/signature.rs` - Declarative API signature catalog loader and symbol matcher
- `src/util.rs` and `src/main.rs` - CLI driver and helpers
- `signatures/`, `examples/`, and `tests/`

## License

MIT - see [LICENSE](LICENSE).

Portions copied or adapted from `llvm-ir-analysis` (Copyright (c) 2020 Craig Disselkoen, MIT License) retain their upstream copyright notice alongside this repository's license.
