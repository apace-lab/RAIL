# static taint analysis (library usage)

The static taint analysis is **not** the classical single tainted/untainted bit model that [`llvm-ir-taint`](https://github.com/cdisselkoen/llvm-ir-taint) implements. It is the AFG static stage exposed as a Rust library. 

Given one or more LLVM IR modules and the LLM/AC signature catalogs, it builds
the pointer assignment graph in `afg` mode and returns a `TaintAnalysis`: the
semantic points it found (auth checks, LLM calls, prompts), the principal
contexts it propagated, and, for every graph node, the principals that reach it
and its source location.

The canonical consumer is `afg_prototype` (`src/main.rs`, `run_pag_and_afg`),
which turns this output into an instrumentation plan. Read that alongside this
doc for a full, working example.

## Relationship to `llvm-ir-taint`

In short: `llvm-ir-taint` answers "is this value tainted?" with an
instruction-level dataflow analysis; RAIL's `taint_analysis` answers "which
authenticated user's data can reach this point?" as a downstream consumer of
the PAG, with an entirely different data model. No types, functions, or files
were copied from `llvm-ir-taint`.


| | `llvm-ir-taint` | RAIL's `taint_analysis` |
|---|---|---|
| what's tracked | a `TaintedType` lattice (tainted/untainted, with pointee/struct shape) per SSA value | a set of `PAContextElem::Principal { auth_callsite }` per PAG node — *which auth call site's data reaches this node* |
| when it runs | its own forward abstract-interpretation pass, walking LLVM instructions directly (`Load`, `Store`, `GEP`, `BinaryOp`, `Select`, `BitCast`, ...) | after the pointer assignment graph (PAG) has already reached its points-to fixed point; it propagates over PAG nodes/edges, never touches LLVM instructions |
| fixed-point driver | a per-function `Worklist` re-processing functions as taint info changes | graph propagation from each `SemanticPoint` (access-control hit), plus `propagate_return_to_callers` to carry an authenticated principal back across call returns |
| what a "positive" means | a value is reachable from a tainted source | a node is reachable from **two or more** distinct principals — a static candidate for a cross-user leak |
| domain vocabulary | `TaintedType`, `TaintState`, `FunctionSummary`, `NamedStructs`, `Pointee`, `Config` | `PAContext`, `PAContextElem`, `SemanticPoint`, `SemanticPointKind` (`AccessControl`, `LlmCall`, `LlmPrompt`, ...), tied to the LLM-API/access-control signature catalogs |
| scope | generic taint propagation for any LLVM program, given a source/sink config | purpose-built for AFG: matching LLM-API and access-control call sites via the JSON catalogs, then asking "do two auth principals overlap on the same data" |



## Add it as a dependency

The taint analysis lives in this crate (`rail_rs`). Depend on it by path:

```toml
# Cargo.toml
[dependencies]
rail_rs = { path = "../rail_rs" }
```

Building against `rail_rs` needs LLVM 19 on the machine (same as the CLI):

```bash
export LLVM_SYS_191_PREFIX=/opt/homebrew/opt/llvm@19   # or your llvm@19 prefix
```

## Minimal usage

```rust
use std::path::Path;

fn main() -> anyhow::Result<()> {
    // 1) Parse the LLVM IR module(s). `llvm_ir` is re-exported by rail_rs.
    let module = rail_rs::llvm_ir::Module::from_ir_path(Path::new("app.ll"))
        .map_err(|e| anyhow::anyhow!("parse failed: {e}"))?;
    let modules = [module];
    let mut analysis = rail_rs::CrossModuleAnalysis::new(modules.iter());

    // 2) Load the catalogs and attach them, so the PAG records LLM/AC points.
    let llm = rail_rs::signature::load_signatures(Path::new("signatures/llm_api_functions.json"))
        .map_err(|e| anyhow::anyhow!("llm catalog: {e}"))?;
    let ac = rail_rs::signature::load_signatures(Path::new("signatures/ac_functions.json"))
        .map_err(|e| anyhow::anyhow!("ac catalog: {e}"))?;
    analysis.set_context_catalogs(llm, ac);

    // 3) Build the PAG in afg mode and run the taint analysis (k = None: default context).
    let taint = analysis.taint_analysis("afg", None);

    println!(
        "app_crate={:?}, {} semantic points, {} tagged nodes",
        taint.app_crate,
        taint.semantic_points.len(),
        taint.node_contexts.len(),
    );
    Ok(())
}
```

`taint_analysis` returns a `Ref<'_, TaintAnalysis>` (the result is cached on the
analysis), so hold it like a shared borrow and read its fields directly.

## What you get back

`TaintAnalysis` fields:

| field | type | meaning |
|-------|------|---------|
| `app_crate` | `String` | the application crate name (used to scope reachability) |
| `semantic_points` | `Vec<SemanticPoint>` | every matched auth / LLM / prompt call site |
| `nodes` | `HashMap<PANodeId, PANode>` | the PAG nodes, keyed by id |
| `node_contexts` | `HashMap<PANodeId, HashSet<PAContextElem>>` | for each node, the principals (and other context) that reach it |
| `active_principals` | `HashMap<FunctionKey, HashSet<PAContextElem>>` | the principals active per function |

`SemanticPoint` fields:

| field | type | meaning |
|-------|------|---------|
| `kind` | `SemanticPointKind` | `AccessControl` / `AccessControlRecovery` / `LlmPrompt` / `LlmCall` |
| `security_point.matched_fn_name` | `String` | the catalog `fn_name` this call site matched |
| `callee` | `Option<String>` | the demangled callee, when known |
| `argument_nodes` | `Vec<PANodeId>` | PAG nodes for the call's arguments |
| `result_node` | `Option<PANodeId>` | PAG node for the call's result (may be an sret pointer) |

`SemanticPointKind` variants carry a `category` string from the catalog
(`LlmCall` also carries an optional `provider`):

```rust
use rail_rs::taint_analysis::SemanticPointKind;

for point in taint.semantic_points.iter() {
    match &point.kind {
        SemanticPointKind::AccessControl { category }
        | SemanticPointKind::AccessControlRecovery { category } => {
            println!("auth [{category}]: {}", point.security_point.matched_fn_name);
        }
        SemanticPointKind::LlmCall { category, .. }
        | SemanticPointKind::LlmPrompt { category } => {
            println!("llm  [{category}]: {}", point.security_point.matched_fn_name);
        }
    }
}
```

## Principals and static overlaps

A **principal** is keyed by the **auth call site** it flows from, not by a runtime
user:

```rust
use rail_rs::PAContextElem;

// A node reached by two or more distinct auth call sites is a static
// cross-user overlap candidate.
for (node_id, ctxs) in taint.node_contexts.iter() {
    let principals: std::collections::HashSet<usize> = ctxs
        .iter()
        .filter_map(|e| match e {
            PAContextElem::Principal { auth_callsite } => Some(*auth_callsite),
            _ => None,
        })
        .collect();
    if principals.len() >= 2 {
        println!("node {node_id}: reached by {} principals", principals.len());
    }
}
```

Because a principal is a static location, two different users flowing through the
**same** auth call site look like one principal here. Distinguishing them needs
the dynamic stages in `afg_prototype` (instrument, MadSim observe, schedule),
which set a per-request principal at runtime.

## Source locations

Each node carries its function and (with debug info) a file and line, which is
how the prototype maps a node back to the source it should instrument:

```rust
if let Some(node) = taint.nodes.get(&node_id) {
    let function = node.function();                 // Option<&str>
    if let Some(loc) = node.source_loc.as_ref() {   // Option<PASourceLocation>
        println!("{:?} at {:?}:{:?}", function, loc.file, loc.line);
    }
}
```

`source_loc` is only populated when the module was compiled with debug info, so
build the input `.ll` with `-C debuginfo=2` (see below).

## Multiple modules

`CrossModuleAnalysis::new` takes any iterator of modules, so a lib + bin app is
just two parsed modules:

```rust
let modules = [
    rail_rs::llvm_ir::Module::from_ir_path(Path::new("app_lib.ll")).unwrap(),
    rail_rs::llvm_ir::Module::from_ir_path(Path::new("app_bin.ll")).unwrap(),
];
let mut analysis = rail_rs::CrossModuleAnalysis::new(modules.iter());
```

For a single crate, `ModuleAnalysis::new(&module)` exposes the same
`taint_analysis`, `set_context_catalogs`, and PAG accessors.

## Producing the `.ll` input

Compile the target with an LLVM 19 toolchain, and add debug info so nodes get
source locations:

```bash
cd <your app>
cargo +1.85.0 rustc --bin <app> -- --emit=llvm-ir -C debuginfo=2 -C codegen-units=1
LL=$(ls -t target/debug/deps/<app>-*.ll | head -1)
```

## Notes

- Catalog matching is by demangled symbol: suffix match first, then
  last-two-segment short name (see `src/signature.rs`). A stubbed module named to
  match a catalog entry (for example `async_openai::chat::Chat::create`) is
  matched the same way the real SDK would be.
- `app_crate` scopes which functions count as application code; the analysis seeds
  reachability from every app-crate function, not only from `main`.
- The catalogs shipped in `signatures/llm_api_functions.json` and
  `signatures/ac_functions.json` are the defaults; pass your own paths to
  `load_signatures` to extend them.
