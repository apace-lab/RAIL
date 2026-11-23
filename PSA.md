# Principal-Sensitive Analysis (Library Usage)

Principal-Sensitive Analysis (**PSA**, `rail_rs::psa`) and Access-Control Enforcement (**ACE**, `rail_rs::ace`) form the static analysis stages of **CRUX**, exposed as a Rust library on top of `rail_rs`.

Instead of tracking a binary sensitivity bit, PSA associates each authentication or authorization check site with a distinct **principal context** (`PAContextElem::Principal { auth_callsite }`) and selectively propagates principal contexts across post-check control-flow continuations, call-graph edges, and value-carrying pointer-assignment-graph (PAG) edges. Building on PSA and DWARF type recovery (`rail_rs::debuginfo`), ACE checks whether every call-graph path to a cataloged resource access or sensitive service operation is mediated by a resource-bound check with matching resource type.

The canonical consumer is [`crux`](https://github.com/apace-lab/crux.git) (`src/main.rs`, `run_pag_and_crux`), which turns PSA and ACE outputs into an `InstrumentationPlan` for R4 source instrumentation and runtime verification.

## Overview of the Model

| Dimension | Classical binary flow tracking | RAIL's `psa` + `ace` |
|---|---|---|
| **Tracked domain** | Single binary label per SSA value | Set of `PAContextElem::Principal { auth_callsite }` contexts per function, call site, and PAG node |
| **Graph substrate** | Instruction-level abstract interpretation | Built on top of the pointer assignment graph (PAG), call graph (CG), and per-function CFGs/dominator trees |
| **Propagation** | Generic source-to-sink forward pass | Selective propagation from each cataloged or inferred check (`SemanticPoint`) upward across helper returns (`propagate_return_to_callers`), downward across callees, and along value-carrying PAG edges |
| **Candidate criterion** | Value reachable from a marked source | Multi-principal PAG overlap (`>= 2` principal contexts) and ACE unmediated paths (`!covers(c, r)` over dominance, resource binding, and DWARF type matching) |
| **Policy vocabulary** | Per-application source/sink annotations | Reusable JSON API signature catalogs (`ac_functions.json`, `data_access_functions.json`, `llm_api_functions.json`) plus structural guard inference (`rail_rs::guard_inference`) |

## Add `rail-rs` as a Dependency

```toml
# Cargo.toml
[dependencies]
rail-rs = { path = "../rail-rs" }
```

Building against `rail-rs` requires LLVM 19 on the machine (matching the CLI):

```bash
export LLVM_SYS_191_PREFIX=/opt/homebrew/opt/llvm@19   # or your system llvm@19 prefix
```

## Minimal Usage

```rust
use std::path::Path;

fn main() -> anyhow::Result<()> {
    // 1) Parse the LLVM IR module(s). `llvm_ir` is re-exported by rail_rs.
    let module = rail_rs::llvm_ir::Module::from_ir_path(Path::new("app.ll"))
        .map_err(|e| anyhow::anyhow!("parse failed: {e}"))?;
    let modules = [module];
    let mut analysis = rail_rs::CrossModuleAnalysis::new(modules.iter());

    // 2) Load the API signature catalogs so the PAG records security-relevant call sites.
    let llm = rail_rs::signature::load_signatures(Path::new("signatures/llm_api_functions.json"))
        .map_err(|e| anyhow::anyhow!("llm catalog: {e}"))?;
    let ac = rail_rs::signature::load_signatures(Path::new("signatures/ac_functions.json"))
        .map_err(|e| anyhow::anyhow!("ac catalog: {e}"))?;
    let data = rail_rs::signature::load_signatures(Path::new("signatures/data_access_functions.json"))
        .map_err(|e| anyhow::anyhow!("data catalog: {e}"))?;
    analysis.set_context_catalogs(llm, ac, data);

    // 3) Build the PAG in crux mode and run Principal-Sensitive Analysis (PSA).
    let psa = analysis.psa("crux", None);

    println!(
        "app_crate={:?}, {} semantic points, {} tagged nodes",
        psa.app_crate,
        psa.semantic_points.len(),
        psa.node_contexts.len(),
    );
    Ok(())
}
```

`psa(...)` returns a `Ref<'_, PrincipalSensitiveAnalysis>` cached on the analysis struct, so you can borrow it and inspect its fields directly.

## Returned Data Structures

`PrincipalSensitiveAnalysis` fields:

| Field | Type | Meaning |
|---|---|---|
| `app_crate` | `String` | Detected or overridden application crate name used to scope workspace reachability |
| `semantic_points` | `Vec<SemanticPoint>` | Matched authentication/authorization checks, resource accesses, and LLM service calls |
| `nodes` | `HashMap<PANodeId, PANode>` | Pointer-assignment-graph nodes keyed by `PANodeId` |
| `node_contexts` | `HashMap<PANodeId, HashSet<PAContextElem>>` | Principal contexts reaching each PAG node |
| `active_principals` | `HashMap<FunctionKey, HashSet<PAContextElem>>` | Principal contexts active in each reachable function |

`SemanticPoint` fields:

| Field | Type | Meaning |
|---|---|---|
| `kind` | `SemanticPointKind` | `AccessControl` / `AccessControlRecovery` / `DataAccess` / `LlmPrompt` / `LlmCall` |
| `security_point.matched_fn_name` | `String` | Catalog `fn_name` matched at this call site |
| `callee` | `Option<String>` | Demangled callee symbol, when resolved |
| `argument_nodes` | `Vec<PANodeId>` | PAG nodes for the call's arguments |
| `result_node` | `Option<PANodeId>` | PAG node for the call's return value (including `sret` pointers) |

Inspecting matched `SemanticPoint`s:

```rust
use rail_rs::psa::SemanticPointKind;

for point in psa.semantic_points.iter() {
    match &point.kind {
        SemanticPointKind::AccessControl { category }
        | SemanticPointKind::AccessControlRecovery { category } => {
            println!("auth [{category}]: {}", point.security_point.matched_fn_name);
        }
        SemanticPointKind::DataAccess { category } => {
            println!("data [{category}]: {}", point.security_point.matched_fn_name);
        }
        SemanticPointKind::LlmCall { category, .. }
        | SemanticPointKind::LlmPrompt { category } => {
            println!("llm  [{category}]: {}", point.security_point.matched_fn_name);
        }
    }
}
```

## Principal Contexts and Multi-Principal Overlaps

Each static principal context is keyed by the authentication or authorization call site (`auth_callsite`) where it originates:

```rust
use rail_rs::PAContextElem;

// A PAG node reached by two or more distinct check sites has |PC(v)| > 1.
for (node_id, ctxs) in psa.node_contexts.iter() {
    let principals: std::collections::HashSet<usize> = ctxs
        .iter()
        .filter_map(|e| match e {
            PAContextElem::Principal { auth_callsite } => Some(*auth_callsite),
            _ => None,
        })
        .collect();
    if principals.len() >= 2 {
        println!("node {node_id}: reached by {} principal contexts", principals.len());
    }
}
```

Because static principal contexts represent program check sites rather than runtime user sessions, two runtime users executing through the same check site share one static context. Distinguishing concrete users and resource instances at runtime is handled by CRUX's dynamic R4 and trace-examination stages (`crux_instrument`, `crux_runtime`, `crux_observe`, and `crux_scheduler`).

## Source Locations and DWARF Metadata

When target bitcode is compiled with debug metadata, each `PANode` carries its enclosing function and Rust `file:line` coordinates:

```rust
if let Some(node) = psa.nodes.get(&node_id) {
    let function = node.function();                 // Option<&str>
    if let Some(loc) = node.source_loc.as_ref() {   // Option<PASourceLocation>
        println!("{:?} at {:?}:{:?}", function, loc.file, loc.line);
    }
}
```

`rail_rs::debuginfo::DebugTypes` additionally extracts composite struct layouts from DWARF records so `rail_rs::ace` can filter infrastructure handles (e.g., database pools) and check resource-type compatibility (`type_disjoint`) under LLVM's opaque pointers (`ptr`).

## Multiple Modules

`CrossModuleAnalysis::new` accepts any iterator of parsed LLVM IR modules (e.g., workspace crates or `lib` + `bin` targets):

```rust
let modules = [
    rail_rs::llvm_ir::Module::from_ir_path(Path::new("app_lib.ll")).unwrap(),
    rail_rs::llvm_ir::Module::from_ir_path(Path::new("app_bin.ll")).unwrap(),
];
let mut analysis = rail_rs::CrossModuleAnalysis::new(modules.iter());
```

For a single module, `ModuleAnalysis::new(&module)` exposes the same `psa`, `set_context_catalogs`, and PAG accessors.

## Producing `.ll` Bitcode Inputs

Compile the target crate with an LLVM 19 Rust toolchain and debug metadata enabled:

```bash
cd <your-app>
cargo +1.85.0 rustc --bin <app> -- --emit=llvm-ir -C debuginfo=2 -C codegen-units=1
LL=$(ls -t target/debug/deps/<app>-*.ll | head -1)
```

## Notes

- Catalog matching runs on demangled symbols: suffix match first, then last-two-segment short-name match (`Type::method`, see `src/signature.rs`).
- `app_crate` scopes workspace reachability (`in_app_workspace` seeds functions across sibling workspace crates sharing the application prefix, capturing `#[async_trait]` closure bodies).
- Default catalogs ship under `signatures/` (`ac_functions.json`, `data_access_functions.json`, `llm_api_functions.json`, `source_dao_functions.json`, and `serve_capture_functions.json`).
