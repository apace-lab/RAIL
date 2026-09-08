// Runs the pag correctness fixtures under tests/pag/ through the built binary and
// checks the points-to output. Assertions compare relationships between values
// (e.g. pts(p) == pts(a), pts(p) != pts(q)) rather than hardcoding node ids, so
// they survive node renumbering.

use std::process::Command;
use std::sync::Mutex;

// The binary writes points_to.txt into the cwd, so runs must not overlap.
static SERIAL: Mutex<()> = Mutex::new(());

// Run one fixture in a given mode and return the contents of points_to.txt.
fn run(fixture: &str, mode: &[&str]) -> String {
    let _guard = SERIAL.lock().unwrap();
    let bin = env!("CARGO_BIN_EXE_rail-rs");
    let ok = Command::new(bin)
        .arg(fixture)
        .args(mode)
        .status()
        .expect("failed to launch rail_rs")
        .success();
    assert!(ok, "rail_rs exited with failure on {fixture}");
    std::fs::read_to_string("points_to.txt").expect("no points_to.txt produced")
}

// Points-to set of the first node whose line contains `needle`, as a sorted list
// of node-id tokens like ["n0", "n2"].
fn set_after(dump: &str, needle: &str) -> Vec<String> {
    let mut lines = dump.lines();
    while let Some(line) = lines.next() {
        if line.contains(needle) {
            let set = lines.next().unwrap_or("").trim();
            let set = set
                .trim_start_matches("-> ")
                .trim_start_matches('{')
                .trim_end_matches('}');
            let mut ids: Vec<String> = set
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            ids.sort();
            return ids;
        }
    }
    panic!("no node matching {needle:?} in points_to dump");
}

// pts of an SSA value `name` (e.g. the pointer %p).
fn pts(dump: &str, name: &str) -> Vec<String> {
    set_after(dump, &format!("::{name} (ctx"))
}

// pts of the memory object for `alloca %name` (e.g. O_la). Matches `::%name::`.
fn pts_obj(dump: &str, name: &str) -> Vec<String> {
    set_after(dump, &format!("::%{name}::"))
}

// ---- basic (same answer in every mode) ----

#[test]
fn addr_of() {
    let d = run("tests/pag/basic/addr_of.ll", &["--pag=kcfa", "--k=1"]);
    assert_eq!(
        pts(&d, "a").len(),
        1,
        "a should point at exactly its alloca object"
    );
}

#[test]
fn copy() {
    let d = run("tests/pag/basic/copy.ll", &["--pag=kcfa", "--k=1"]);
    assert_eq!(pts(&d, "q"), pts(&d, "a"), "q = a, so pts must match");
    assert_eq!(pts(&d, "q").len(), 1);
}

#[test]
fn store_load() {
    let d = run("tests/pag/basic/store_load.ll", &["--pag=kcfa", "--k=1"]);
    // %r = *pp, and *pp was set to &a, so r must point where a points (O_a).
    assert_eq!(pts(&d, "r"), pts(&d, "a"), "r = *pp should resolve to O_a");
    assert_eq!(pts(&d, "r").len(), 1);
}

#[test]
fn two_fields() {
    let d = run("tests/pag/basic/two_fields.ll", &["--pag=kcfa", "--k=1"]);
    assert_eq!(pts(&d, "ra"), pts(&d, "a"), "ra = s.f0 should be O_a");
    assert_eq!(pts(&d, "rb"), pts(&d, "b"), "rb = s.f1 should be O_b");
    assert_ne!(pts(&d, "ra"), pts(&d, "rb"), "fields must not merge");
}

// ---- context (kcfa vs insensitive) ----

#[test]
fn identity_return_kcfa_separates() {
    let d = run(
        "tests/pag/context/identity_return.ll",
        &["--pag=kcfa", "--k=1"],
    );
    assert_eq!(pts(&d, "p"), pts(&d, "a"), "p = id(&a) should be O_a");
    assert_eq!(pts(&d, "q"), pts(&d, "b"), "q = id(&b) should be O_b");
    assert_ne!(
        pts(&d, "p"),
        pts(&d, "q"),
        "kcfa must keep the two calls apart"
    );
}

#[test]
fn identity_return_insensitive_merges() {
    let d = run(
        "tests/pag/context/identity_return.ll",
        &["--pag=insensitive"],
    );
    assert_eq!(
        pts(&d, "p"),
        pts(&d, "q"),
        "insensitive must merge the two calls"
    );
    assert_eq!(
        pts(&d, "p").len(),
        2,
        "merged set should hold both O_a and O_b"
    );
}

#[test]
fn two_callers_store_reaches_global() {
    let d = run(
        "tests/pag/context/two_callers_store.ll",
        &["--pag=kcfa", "--k=1"],
    );
    // *param = &g in the shared callee, so both callers' local objects hold O_g.
    assert!(
        !pts_obj(&d, "la").is_empty(),
        "O_la should hold O_g after the store"
    );
    assert_eq!(
        pts_obj(&d, "la"),
        pts_obj(&d, "lb"),
        "both callers' objects reach the same global g"
    );
}

#[test]
fn depth_k1_separates() {
    let d = run(
        "tests/pag/context/depth_k1_limit.ll",
        &["--pag=kcfa", "--k=1"],
    );
    assert_eq!(pts(&d, "p"), pts(&d, "a"));
    assert_eq!(pts(&d, "q"), pts(&d, "b"));
    assert_ne!(
        pts(&d, "p"),
        pts(&d, "q"),
        "per-context reanalysis should keep p and q apart"
    );
}
