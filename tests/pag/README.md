# PAG tests

Small hand-written .ll fixtures for rail_rs's pointer analysis. Two groups:
`basic/` (points-to semantics, same answer in every mode) and `context/` (the
kcfa vs insensitive behaviour). Each .ll also has its expected answer in the
header comment. This file is how to run them and what to expect.



### how to run
`cargo test -- --nocapture --test-threads=1`



## Why the fixtures look like Rust IR

rail_rs was built for Rust-compiled IR, so the fixtures imitate it:

- Opaque pointers (`ptr`), llvm-19. Not the old `i32*` form.
- Rust-legacy-mangled names. Two things the source needs:
  - `find_main_function_name` only picks a main whose symbol has "main17h". A
    plain `@main` is not found and nothing gets analyzed, so main is
    `_ZN4test4main17h0000000000000000E`.
  - Context is only applied to app-crate functions. `parse_app_crate` reads the
    crate from `_ZN<len><crate>` in main (here `4test`, so crate = `test`), so
    every callee is mangled into crate `test` (`_ZN4test...`) or it stays Global.
- `O_x` means the object for `alloca %x` (an alloca_object node). `nK` is the node
  id printed in points_to.txt.

## How to run

Mode is a CLI flag, no rebuild needed:

```bash
# kcfa, k=1
./target/debug/rail_rs tests/pag/context/identity_return.ll --pag=kcfa --k=1
# insensitive
./target/debug/rail_rs tests/pag/context/identity_return.ll --pag=insensitive
# afg mode (loads catalogs, records context points)
./target/debug/rail_rs <in.ll> --pag=afg --api=signatures/llm_api_functions.json --ac=signatures/ac_functions.json
cat points_to.txt
```

Modes: kcfa/kobj/kmix (need `--k=`), afg, anything else falls back to insensitive.

## basic (same answer in every mode)

```
addr_of.ll     pts(%a)={O_a}
copy.ll        pts(%q)={O_a}
store_load.ll  pts(%r)={O_a}
two_fields.ll  pts(ra)={O_a}, pts(rb)={O_b}
```

## context (kcfa vs insensitive)

identity_return.ll, `fn id(x)->x ; p=id(&a) ; q=id(&b)`

```
  insensitive:  pts(%p)=pts(%q)={O_a,O_b}     (merged)
  kcfa k=1:     pts(%p)={O_a}, pts(%q)={O_b}   (separated)
```

This is the main one. Insensitive merges the two calls, kcfa keeps them apart.

two_callers_store.ll, `fn callee(param){*param=&g} ; caller_a{callee(&la)} ; caller_b{callee(&lb)}`

```
  insensitive:  callee's %param = {O_la, O_lb}
  kcfa k=1:     %param splits per context, {O_la} vs {O_lb}
```

Either way, O_la and O_lb point at O_g.

depth_k1_limit.ll, `fn id(x)->x ; fn wrap(x)->id(x) ; p=wrap(&a) ; q=wrap(&b)`

One wrapper level sits between the calls. wrap is re-analyzed per calling context,
so kcfa k=1 still separates p and q ({O_a} vs {O_b}), while insensitive merges
them. Good for seeing how far the context reaches.
