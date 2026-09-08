; addr_of.ll : AddressOf constraint (p = &a)
; The alloca %a is itself the address of a stack object O_a.
; EXPECTED (both modes): pts(%a) = { O_a }   (the alloca object)
;
; Names are Rust-legacy-mangled into crate "test" so rail_rs's main
; detection (needs "main17h") and app-crate gate (_ZN<len>test) fire.

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @"_ZN4test4main17h0000000000000000E"() {
start:
  %a = alloca i32, align 4          ; %a -> O_a
  ret i32 0
}
