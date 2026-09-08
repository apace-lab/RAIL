; two_callers_store.ll : shared callee writes a pointer through its param.
; (Same shape as the framework's context_test.ll, but opaque-ptr + mangled so
;  rail_rs actually analyzes it, and observable via a pointer store.)
;
;   fn callee(param) { *param = &g }
;   caller_a: la; callee(&la)     ; context ca
;   caller_b: lb; callee(&lb)     ; context cb
;
; The separation is observable on the callee's %param node:
; EXPECTED (insensitive):  callee/%param merges  pts = { O_la, O_lb }
; EXPECTED (k-CFA, k=1):   %param has two context copies:
;                          %param@ca -> { O_la } ,  %param@cb -> { O_lb }
; In both modes: pts(O_la contents) and pts(O_lb contents) include { O_g }.

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@"_ZN4test1g17h0000000000000000E" = global i32 0    ; O_g

define void @"_ZN4test6callee17h0000000000000000E"(ptr %param) {
start:
  store ptr @"_ZN4test1g17h0000000000000000E", ptr %param   ; *param = &g
  ret void
}

define void @"_ZN4test8caller_a17h0000000000000000E"() {
start:
  %la = alloca ptr, align 8          ; %la -> O_la
  call void @"_ZN4test6callee17h0000000000000000E"(ptr %la)
  ret void
}

define void @"_ZN4test8caller_b17h0000000000000000E"() {
start:
  %lb = alloca ptr, align 8          ; %lb -> O_lb
  call void @"_ZN4test6callee17h0000000000000000E"(ptr %lb)
  ret void
}

define i32 @"_ZN4test4main17h0000000000000000E"() {
start:
  call void @"_ZN4test8caller_a17h0000000000000000E"()
  call void @"_ZN4test8caller_b17h0000000000000000E"()
  ret i32 0
}
