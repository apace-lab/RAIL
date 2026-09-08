; two_fields.ll : field sensitivity, two struct fields stay separate.
;   struct Pair { f0: ptr, f1: ptr }
;   s.f0 = &a ;  s.f1 = &b
;   ra = s.f0 ;  rb = s.f1
; EXPECTED (rail_rs is field-sensitive):
;   pts(%ra) = { O_a } ;  pts(%rb) = { O_b }
; A field-insensitive analysis would instead give pts(%ra)=pts(%rb)={O_a,O_b}.

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%Pair = type { ptr, ptr }

define i32 @"_ZN4test4main17h0000000000000000E"() {
start:
  %a = alloca i32, align 4          ; %a -> O_a
  %b = alloca i32, align 4          ; %b -> O_b
  %s = alloca %Pair, align 8        ; %s -> O_s

  %f0 = getelementptr inbounds %Pair, ptr %s, i32 0, i32 0
  store ptr %a, ptr %f0             ; s.f0 = &a  => O_s.f0 -> O_a
  %f1 = getelementptr inbounds %Pair, ptr %s, i32 0, i32 1
  store ptr %b, ptr %f1             ; s.f1 = &b  => O_s.f1 -> O_b

  %g0 = getelementptr inbounds %Pair, ptr %s, i32 0, i32 0
  %ra = load ptr, ptr %g0           ; ra = s.f0  => %ra -> O_a
  %g1 = getelementptr inbounds %Pair, ptr %s, i32 0, i32 1
  %rb = load ptr, ptr %g1           ; rb = s.f1  => %rb -> O_b
  ret i32 0
}
