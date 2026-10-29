#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Symbol 285 is the length 258 with no extra bits: one extra bit is refused *)
prfn _extra (): $Z.LENGTH_SYMBOL(285, 1, 258) = $Z.LENGTH_SYMBOL_last()

implement main0 () = ()
