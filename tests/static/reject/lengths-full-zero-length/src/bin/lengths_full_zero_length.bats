#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A complete code has a maximum length of at least 1 *)
prfn _zero {lengths:$A.cells}{first_code,count:nat} (next: $Z.NEXT_CODE(lengths, 0, first_code), counted: $Z.BL_COUNT(lengths, 0, count)): $Z.LENGTHS_FULL(lengths, 0) =
  $Z.LENGTHS_FULL_mk(next, counted, $AR.POW2_zero())

implement main0 () = ()
