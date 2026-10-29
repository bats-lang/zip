#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* next_code[len + 1] = 2 * (next_code[len] + bl_count[len]): leaving the count out is refused *)
prfn _no_count {lengths:$A.cells}{len,first_code,count:nat | len >= 1}
  (before: $Z.NEXT_CODE(lengths, len, first_code), counted: $Z.BL_COUNT(lengths, len, count)): $Z.NEXT_CODE(lengths, len + 1, 2 * first_code) =
  $Z.NEXT_CODE_next(before, counted)

implement main0 () = ()
