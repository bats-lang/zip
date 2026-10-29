#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* bl_count[len] has one value; the lemma does not give it one more *)
prfn _plus_one {lengths:$A.cells}{len,first_count,second_count:nat}
  (first: $Z.BL_COUNT(lengths, len, first_count), second: $Z.BL_COUNT(lengths, len, second_count)): [first_count + 1 == second_count] void =
  $Z.bl_count_functional(first, second)

implement main0 () = ()
