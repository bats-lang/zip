#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The fit of the 32 fixed distance lengths is to 15 bits; the lemma does not give it to 16 *)
prfn _sixteen {lengths:$A.cells} (fixed: $Z.FIXED_DIST(lengths)): $Z.LENGTHS_FIT(lengths, 16) =
  $Z.fixed_dist_fit(fixed)

implement main0 () = ()
