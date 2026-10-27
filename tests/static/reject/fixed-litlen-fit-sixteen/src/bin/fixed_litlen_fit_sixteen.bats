#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The fit of the 288 fixed lengths is to 15 bits; the lemma does not give it to 16 *)
prfn _sixteen {lengths:$A.cells} (fixed: $Z.FIXED_LITLEN(lengths)): $Z.LENGTHS_FIT(lengths, 16) =
  $Z.fixed_litlen_fit(fixed)

implement main0 () = ()
