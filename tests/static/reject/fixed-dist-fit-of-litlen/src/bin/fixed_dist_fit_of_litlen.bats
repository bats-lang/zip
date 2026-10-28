#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The distance lemma takes the distance lengths, not the literal/length lengths *)
prfn _of_litlen {lengths:$A.cells} (fixed: $Z.FIXED_LITLEN(lengths)): $Z.LENGTHS_FIT(lengths, 15) =
  $Z.fixed_dist_fit(fixed)

implement main0 () = ()
