#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The literal/length lemma takes the literal/length lengths, not the distance lengths *)
prfn _of_dist {lengths:$A.cells} (fixed: $Z.FIXED_DIST(lengths)): $Z.LENGTHS_FIT(lengths, 15) =
  $Z.fixed_litlen_fit(fixed)

implement main0 () = ()
