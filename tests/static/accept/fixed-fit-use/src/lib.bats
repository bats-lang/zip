#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The fixed codes, made from their runs, fit to 15 bits: the two lemmas called with their true claims *)
prfn _litlen_fit {lengths:$A.cells} (fixed: $Z.FIXED_LITLEN(lengths)): $Z.LENGTHS_FIT(lengths, 15) = $Z.fixed_litlen_fit(fixed)

prfn _dist_fit {lengths:$A.cells} (fixed: $Z.FIXED_DIST(lengths)): $Z.LENGTHS_FIT(lengths, 15) = $Z.fixed_dist_fit(fixed)
