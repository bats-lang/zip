#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The fixed distance codes have 5 bits: a run of 4 is refused *)
prfn _four {lengths:$A.cells} (run: $Z.RUN(32, 4, $A.cnil(), lengths)): $Z.FIXED_DIST(lengths) = $Z.FIXED_DIST_mk(run)

implement main0 () = ()
