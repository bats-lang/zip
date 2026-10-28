#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* There are 32 fixed distance codes: a run of 30 is refused *)
prfn _thirty {lengths:$A.cells} (run: $Z.RUN(30, 5, $A.cnil(), lengths)): $Z.FIXED_DIST(lengths) = $Z.FIXED_DIST_mk(run)

implement main0 () = ()
