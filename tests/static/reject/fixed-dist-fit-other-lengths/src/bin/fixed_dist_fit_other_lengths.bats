#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The fit is of the lengths whose run was given, not of other cells *)
prfn _other {lengths,other:$A.cells} (fixed: $Z.FIXED_DIST(lengths)): $Z.LENGTHS_FIT(other, 15) =
  $Z.fixed_dist_fit(fixed)

implement main0 () = ()
