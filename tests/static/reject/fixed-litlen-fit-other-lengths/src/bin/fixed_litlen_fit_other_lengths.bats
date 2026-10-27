#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The fit is of the lengths whose runs were given, not of other cells *)
prfn _other {lengths,other:$A.cells} (fixed: $Z.FIXED_LITLEN(lengths)): $Z.LENGTHS_FIT(other, 15) =
  $Z.fixed_litlen_fit(fixed)

implement main0 () = ()
