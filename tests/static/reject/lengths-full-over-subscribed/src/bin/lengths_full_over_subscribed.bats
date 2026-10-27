#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Three codes of one bit are 0 + 3 > 2: LENGTHS_FULL needs the sum to be the power *)
prfn _over {lengths:$A.cells} (counted: $Z.BL_COUNT(lengths, 1, 3)): $Z.LENGTHS_FULL(lengths, 1) =
  $Z.LENGTHS_FULL_mk($Z.NEXT_CODE_first(), counted, $AR.POW2_succ($AR.POW2_zero()))

implement main0 () = ()
