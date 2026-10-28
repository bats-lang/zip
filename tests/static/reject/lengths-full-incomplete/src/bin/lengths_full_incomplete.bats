#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* One code of one bit leaves the other unused: 0 + 1 is not 2, so LENGTHS_FULL is refused *)
prfn _one_one (): $Z.BL_COUNT($A.ccons(1, $A.cnil()), 1, 1) =
  $Z.BL_COUNT_mk($A.CLEN_cons($A.CLEN_nil()), $Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_zero()))

prfn _incomplete (): $Z.LENGTHS_FULL($A.ccons(1, $A.cnil()), 1) = $Z.LENGTHS_FULL_mk($Z.NEXT_CODE_first(), _one_one(), $AR.POW2_succ($AR.POW2_zero()))

implement main0 () = ()
