#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* On lengths 1, 2, 2 next_code[2] is 2, not 1 *)
(* lengths = $A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))): next_code[1] = 0, next_code[2] = 2 * (0 + 1) = 2 *)
prfn _one_length_one (): $Z.BL_COUNT($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 1, 1) =
  $Z.BL_COUNT_mk($A.CLEN_cons($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))),
    $Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_zero()))))

prfn _first_code_of_two (): $Z.NEXT_CODE($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 2) =
  $Z.NEXT_CODE_next($Z.NEXT_CODE_first(), _one_length_one())

prfn _rank_of_third (): $Z.COUNT_BEFORE($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 2, 1) =
  $Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_zero()))

prfn _third_is_at_two (): $A.NTH($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 2) = $A.NTH_there($A.NTH_there($A.NTH_here()))

prfn _wrong_first (): $Z.NEXT_CODE($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 1) = $Z.NEXT_CODE_next($Z.NEXT_CODE_first(), _one_length_one())

implement main0 () = ()
