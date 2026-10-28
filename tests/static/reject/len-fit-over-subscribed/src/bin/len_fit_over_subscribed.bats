#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Three codes of one bit do not fit (3 > 2): LEN_FIT_step refuses them *)
prfn _three_codes {lengths:$A.cells}
  (before: $Z.LEN_FIT(lengths, 0), counted: $Z.BL_COUNT(lengths, 1, 3), power: $AR.POW2(1, 2)): $Z.LEN_FIT(lengths, 1) =
  $Z.LEN_FIT_step(before, $Z.NEXT_CODE_first(), counted, power)

implement main0 () = ()
