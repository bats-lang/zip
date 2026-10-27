#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The counts are of all the symbols the lengths have: counts for 3 of 2 symbols are refused *)
prfn _other_symbols (clen: $A.CLEN($A.ccons(1, $A.ccons(1, $A.cnil())), 2), zeros: $Z.COUNT_BEFORE($A.ccons(1, $A.ccons(1, $A.cnil())), 3, 0, 2), ones: $Z.COUNT_BEFORE($A.ccons(1, $A.ccons(1, $A.cnil())), 3, 1, 1)): $Z.LENGTHS_SINGLE($A.ccons(1, $A.ccons(1, $A.cnil()))) =
  $Z.LENGTHS_SINGLE_mk(clen, zeros, ones)

implement main0 () = ()
