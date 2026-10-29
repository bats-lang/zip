#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Two symbols of one bit are not a single code: COUNT_BEFORE of ones 1 for 2 symbols is refused *)
prfn _two (clen: $A.CLEN($A.ccons(1, $A.ccons(1, $A.cnil())), 2), zeros: $Z.COUNT_BEFORE($A.ccons(1, $A.ccons(1, $A.cnil())), 2, 0, 1), ones: $Z.COUNT_BEFORE($A.ccons(1, $A.ccons(1, $A.cnil())), 2, 1, 2)): $Z.LENGTHS_SINGLE($A.ccons(1, $A.ccons(1, $A.cnil()))) =
  $Z.LENGTHS_SINGLE_mk(clen, zeros, ones)

implement main0 () = ()
