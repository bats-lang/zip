#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Each length starts three bits after the one before: the second read from bit 2 is refused *)
prfn _position (first: $Z.BITS($A.ccons(45, $A.ccons(0, $A.cnil())), 0, 3, 5), second: $Z.BITS($A.ccons(45, $A.ccons(0, $A.cnil())), 2, 3, 5)): $Z.READ_LENGTHS3($A.ccons(45, $A.ccons(0, $A.cnil())), 0, 2, $A.ccons(5, $A.ccons(5, $A.cnil()))) =
  $Z.READ_LENGTHS3_cons(first, $Z.READ_LENGTHS3_cons(second, $Z.READ_LENGTHS3_nil()))

implement main0 () = ()
