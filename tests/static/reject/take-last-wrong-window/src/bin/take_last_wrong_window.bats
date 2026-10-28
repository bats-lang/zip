#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The last 2 cells of [1, 2, 3] are [2, 3], not [1, 2] *)
prfn _wrong (): $Z.TAKE_LAST($A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))), 2, $A.ccons(1, $A.ccons(2, $A.cnil()))) =
  $Z.TAKE_LAST_drop{$A.ccons(2, $A.ccons(3, $A.cnil())), $A.ccons(1, $A.ccons(2, $A.cnil()))}{1}{2, 2}($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil())), $Z.TAKE_LAST_short{$A.ccons(2, $A.ccons(3, $A.cnil()))}{2, 2}($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))))

implement main0 () = ()
