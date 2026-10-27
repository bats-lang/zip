#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Nothing is dropped from a sequence of keep cells: TAKE_LAST_drop refuses a rest shorter than keep *)
prfn _short_rest (): $Z.TAKE_LAST($A.ccons(1, $A.ccons(2, $A.cnil())), 2, $A.ccons(2, $A.cnil())) =
  $Z.TAKE_LAST_drop{$A.ccons(2, $A.cnil()), $A.ccons(2, $A.cnil())}{1}{1, 2}($A.CLEN_cons($A.CLEN_nil()), $Z.TAKE_LAST_short{$A.ccons(2, $A.cnil())}{1, 2}($A.CLEN_cons($A.CLEN_nil())))

implement main0 () = ()
