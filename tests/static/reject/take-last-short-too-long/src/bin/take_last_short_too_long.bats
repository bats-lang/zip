#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A sequence of 3 cells is not short for keep 2: TAKE_LAST_short refuses it *)
prfn _long (): $Z.TAKE_LAST($A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))), 2, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))) = $Z.TAKE_LAST_short{$A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))}{3, 2}($A.CLEN_cons($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))))

implement main0 () = ()
