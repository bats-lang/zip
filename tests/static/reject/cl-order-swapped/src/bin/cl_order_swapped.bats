#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The code length code lengths are stored in the order 16, 17, 18, 0, 8 ...: 17 and 16 swapped is another order *)
prfn _swapped (): $Z.CL_ORDER($A.ccons(17, $A.ccons(16, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil())))))))))))))))))))) = $Z.CL_ORDER_mk()

implement main0 () = ()
