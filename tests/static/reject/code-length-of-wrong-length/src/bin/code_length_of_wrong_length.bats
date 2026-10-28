#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Symbol 16 is stored first, with the first value: the second value is refused *)
prfn _wrong_length (): $Z.CODE_LENGTH_OF($A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil()))))))))))))))))))), 16, 2, $A.ccons(5, $A.ccons(5, $A.cnil())), 6) =
  $Z.CODE_LENGTH_OF_stored{$A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil()))))))))))))))))))), $A.ccons(5, $A.ccons(5, $A.cnil()))}{16, 0, 2, 6}($A.NTH_here(), $A.NTH_here())

implement main0 () = ()
