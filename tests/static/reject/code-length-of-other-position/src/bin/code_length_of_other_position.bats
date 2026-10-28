#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The length of a symbol is the value at its own position: the value at the next position is refused *)
prfn _other_position (): $Z.CODE_LENGTH_OF($A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil()))))))))))))))))))), 16, 2, $A.ccons(5, $A.ccons(5, $A.cnil())), 5) =
  $Z.CODE_LENGTH_OF_stored{$A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil()))))))))))))))))))), $A.ccons(5, $A.ccons(5, $A.cnil()))}{16, 0, 2, 5}($A.NTH_here(), $A.NTH_there($A.NTH_here()))

implement main0 () = ()
