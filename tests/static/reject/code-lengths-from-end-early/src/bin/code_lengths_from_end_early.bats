#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The lengths run over symbols 0 to 18: ending at symbol 18 is refused *)
prfn _early (): $Z.CODE_LENGTHS_FROM($A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil()))))))))))))))))))), 2, $A.ccons(5, $A.ccons(5, $A.cnil())), 18, $A.cnil()) = $Z.CODE_LENGTHS_FROM_end{$A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil()))))))))))))))))))), $A.ccons(5, $A.ccons(5, $A.cnil()))}{2}()

implement main0 () = ()
