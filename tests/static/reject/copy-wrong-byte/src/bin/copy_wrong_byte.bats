#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Copying 2 bytes from distance 2 over 1, 2 gives 1, 2, 1, 2: the second copied byte is 2, not 3 *)
prfn _wrong_byte (): $Z.COPY($A.ccons(1, $A.ccons(2, $A.cnil())), 2, 2, $A.ccons(1, $A.ccons(2, $A.ccons(1, $A.ccons(3, $A.cnil()))))) =
  $Z.COPY_step{$A.ccons(1, $A.ccons(2, $A.cnil())), $A.ccons(1, $A.ccons(2, $A.ccons(1, $A.cnil()))), $A.ccons(1, $A.ccons(2, $A.ccons(1, $A.ccons(2, $A.cnil()))))}{2, 2, 1, 1}($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil())), $A.NTH_here(), $A.APPEND_cons{1}{$A.ccons(2, $A.cnil()), $A.ccons(1, $A.cnil()), $A.ccons(2, $A.ccons(1, $A.cnil()))}($A.APPEND_cons{2}{$A.cnil(), $A.ccons(1, $A.cnil()), $A.ccons(1, $A.cnil())}($A.APPEND_nil{$A.ccons(1, $A.cnil())}())), $Z.COPY_step{$A.ccons(1, $A.ccons(2, $A.ccons(1, $A.cnil()))), $A.ccons(1, $A.ccons(2, $A.ccons(1, $A.ccons(2, $A.cnil())))), $A.ccons(1, $A.ccons(2, $A.ccons(1, $A.ccons(2, $A.cnil()))))}{3, 2, 0, 2}($A.CLEN_cons($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))), $A.NTH_there($A.NTH_here()), $A.APPEND_cons{1}{$A.ccons(2, $A.ccons(1, $A.cnil())), $A.ccons(2, $A.cnil()), $A.ccons(2, $A.ccons(1, $A.ccons(2, $A.cnil())))}($A.APPEND_cons{2}{$A.ccons(1, $A.cnil()), $A.ccons(2, $A.cnil()), $A.ccons(1, $A.ccons(2, $A.cnil()))}($A.APPEND_cons{1}{$A.cnil(), $A.ccons(2, $A.cnil()), $A.ccons(2, $A.cnil())}($A.APPEND_nil{$A.ccons(2, $A.cnil())}()))), $Z.COPY_done{$A.ccons(1, $A.ccons(2, $A.ccons(1, $A.ccons(2, $A.cnil()))))}{2}()))

implement main0 () = ()
