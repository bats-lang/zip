#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The window starts at cell start of the buffer: the slice from cell 0 is refused *)
prfn _start (): $Z.WINDOW_IN_BUFFER($A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))), 1, $A.ccons(9, $A.ccons(1, $A.ccons(2, $A.cnil())))) =
  $Z.WINDOW_IN_BUFFER_mk{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))), $A.ccons(9, $A.ccons(1, $A.ccons(2, $A.cnil())))}{1, 3}($Z.SLICE_cons{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{0, 2}{9}{$A.ccons(1, $A.ccons(2, $A.cnil()))}($A.NTH_here(), $Z.SLICE_cons{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{1, 1}{1}{$A.ccons(2, $A.cnil())}($A.NTH_there($A.NTH_here()), $Z.SLICE_cons{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{2, 0}{2}{$A.cnil()}($A.NTH_there($A.NTH_there($A.NTH_here())), $Z.SLICE_nil{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{3}()))), $A.CLEN_cons($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))))

implement main0 () = ()
