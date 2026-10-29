#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The window is a slice of the decoder's buffer and has its count of cells *)
prfn _in_buffer (): $Z.WINDOW_IN_BUFFER($A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))), 1, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))) =
  $Z.WINDOW_IN_BUFFER_mk{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))), $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil())))}{1, 3}($Z.SLICE_cons{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{1, 2}{1}{$A.ccons(2, $A.ccons(3, $A.cnil()))}($A.NTH_there($A.NTH_here()), $Z.SLICE_cons{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{2, 1}{2}{$A.ccons(3, $A.cnil())}($A.NTH_there($A.NTH_there($A.NTH_here())), $Z.SLICE_cons{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{3, 0}{3}{$A.cnil()}($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))), $Z.SLICE_nil{$A.ccons(9, $A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))))}{4}()))), $A.CLEN_cons($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))))
