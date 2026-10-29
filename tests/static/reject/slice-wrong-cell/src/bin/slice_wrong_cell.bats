#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Cells 1 and 2 of 5, 6, 7 are 6, 7 and not 6, 8 *)
prfn _wrong_cell (): $Z.SLICE($A.ccons(5, $A.ccons(6, $A.ccons(7, $A.cnil()))), 1, 2, $A.ccons(6, $A.ccons(8, $A.cnil()))) =
  $Z.SLICE_cons($A.NTH_there($A.NTH_here()), $Z.SLICE_cons($A.NTH_there($A.NTH_there($A.NTH_here())), $Z.SLICE_nil()))

implement main0 () = ()
