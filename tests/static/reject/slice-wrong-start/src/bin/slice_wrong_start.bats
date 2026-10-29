#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A slice starting at cell 0 is not the one starting at cell 1 *)
prfn _wrong_start (): $Z.SLICE($A.ccons(5, $A.ccons(6, $A.ccons(7, $A.cnil()))), 0, 2, $A.ccons(6, $A.ccons(7, $A.cnil()))) =
  $Z.SLICE_cons($A.NTH_there($A.NTH_here()), $Z.SLICE_cons($A.NTH_there($A.NTH_there($A.NTH_here())), $Z.SLICE_nil()))

implement main0 () = ()
