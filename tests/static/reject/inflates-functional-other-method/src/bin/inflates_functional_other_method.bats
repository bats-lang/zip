#include "share/atspre_staload.hats"
#use array as A
staload Z = "zip/src/lib.sats"

(* The lemma is for the same method *)
prfn _method {cs,first,second:$A.cells}
  (a: $Z.INFLATES($Z.inflate_stored(), cs, first), b: $Z.INFLATES($Z.inflate_deflated(), cs, second)): $Z.CELLS_EQ(first, second) =
  $Z.inflates_functional(a, b)

implement main0 () = ()
