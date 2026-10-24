#include "share/atspre_staload.hats"
#use array as A
#use zip as Z

(* The lemma does not say the outputs differ *)
prfn _distinct {cs,first,second:$A.cells}
  (a: $Z.INFLATES($Z.inflate_stored(), cs, first), b: $Z.INFLATES($Z.inflate_stored(), cs, second)): $Z.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.inflates_functional(a, b)
