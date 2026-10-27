#include "share/atspre_staload.hats"
#use array as A
#use zip as Z

(* A stored entry inflates to its own cells, and two proofs of one entry give the same cells *)
prfn _stored {cs:$A.cells} (): $Z.INFLATES($Z.inflate_stored(), cs, cs) = $Z.INFLATES_stored()

prfn _same {cs,first,second:$A.cells}
  (a: $Z.INFLATES($Z.inflate_stored(), cs, first), b: $Z.INFLATES($Z.inflate_stored(), cs, second)): $Z.CELLS_EQ(first, second) =
  $Z.inflates_functional(a, b)

prfn _literal (): $Z.INFLATES($Z.inflate_stored(), $A.ccons(7, $A.cnil()), $A.ccons(7, $A.cnil())) = $Z.INFLATES_stored()

(* the old form: zip's own CELLS_EQ and its constructor are still there (keyword: cells-eq, removal zip#74) *)
prfn _old_cells_eq {cs:$A.cells} (): $Z.CELLS_EQ(cs, cs) = $Z.CELLS_EQ_refl()
