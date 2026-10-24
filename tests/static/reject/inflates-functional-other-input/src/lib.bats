#include "share/atspre_staload.hats"
#use array as A
#use zip as Z

(* The lemma is for the same compressed cells *)
prfn _other (a: $Z.INFLATES($Z.inflate_stored(), $A.cnil(), $A.cnil()), b: $Z.INFLATES($Z.inflate_stored(), $A.ccons(1, $A.cnil()), $A.ccons(1, $A.cnil()))): $Z.CELLS_EQ($A.cnil(), $A.ccons(1, $A.cnil())) =
  $Z.inflates_functional(a, b)
