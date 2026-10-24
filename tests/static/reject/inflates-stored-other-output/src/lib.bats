#include "share/atspre_staload.hats"
#use array as A
#use zip as Z

(* A stored entry does not inflate to other cells than its own *)
prfn _changed (): $Z.INFLATES($Z.inflate_stored(), $A.ccons(7, $A.cnil()), $A.ccons(8, $A.cnil())) = $Z.INFLATES_stored()
