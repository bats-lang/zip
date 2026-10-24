#include "share/atspre_staload.hats"
#use array as A
#use zip as Z

(* The stored constructor is the stored method's only *)
prfn _claimed {cs:$A.cells} (): $Z.INFLATES($Z.inflate_deflated(), cs, cs) = $Z.INFLATES_stored()
