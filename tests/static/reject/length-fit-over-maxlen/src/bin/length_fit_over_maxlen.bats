#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A length above the maximum is refused by AT_MOST_cons *)
prfn _eight {rest:$A.cells} (others: $Z.AT_MOST(rest, 7)): $Z.AT_MOST($A.ccons(8, rest), 7) = $Z.AT_MOST_cons(others)

implement main0 () = ()
