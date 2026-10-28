#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* An empty code has every symbol at length 0: a count of 1 zero among 2 symbols is refused *)
prfn _one_used (clen: $A.CLEN($A.ccons(1, $A.ccons(1, $A.cnil())), 2), zeros: $Z.COUNT_BEFORE($A.ccons(1, $A.ccons(1, $A.cnil())), 2, 0, 1)): $Z.LENGTHS_EMPTY($A.ccons(1, $A.ccons(1, $A.cnil()))) = $Z.LENGTHS_EMPTY_mk(clen, zeros)

implement main0 () = ()
