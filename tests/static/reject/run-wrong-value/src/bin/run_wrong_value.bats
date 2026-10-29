#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A run of 7s is not the cells 7, 8 *)
prfn _wrong_value (): $Z.RUN(2, 7, $A.cnil(), $A.ccons(7, $A.ccons(8, $A.cnil()))) = $Z.RUN_cons($Z.RUN_cons($Z.RUN_zero()))

implement main0 () = ()
