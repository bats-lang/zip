#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A run of two 7s is not a run of three *)
prfn _wrong_count (): $Z.RUN(3, 7, $A.cnil(), $A.ccons(7, $A.ccons(7, $A.cnil()))) = $Z.RUN_cons($Z.RUN_cons($Z.RUN_zero()))

implement main0 () = ()
