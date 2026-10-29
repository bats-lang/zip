#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* next_code[1] is 0 (3.2.2) *)
prfn _first_is_one {lengths:$A.cells} (): $Z.NEXT_CODE(lengths, 1, 1) = $Z.NEXT_CODE_first()

implement main0 () = ()
