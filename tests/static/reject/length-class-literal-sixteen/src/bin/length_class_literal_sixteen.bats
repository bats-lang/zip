#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Symbol 16 repeats the previous length: it is not a literal length *)
prfn _sixteen_literal (): $Z.LENGTH_CLASS($Z.length_literal(), 16) = $Z.LENGTH_CLASS_literal()

implement main0 () = ()
