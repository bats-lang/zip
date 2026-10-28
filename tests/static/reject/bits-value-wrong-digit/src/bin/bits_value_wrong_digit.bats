#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* One bit 1 is the number 1, not 2 *)
prfn _wrong_digit {source:$A.cells} (first: $Z.BIT(source, 0, 1)): $Z.BITS(source, 0, 1, 2) =
  $Z.BITS_cons(first, $Z.BITS_nil())

implement main0 () = ()
