#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Data elements are packed least significant bit first (3.1.1): bits 1 then 0 are the number 1, not 2 *)
prfn _lsb_first {source:$A.cells} (first: $Z.BIT(source, 0, 1), second: $Z.BIT(source, 1, 0)): $Z.BITS(source, 0, 2, 2) =
  $Z.BITS_cons(first, $Z.BITS_cons(second, $Z.BITS_nil()))

implement main0 () = ()
