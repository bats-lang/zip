#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* BITS has one value; the lemma does not give it one more *)
prfn _plus_one {source:$A.cells}{p,width,first_value,second_value:nat}
  (first: $Z.BITS(source, p, width, first_value), second: $Z.BITS(source, p, width, second_value)): [first_value + 1 == second_value] void =
  $Z.bits_functional(first, second)

implement main0 () = ()
