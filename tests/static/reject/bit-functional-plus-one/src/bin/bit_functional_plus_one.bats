#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A bit of the cells has one value; the lemma does not give it one more *)
prfn _plus_one {source:$A.cells}{p,first_bit,second_bit:nat}
  (first: $Z.BIT(source, p, first_bit), second: $Z.BIT(source, p, second_bit)): [first_bit + 1 == second_bit] void =
  $Z.bit_functional(first, second)

implement main0 () = ()
