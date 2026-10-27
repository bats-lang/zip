#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The lemma needs both BITS from one bit position *)
prfn _other_position {source:$A.cells}{p,width,first_value,second_value:nat}
  (first: $Z.BITS(source, p, width, first_value), second: $Z.BITS(source, p + 1, width, second_value)): [first_value == second_value] void =
  $Z.bits_functional(first, second)

implement main0 () = ()
