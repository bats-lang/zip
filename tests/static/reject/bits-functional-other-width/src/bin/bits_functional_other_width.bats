#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The lemma needs both BITS of one width: widths 1 and 2 are not *)
prfn _other_width {source:$A.cells}{p,first_value,second_value:nat}
  (first: $Z.BITS(source, p, 1, first_value), second: $Z.BITS(source, p, 2, second_value)): [first_value == second_value] void =
  $Z.bits_functional(first, second)

implement main0 () = ()
