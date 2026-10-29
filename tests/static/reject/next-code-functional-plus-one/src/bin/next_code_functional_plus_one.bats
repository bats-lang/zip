#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* next_code[len] has one value; the lemma does not give it one more *)
prfn _plus_one {lengths:$A.cells}{len,first_code,second_code:nat}
  (first: $Z.NEXT_CODE(lengths, len, first_code), second: $Z.NEXT_CODE(lengths, len, second_code)): [first_code + 1 == second_code] void =
  $Z.next_code_functional(first, second)

implement main0 () = ()
