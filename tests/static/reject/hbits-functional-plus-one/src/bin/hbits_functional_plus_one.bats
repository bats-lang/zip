#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* HBITS has one code; the lemma does not give it one more *)
prfn _plus_one {source:$A.cells}{p,width,first_code,second_code:nat}
  (first: $Z.HBITS(source, p, width, first_code), second: $Z.HBITS(source, p, width, second_code)): [first_code + 1 == second_code] void =
  $Z.hbits_functional(first, second)

implement main0 () = ()
