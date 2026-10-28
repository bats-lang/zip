#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* An element has at most 16 bits: BITS_cons refuses width 17 *)
prfn _seventeen {source:$A.cells}{p,value:nat} (first: $Z.BIT(source, p, 0), rest: $Z.BITS(source, p + 1, 16, value)): $Z.BITS(source, p, 17, 2 * value) =
  $Z.BITS_cons(first, rest)

implement main0 () = ()
