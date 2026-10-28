#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The bits read from the earlier cells are the same value in the whole; the lemma does not give it one more *)
prfn _plus_one {earlier,later,whole:$A.cells}{p,width,value:nat}
  (appended: $A.APPEND(earlier, later, whole), bits: $Z.BITS(earlier, p, width, value)): $Z.BITS(whole, p, width, value + 1) =
  $Z.bits_in_prefix(appended, bits)

implement main0 () = ()
