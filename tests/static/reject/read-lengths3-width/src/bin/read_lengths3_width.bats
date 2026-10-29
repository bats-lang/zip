#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Each length is three bits: a four-bit read is refused *)
prfn _four_bits {source:$A.cells}{p,value:nat} (bits: $Z.BITS(source, p, 4, value)): $Z.READ_LENGTHS3(source, p, 1, $A.ccons(value, $A.cnil())) =
  $Z.READ_LENGTHS3_cons(bits, $Z.READ_LENGTHS3_nil())

implement main0 () = ()
