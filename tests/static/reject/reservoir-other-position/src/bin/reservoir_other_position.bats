#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The reservoir is of the bits from p: from p + 1 is refused *)
prfn _position {consumed:$A.cells}{p,count,value:nat} (bits: $Z.BITS(consumed, p, count, value)): $Z.RESERVOIR(consumed, p + 1, count, value) =
  $Z.RESERVOIR_mk(bits)

implement main0 () = ()
