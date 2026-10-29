#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The reservoir holds the bits read: another value is refused *)
prfn _value {consumed:$A.cells}{p,count,value:nat} (bits: $Z.BITS(consumed, p, count, value)): $Z.RESERVOIR(consumed, p, count, value + 1) =
  $Z.RESERVOIR_mk(bits)

implement main0 () = ()
