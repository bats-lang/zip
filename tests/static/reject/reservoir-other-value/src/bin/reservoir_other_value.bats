#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The reservoir holds the bits read: another value is refused *)
prfn _value {consumed:$A.cells}{p,count,value:nat} (bits: $Z.BITS(consumed, p, count, value)): $Z.RESERVOIR(consumed, p, count, value + 1) =
  $Z.RESERVOIR_mk(bits)

implement main0 () = ()
