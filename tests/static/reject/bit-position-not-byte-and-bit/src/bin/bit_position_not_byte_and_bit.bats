#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Bit 9 is bit 1 of byte 1, not bit 0 of byte 0 *)
prfn _wrong_position {source:$A.cells} (found: $A.NTH(source, 0, 5), byte_bit: $Z.BYTE_BIT(5, 0, 1)): $Z.BIT(source, 9, 1) =
  $Z.BIT_mk(found, byte_bit)

implement main0 () = ()
