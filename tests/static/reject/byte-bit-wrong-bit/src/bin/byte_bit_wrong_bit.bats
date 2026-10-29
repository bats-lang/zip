#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Bit 0 of the byte 5 is 1, not 0 *)
prfn _wrong_bit (): $Z.BYTE_BIT(5, 0, 0) = $Z.BYTE_BIT_here{2}{1}()

implement main0 () = ()
