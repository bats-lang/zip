#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* BTYPE 11 is reserved (3.2.3) and names no kind *)
prfn _reserved (): $Z.BTYPE($Z.block_stored(), 3) = $Z.BTYPE_stored()

implement main0 () = ()
