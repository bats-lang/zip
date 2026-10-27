#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* BTYPE 01 is the fixed kind, not the stored one *)
prfn _fixed_is_stored (): $Z.BTYPE($Z.block_stored(), 1) = $Z.BTYPE_stored()

implement main0 () = ()
