#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Symbol 29 starts at the distance 24577, not 24576 (3.2.5) *)
prfn _wrong_base (power: $AR.POW2(13, 8192)): $Z.DISTANCE_SYMBOL(29, 13, 24576) = $Z.DISTANCE_SYMBOL_base_3_times(power)

implement main0 () = ()
