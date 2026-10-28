#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Distance symbols 30 and 31 never occur: 14 extra bits (symbol 30) is refused *)
prfn _symbol_thirty (power: $AR.POW2(14, 16384)): $Z.DISTANCE_SYMBOL(30, 14, 32769) = $Z.DISTANCE_SYMBOL_base_2_times(power)

implement main0 () = ()
