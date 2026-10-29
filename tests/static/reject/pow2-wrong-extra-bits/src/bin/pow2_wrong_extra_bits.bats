#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The power in a table row is 2 to its extra bits: 2 to the 2 is not 2 *)
prfn _wrong_power (power: $AR.POW2(2, 4)): $Z.LENGTH_SYMBOL(265, 1, 11) = $Z.LENGTH_SYMBOL_base_4_times(power)

implement main0 () = ()
