#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Symbol 284 starts at the length 227, not 228 (3.2.5) *)
prfn _wrong_base (power: $AR.POW2(5, 32)): $Z.LENGTH_SYMBOL(284, 5, 228) = $Z.LENGTH_SYMBOL_base_7_times(power)

implement main0 () = ()
