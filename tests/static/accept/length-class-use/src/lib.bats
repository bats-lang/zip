#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The code length symbols 0 to 15 are lengths, 16 repeats, 17 and 18 are runs of zeros *)
prfn _fifteen (): $Z.LENGTH_CLASS($Z.length_literal(), 15) = $Z.LENGTH_CLASS_literal()
prfn _sixteen (): $Z.LENGTH_CLASS($Z.length_repeat_previous(), 16) = $Z.LENGTH_CLASS_repeat_previous()
prfn _seventeen (): $Z.LENGTH_CLASS($Z.length_zeros_short(), 17) = $Z.LENGTH_CLASS_zeros_short()
prfn _eighteen (): $Z.LENGTH_CLASS($Z.length_zeros_long(), 18) = $Z.LENGTH_CLASS_zeros_long()
