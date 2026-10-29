#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The fit must be to 15 bits: a code checked to 7 (the code length code) is refused *)
prfn _seven {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 7), full: $Z.LENGTHS_FULL(lengths, 15)): $Z.LITLEN_USABLE(lengths) =
  $Z.LITLEN_USABLE_full(fit, full)

implement main0 () = ()
