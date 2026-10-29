#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The fit and the completeness must be of the same lengths *)
prfn _other {first_lengths,second_lengths:$A.cells} (fit: $Z.LENGTHS_FIT(first_lengths, 15), full: $Z.LENGTHS_FULL(second_lengths, 15)): $Z.LITLEN_USABLE(first_lengths) =
  $Z.LITLEN_USABLE_full(fit, full)

implement main0 () = ()
