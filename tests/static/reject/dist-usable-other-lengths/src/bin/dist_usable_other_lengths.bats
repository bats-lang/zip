#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The fit and the empty code must be of the same lengths *)
prfn _other {first_lengths,second_lengths:$A.cells} (fit: $Z.LENGTHS_FIT(first_lengths, 15), empty: $Z.LENGTHS_EMPTY(second_lengths)): $Z.DIST_USABLE(first_lengths) =
  $Z.DIST_USABLE_empty(fit, empty)

implement main0 () = ()
