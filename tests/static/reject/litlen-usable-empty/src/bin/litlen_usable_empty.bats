#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The literal/length code cannot be empty (3.2.7 allows that only for distances): LITLEN_USABLE has no such constructor *)
prfn _empty {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 15), empty: $Z.LENGTHS_EMPTY(lengths)): $Z.LITLEN_USABLE(lengths) =
  $Z.LITLEN_USABLE_single(fit, empty)

implement main0 () = ()
