#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The runs end the lengths: a last run that leaves cells is refused *)
prfn _not_ended {lengths,after_144,after_112,after_24,rest:$A.cells}
  (first: $Z.RUN(144, 8, after_144, lengths), second: $Z.RUN(112, 9, after_112, after_144), third: $Z.RUN(24, 7, after_24, after_112), fourth: $Z.RUN(8, 8, rest, after_24))
  : $Z.FIXED_LITLEN(lengths) =
  $Z.FIXED_LITLEN_mk(first, second, third, fourth)

implement main0 () = ()
