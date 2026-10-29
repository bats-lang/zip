#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The first 144 literal codes have 8 bits (3.2.6): a run of 9 is refused *)
prfn _nine {lengths,after_144,after_112,after_24:$A.cells}
  (first: $Z.RUN(144, 9, after_144, lengths), second: $Z.RUN(112, 9, after_112, after_144), third: $Z.RUN(24, 7, after_24, after_112), fourth: $Z.RUN(8, 8, $A.cnil(), after_24)): $Z.FIXED_LITLEN(lengths) =
  $Z.FIXED_LITLEN_mk(first, second, third, fourth)

implement main0 () = ()
