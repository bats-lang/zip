#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The 7-bit run is third (256 to 279): in second place it is refused *)
prfn _misordered {lengths,after_144,after_112,after_24:$A.cells}
  (first: $Z.RUN(144, 8, after_144, lengths), second: $Z.RUN(24, 7, after_112, after_144), third: $Z.RUN(112, 9, after_24, after_112), fourth: $Z.RUN(8, 8, $A.cnil(), after_24))
  : $Z.FIXED_LITLEN(lengths) =
  $Z.FIXED_LITLEN_mk(first, second, third, fourth)

implement main0 () = ()
