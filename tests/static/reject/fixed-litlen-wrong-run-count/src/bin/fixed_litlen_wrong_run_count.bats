#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The first run is 144 codes: a run of 143 is refused *)
prfn _short {lengths,after_143,after_112,after_24:$A.cells}
  (first: $Z.RUN(143, 8, after_143, lengths), second: $Z.RUN(112, 9, after_112, after_143), third: $Z.RUN(24, 7, after_24, after_112), fourth: $Z.RUN(8, 8, $A.cnil(), after_24))
  : $Z.FIXED_LITLEN(lengths) =
  $Z.FIXED_LITLEN_mk(first, second, third, fourth)

implement main0 () = ()
