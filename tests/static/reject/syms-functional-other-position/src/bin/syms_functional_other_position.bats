#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Both SYMS must start at one bit *)
prfn _other_position {litlen,dist,source:$A.cells}{p:nat}{output,first,second:$A.cells}{first_end,second_end:nat}
  (litlen_fit: $Z.LENGTHS_FIT(litlen, 15), dist_fit: $Z.LENGTHS_FIT(dist, 15), a: $Z.SYMS(litlen, dist, source, p, output, first, first_end), b: $Z.SYMS(litlen, dist, source, p + 1, output, second, second_end))
  : $A.CELLS_EQ(first, second) =
  $Z.syms_functional(litlen_fit, dist_fit, a, b)

implement main0 () = ()
