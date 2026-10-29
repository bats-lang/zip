#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The end-of-block symbol ends at one bit; the lemma does not give it one more *)
prfn _plus_one {litlen,dist,source:$A.cells}{p:nat}{output,first,second:$A.cells}{first_end,second_end:nat}
  (litlen_fit: $Z.LENGTHS_FIT(litlen, 15), dist_fit: $Z.LENGTHS_FIT(dist, 15), a: $Z.SYMS(litlen, dist, source, p, output, first, first_end), b: $Z.SYMS(litlen, dist, source, p, output, second, second_end))
  : [first_end + 1 == second_end] void =
  let prval _ = $Z.syms_functional(litlen_fit, dist_fit, a, b) in () end

implement main0 () = ()
