#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The block ends where its end-of-block symbol ends *)
prfn _fact {source,litlen,dist,before,after:$A.cells}{p,end_bit:nat}
  (fixed_litlen: $Z.FIXED_LITLEN(litlen), fixed_dist: $Z.FIXED_DIST(dist), litlen_fit: $Z.LENGTHS_FIT(litlen, 15), dist_fit: $Z.LENGTHS_FIT(dist, 15), syms: $Z.SYMS(litlen, dist, source, p, before, after, end_bit))
  : $Z.BLOCK($Z.block_fixed(), source, p, before, after, end_bit + 1) =
  $Z.BLOCK_fixed(fixed_litlen, fixed_dist, litlen_fit, dist_fit, syms)

implement main0 () = ()
