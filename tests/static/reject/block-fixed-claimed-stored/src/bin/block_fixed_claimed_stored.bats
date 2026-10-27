#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A fixed block is not a stored one *)
prfn _fact {source,litlen,dist,before,after:$A.cells}{p,end_bit:nat}
  (fixed_litlen: $Z.FIXED_LITLEN(litlen), fixed_dist: $Z.FIXED_DIST(dist), litlen_fit: $Z.LENGTHS_FIT(litlen, 15), dist_fit: $Z.LENGTHS_FIT(dist, 15), syms: $Z.SYMS(litlen, dist, source, p, before, after, end_bit))
  : $Z.BLOCK($Z.block_stored(), source, p, before, after, end_bit) =
  $Z.BLOCK_fixed(fixed_litlen, fixed_dist, litlen_fit, dist_fit, syms)

implement main0 () = ()
