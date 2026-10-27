#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The end-of-block symbol ends at p + used: one bit more is refused *)
prfn _end_bit {litlen,dist,source,output:$A.cells}{p,sym,used:nat}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used), class: $Z.SYMBOL_CLASS($Z.symbol_end_of_block(), sym)): $Z.SYMS(litlen, dist, source, p, output, output, p + used + 1) =
  $Z.SYMS_end(decoded, class)

implement main0 () = ()
