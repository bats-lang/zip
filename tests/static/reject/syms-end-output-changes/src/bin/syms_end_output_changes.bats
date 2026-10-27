#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The end-of-block symbol appends nothing: an output that grew is refused *)
prfn _grows {litlen,dist,source,output,other:$A.cells}{p,sym,used:nat}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used), class: $Z.SYMBOL_CLASS($Z.symbol_end_of_block(), sym)): $Z.SYMS(litlen, dist, source, p, output, other, p + used) =
  $Z.SYMS_end(decoded, class)

implement main0 () = ()
