#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Only the end-of-block class ends the symbols: a literal class is refused *)
prfn _literal_ends {litlen,dist,source,output:$A.cells}{p,sym,used:nat}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used), class: $Z.SYMBOL_CLASS($Z.symbol_literal(), sym)): $Z.SYMS(litlen, dist, source, p, output, output, p + used) =
  $Z.SYMS_end(decoded, class)

implement main0 () = ()
