#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The next symbol starts after the bits the literal used: from p is refused *)
prfn _same_bit {litlen,dist,source,output,next,after:$A.cells}{p,sym,used,end_bit:nat}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used), class: $Z.SYMBOL_CLASS($Z.symbol_literal(), sym),
   appended: $A.APPEND(output, $A.ccons(sym, $A.cnil()), next), rest: $Z.SYMS(litlen, dist, source, p, next, after, end_bit))
  : $Z.SYMS(litlen, dist, source, p, output, after, end_bit) =
  $Z.SYMS_literal(decoded, class, appended, rest)

implement main0 () = ()
