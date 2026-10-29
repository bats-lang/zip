#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The next code starts after the bits used: from p is refused *)
prfn _fact {code_length_code,source,so_far,next,lengths,run:$A.cells}{p,total,so_far_count,sym,used,end_bit:nat | so_far_count < total}
  (so_far_len: $A.CLEN(so_far, so_far_count),
   decoded: $Z.DECSYM(code_length_code, source, p, sym, used),
   class: $Z.LENGTH_CLASS($Z.length_literal(), sym),
   appended: $A.APPEND(so_far, $A.ccons(sym, $A.cnil()), next),
   rest: $Z.CODE_LENGTHS(code_length_code, source, p, next, total, lengths, end_bit))
  : $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit) =
  $Z.CODE_LENGTHS_literal(so_far_len, decoded, class, appended, rest)

implement main0 () = ()
