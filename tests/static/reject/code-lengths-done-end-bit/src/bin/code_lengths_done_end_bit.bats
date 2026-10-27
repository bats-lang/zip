#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Done ends where it stands: one bit later is refused *)
prfn _fact {code_length_code,source,so_far,next,lengths,run:$A.cells}{p,total:nat}
  (so_far_len: $A.CLEN(so_far, total))
  : $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, so_far, p + 1) =
  $Z.CODE_LENGTHS_done(so_far_len)

implement main0 () = ()
