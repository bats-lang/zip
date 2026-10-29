#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The lengths done are the lengths so far: other cells are refused *)
prfn _fact {code_length_code,source,so_far,next,lengths,run:$A.cells}{p,total:nat}
  (so_far_len: $A.CLEN(so_far, total))
  : $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, p) =
  $Z.CODE_LENGTHS_done(so_far_len)

implement main0 () = ()
