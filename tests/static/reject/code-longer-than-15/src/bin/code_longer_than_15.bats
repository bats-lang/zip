#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A code has 1 to 15 bits: CODE_mk refuses 16 *)
prfn _sixteen {lengths:$A.cells}{sym,first_code,rank:nat}
  (found: $A.NTH(lengths, sym, 16), next: $Z.NEXT_CODE(lengths, 16, first_code), before: $Z.COUNT_BEFORE(lengths, sym, 16, rank))
  : $Z.CODE(lengths, sym, first_code + rank, 16) =
  $Z.CODE_mk(found, next, before)

implement main0 () = ()
