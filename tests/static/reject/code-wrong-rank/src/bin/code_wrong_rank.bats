#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The code of a symbol is the first code of its length plus its rank: one more is refused *)
prfn _rank_plus_one {lengths:$A.cells}{sym,len,first_code,rank:nat | 1 <= len; len <= 15}
  (found: $A.NTH(lengths, sym, len), next: $Z.NEXT_CODE(lengths, len, first_code), before: $Z.COUNT_BEFORE(lengths, sym, len, rank))
  : $Z.CODE(lengths, sym, first_code + rank + 1, len) =
  $Z.CODE_mk(found, next, before)

implement main0 () = ()
