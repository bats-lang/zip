#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A hit counts one more: the same count is refused *)
prfn _hit_counts {rest:$A.cells}{until,count:nat}{len:int}
  (counted: $Z.COUNT_BEFORE(rest, until, len, count)): $Z.COUNT_BEFORE($A.ccons(len, rest), until + 1, len, count) =
  $Z.COUNT_BEFORE_hit(counted)

implement main0 () = ()
