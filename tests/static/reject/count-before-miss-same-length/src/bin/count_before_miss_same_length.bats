#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A symbol of the length counted is a hit: COUNT_BEFORE_miss refuses it *)
prfn _same_is_not_a_miss {rest:$A.cells}{until,count:nat}{len:int}
  (counted: $Z.COUNT_BEFORE(rest, until, len, count)): $Z.COUNT_BEFORE($A.ccons(len, rest), until + 1, len, count) =
  $Z.COUNT_BEFORE_miss(counted)

implement main0 () = ()
