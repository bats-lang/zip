#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A symbol that is the head of the order is in its prefix: NOT_IN_PREFIX_cons refuses it *)
prfn _head {order:$A.cells}{count:nat} (rest: $Z.NOT_IN_PREFIX(order, count, 16)): $Z.NOT_IN_PREFIX($A.ccons(16, order), count + 1, 16) =
  $Z.NOT_IN_PREFIX_cons(rest)

implement main0 () = ()
