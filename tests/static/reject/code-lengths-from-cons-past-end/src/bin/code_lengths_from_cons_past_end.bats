#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The lengths stop at symbol 18: a cons for symbol 19 is refused *)
prfn _past {order,values,rest:$A.cells}{count,len:nat} (length_of: $Z.CODE_LENGTH_OF(order, 19, count, values, len), tail: $Z.CODE_LENGTHS_FROM(order, count, values, 20, rest))
  : $Z.CODE_LENGTHS_FROM(order, count, values, 19, $A.ccons(len, rest)) =
  $Z.CODE_LENGTHS_FROM_cons(length_of, tail)

implement main0 () = ()
