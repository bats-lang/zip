#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Both must be of the one read values *)
prfn _other {order,values,other:$A.cells}{count,first_sym:nat | first_sym <= 19}{first,second:$A.cells}
  (order_proof: $Z.CL_ORDER(order), len: $A.CLEN(values, count), a: $Z.CODE_LENGTHS_FROM(order, count, values, first_sym, first), b: $Z.CODE_LENGTHS_FROM(order, count, other, first_sym, second))
  : $A.CELLS_EQ(first, second) =
  $Z.code_lengths_from_functional(order_proof, len, a, b)

implement main0 () = ()
