#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The lemma needs the order to be CL_ORDER: another order is refused (it has repeated symbols the lemma cannot exclude) *)
prfn _other_order {order,other,values:$A.cells}{count,first_sym:nat | first_sym <= 19}{first,second:$A.cells}
  (order_proof: $Z.CL_ORDER(other), len: $A.CLEN(values, count), a: $Z.CODE_LENGTHS_FROM(order, count, values, first_sym, first), b: $Z.CODE_LENGTHS_FROM(order, count, values, first_sym, second))
  : $A.CELLS_EQ(first, second) =
  $Z.code_lengths_from_functional(order_proof, len, a, b)

implement main0 () = ()
