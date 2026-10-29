#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The code length code lengths are one set of cells; the lemma does not make two differ *)
prfn _distinct {order,values:$A.cells}{count,first_sym:nat | first_sym <= 19}{first,second:$A.cells}
  (order_proof: $Z.CL_ORDER(order), len: $A.CLEN(values, count), a: $Z.CODE_LENGTHS_FROM(order, count, values, first_sym, first), b: $Z.CODE_LENGTHS_FROM(order, count, values, first_sym, second))
  : $A.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.code_lengths_from_functional(order_proof, len, a, b)

implement main0 () = ()
