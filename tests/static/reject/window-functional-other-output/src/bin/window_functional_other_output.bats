#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Both windows must be of one output *)
prfn _other {output,other,first,second:$A.cells} (a: $Z.WINDOW(output, first), b: $Z.WINDOW(other, second)): $A.CELLS_EQ(first, second) =
  $Z.window_functional(a, b)

implement main0 () = ()
