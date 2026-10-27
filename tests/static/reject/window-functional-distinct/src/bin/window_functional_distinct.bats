#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A window is one set of cells; the lemma does not make two differ *)
prfn _distinct {output,first,second:$A.cells} (a: $Z.WINDOW(output, first), b: $Z.WINDOW(output, second)): $A.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.window_functional(a, b)

implement main0 () = ()
