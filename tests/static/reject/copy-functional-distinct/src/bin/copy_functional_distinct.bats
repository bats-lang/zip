#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A copy gives one set of cells; the lemma does not make two differ *)
prfn _distinct {output:$A.cells}{distance,length:nat}{first,second:$A.cells}
  (a: $Z.COPY(output, distance, length, first), b: $Z.COPY(output, distance, length, second)): $A.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.copy_functional(a, b)

implement main0 () = ()
