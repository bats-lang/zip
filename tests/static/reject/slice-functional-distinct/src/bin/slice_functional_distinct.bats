#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A slice is one set of cells; the lemma does not make two differ *)
prfn _distinct {source:$A.cells}{start,width:nat}{first,second:$A.cells}
  (a: $Z.SLICE(source, start, width, first), b: $Z.SLICE(source, start, width, second)): $A.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.slice_functional(a, b)

implement main0 () = ()
