#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Both BLOCKS must start from one output so far *)
prfn _other_before {source:$A.cells}{p:nat}{before,other,first,second:$A.cells}
  (a: $Z.BLOCKS(source, p, before, first), b: $Z.BLOCKS(source, p, other, second)): $A.CELLS_EQ(first, second) =
  $Z.blocks_functional(a, b)

implement main0 () = ()
