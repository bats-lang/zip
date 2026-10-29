#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Both BLOCKS must start at one bit: p and p + 8 are not one *)
prfn _other_position {source:$A.cells}{p:nat}{before,first,second:$A.cells}
  (a: $Z.BLOCKS(source, p, before, first), b: $Z.BLOCKS(source, p + 8, before, second)): $A.CELLS_EQ(first, second) =
  $Z.blocks_functional(a, b)

implement main0 () = ()
