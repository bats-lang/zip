#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A stream gives one output; the lemma does not make two differ *)
prfn _distinct {source:$A.cells}{p:nat}{before,first,second:$A.cells}
  (a: $Z.BLOCKS(source, p, before, first), b: $Z.BLOCKS(source, p, before, second)): $A.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.blocks_functional(a, b)

implement main0 () = ()
