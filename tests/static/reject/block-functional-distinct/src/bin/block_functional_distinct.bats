#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A block gives one output; the lemma does not make two differ *)
prfn _distinct {kind:$Z.block_kind}{source:$A.cells}{p:nat}{before,first,second:$A.cells}{first_end,second_end:nat}
  (a: $Z.BLOCK(kind, source, p, before, first, first_end), b: $Z.BLOCK(kind, source, p, before, second, second_end)): $A.CELLS_EQ(first, $A.ccons(0, second)) =
  let prval _ = $Z.block_functional(a, b) in $Z.block_functional(a, b) end

implement main0 () = ()
