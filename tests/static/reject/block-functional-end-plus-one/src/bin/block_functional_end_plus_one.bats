#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A block ends at one bit; the lemma does not give it one more *)
prfn _plus_one {kind:$Z.block_kind}{source:$A.cells}{p:nat}{before,first,second:$A.cells}{first_end,second_end:nat}
  (a: $Z.BLOCK(kind, source, p, before, first, first_end), b: $Z.BLOCK(kind, source, p, before, second, second_end)): [first_end + 1 == second_end] void =
  let prval _ = $Z.block_functional(a, b) in () end

implement main0 () = ()
