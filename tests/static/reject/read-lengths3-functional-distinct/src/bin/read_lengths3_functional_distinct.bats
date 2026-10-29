#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The values read are one set of cells; the lemma does not make two differ *)
prfn _distinct {source:$A.cells}{p,count:nat}{first,second:$A.cells}
  (a: $Z.READ_LENGTHS3(source, p, count, first), b: $Z.READ_LENGTHS3(source, p, count, second)): $A.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.read_lengths3_functional(a, b)

implement main0 () = ()
