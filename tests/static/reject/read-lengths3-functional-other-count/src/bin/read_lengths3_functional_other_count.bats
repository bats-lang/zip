#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Both must read the same number of lengths *)
prfn _other_count {source:$A.cells}{p,count:nat}{first,second:$A.cells}
  (a: $Z.READ_LENGTHS3(source, p, count, first), b: $Z.READ_LENGTHS3(source, p, count + 1, second)): $A.CELLS_EQ(first, second) =
  $Z.read_lengths3_functional(a, b)

implement main0 () = ()
