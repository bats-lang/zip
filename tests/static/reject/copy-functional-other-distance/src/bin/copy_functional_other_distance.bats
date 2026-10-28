#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Both copies must be of one distance *)
prfn _other {output:$A.cells}{distance,length:nat}{first,second:$A.cells}
  (a: $Z.COPY(output, distance, length, first), b: $Z.COPY(output, distance + 1, length, second)): $A.CELLS_EQ(first, second) =
  $Z.copy_functional(a, b)

implement main0 () = ()
