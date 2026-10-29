#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The last min(keep, count) cells: 2 of [1, 2, 3] are [2, 3], all of [1] when keep is 2, and the windows are unique *)
prfn _drop_one (): $Z.TAKE_LAST($A.ccons(1, $A.ccons(2, $A.ccons(3, $A.cnil()))), 2, $A.ccons(2, $A.ccons(3, $A.cnil()))) =
  $Z.TAKE_LAST_drop{$A.ccons(2, $A.ccons(3, $A.cnil())), $A.ccons(2, $A.ccons(3, $A.cnil()))}{1}{2, 2}($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil())), $Z.TAKE_LAST_short{$A.ccons(2, $A.ccons(3, $A.cnil()))}{2, 2}($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))))

prfn _short (): $Z.TAKE_LAST($A.ccons(1, $A.cnil()), 2, $A.ccons(1, $A.cnil())) = $Z.TAKE_LAST_short{$A.ccons(1, $A.cnil())}{1, 2}($A.CLEN_cons($A.CLEN_nil()))

prfn _unique {output,first,second:$A.cells}
  (a: $Z.WINDOW(output, first), b: $Z.WINDOW(output, second)): $A.CELLS_EQ(first, second) =
  $Z.window_functional(a, b)
