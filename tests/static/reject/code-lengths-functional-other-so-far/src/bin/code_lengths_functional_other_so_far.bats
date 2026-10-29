#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Both decodings must start from the same lengths so far *)
prfn _other_so_far {code_length_code,source:$A.cells}{p,total:nat}{so_far,other,first,second:$A.cells}{first_end,second_end:nat}
  (fit: $Z.LENGTHS_FIT(code_length_code, 7), a: $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, first, first_end), b: $Z.CODE_LENGTHS(code_length_code, source, p, other, total, second, second_end))
  : $A.CELLS_EQ(first, second) =
  $Z.code_lengths_functional(fit, a, b)

implement main0 () = ()
