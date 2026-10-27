#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Both decodings must be of one total *)
prfn _other_total {code_length_code,source:$A.cells}{p,total:nat}{so_far,first,second:$A.cells}{first_end,second_end:nat}
  (fit: $Z.LENGTHS_FIT(code_length_code, 7), a: $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, first, first_end), b: $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total + 1, second, second_end))
  : $A.CELLS_EQ(first, second) =
  $Z.code_lengths_functional(fit, a, b)

implement main0 () = ()
