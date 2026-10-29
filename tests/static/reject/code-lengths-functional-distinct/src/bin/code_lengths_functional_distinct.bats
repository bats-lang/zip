#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A decoding of code lengths gives one set of cells; the lemma does not make two differ *)
prfn _distinct {code_length_code,source:$A.cells}{p,total:nat}{so_far,first,second:$A.cells}{first_end,second_end:nat}
  (fit: $Z.LENGTHS_FIT(code_length_code, 7), a: $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, first, first_end), b: $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, second, second_end))
  : $A.CELLS_EQ(first, $A.ccons(0, second)) =
  $Z.code_lengths_functional(fit, a, b)

implement main0 () = ()
