#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The code lengths end at one bit; the lemma does not give it one more *)
prfn _plus_one {code_length_code,source:$A.cells}{p,total:nat}{so_far,first,second:$A.cells}{first_end,second_end:nat}
  (fit: $Z.LENGTHS_FIT(code_length_code, 7), a: $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, first, first_end), b: $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, second, second_end))
  : [first_end + 1 == second_end] void =
  let prval _ = $Z.code_lengths_functional(fit, a, b) in () end

implement main0 () = ()
