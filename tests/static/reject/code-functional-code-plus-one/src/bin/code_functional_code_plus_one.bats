#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A symbol has one code; the lemma does not give it one more *)
prfn _plus_one {lengths:$A.cells}{sym,first_code,first_len,second_code,second_len:nat}
  (first: $Z.CODE(lengths, sym, first_code, first_len), second: $Z.CODE(lengths, sym, second_code, second_len)): [first_code + 1 == second_code] void =
  $Z.code_functional(first, second)

implement main0 () = ()
