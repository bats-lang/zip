#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A symbol has one code length; the lemma does not give it one more *)
prfn _plus_one {lengths:$A.cells}{sym,first_code,first_len,second_code,second_len:nat}
  (first: $Z.CODE(lengths, sym, first_code, first_len), second: $Z.CODE(lengths, sym, second_code, second_len)): [first_len + 1 == second_len] void =
  $Z.code_functional(first, second)

implement main0 () = ()
