#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Bits decode using one number of bits; the lemma does not give it one more *)
prfn _plus_one {lengths,source:$A.cells}{maxlen,p,first_sym,first_used,second_sym,second_used:nat}
  (fit: $Z.LENGTHS_FIT(lengths, maxlen), first: $Z.DECSYM(lengths, source, p, first_sym, first_used), second: $Z.DECSYM(lengths, source, p, second_sym, second_used))
  : [first_used + 1 == second_used] void =
  $Z.decsym_functional(fit, first, second)

implement main0 () = ()
