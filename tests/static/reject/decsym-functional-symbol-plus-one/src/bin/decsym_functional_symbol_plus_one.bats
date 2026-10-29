#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Bits decode to one symbol; the lemma does not give it one more *)
prfn _plus_one {lengths,source:$A.cells}{maxlen,p,first_sym,first_used,second_sym,second_used:nat}
  (fit: $Z.LENGTHS_FIT(lengths, maxlen), first: $Z.DECSYM(lengths, source, p, first_sym, first_used), second: $Z.DECSYM(lengths, source, p, second_sym, second_used))
  : [first_sym + 1 == second_sym] void =
  $Z.decsym_functional(fit, first, second)

implement main0 () = ()
