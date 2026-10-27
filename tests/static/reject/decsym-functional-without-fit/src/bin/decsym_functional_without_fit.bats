#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Prefix-freeness needs the lengths to fit: two decodings of other lengths are not one symbol *)
prfn _other_lengths {first_lengths,second_lengths,source:$A.cells}{maxlen,p,first_sym,first_used,second_sym,second_used:nat}
  (fit: $Z.LENGTHS_FIT(first_lengths, maxlen), first: $Z.DECSYM(first_lengths, source, p, first_sym, first_used), second: $Z.DECSYM(second_lengths, source, p, second_sym, second_used))
  : [first_sym == second_sym] void =
  $Z.decsym_functional(fit, first, second)

implement main0 () = ()
