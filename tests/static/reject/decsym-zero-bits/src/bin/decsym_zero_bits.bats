#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A decode reads at least one bit: DECSYM_mk refuses used 0 *)
prfn _zero_bits {lengths,source:$A.cells}{p,sym,code:nat}
  (read: $Z.HBITS(source, p, 0, code), coded: $Z.CODE(lengths, sym, code, 0)): $Z.DECSYM(lengths, source, p, sym, 0) =
  $Z.DECSYM_mk(read, coded)

implement main0 () = ()
