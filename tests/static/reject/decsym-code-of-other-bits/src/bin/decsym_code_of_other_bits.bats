#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The code of the decoded symbol must be the bits read: another code is refused *)
prfn _other_code {lengths,source:$A.cells}{p,sym,used,read_code,symbol_code:nat | 1 <= used; used <= 15}
  (read: $Z.HBITS(source, p, used, read_code), coded: $Z.CODE(lengths, sym, symbol_code, used)): $Z.DECSYM(lengths, source, p, sym, used) =
  $Z.DECSYM_mk(read, coded)

implement main0 () = ()
