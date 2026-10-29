#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A length is at most 258 (symbol 284 with 31 reaches it): 257 is refused *)
prfn _below {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (symbol: $Z.LENGTH_SYMBOL(sym, extra_bits, base), bits: $Z.BITS(source, p, extra_bits, value)): [base + value <= 257] void =
  $Z.length_range(symbol, bits)

implement main0 () = ()
