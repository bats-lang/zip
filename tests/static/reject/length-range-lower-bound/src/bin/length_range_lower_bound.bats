#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A length is at least 3: 4 is refused *)
prfn _above {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (symbol: $Z.LENGTH_SYMBOL(sym, extra_bits, base), bits: $Z.BITS(source, p, extra_bits, value)): [4 <= base + value] void =
  $Z.length_range(symbol, bits)

implement main0 () = ()
