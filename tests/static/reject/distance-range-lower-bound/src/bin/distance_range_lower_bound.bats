#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A distance is at least 1: 2 is refused *)
prfn _above {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (symbol: $Z.DISTANCE_SYMBOL(sym, extra_bits, base), bits: $Z.BITS(source, p, extra_bits, value)): [2 <= base + value] void =
  $Z.distance_range(symbol, bits)

implement main0 () = ()
