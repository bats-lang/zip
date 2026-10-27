#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A distance is at most 32768 (the table of 3.2.5): 32767 is refused *)
prfn _below {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (symbol: $Z.DISTANCE_SYMBOL(sym, extra_bits, base), bits: $Z.BITS(source, p, extra_bits, value)): [base + value <= 32767] void =
  $Z.distance_range(symbol, bits)

implement main0 () = ()
