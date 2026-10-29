#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* RFC 1951 3.2.5: symbols 265 (11, one extra bit), 284 (227, five) and 285 (258); distance symbols 4 (5, one extra bit) and 29 (24577, thirteen); and the ranges *)
prfn _length_265 (power: $AR.POW2(1, 2)): $Z.LENGTH_SYMBOL(265, 1, 11) = $Z.LENGTH_SYMBOL_base_4_times(power)
prfn _length_284 (power: $AR.POW2(5, 32)): $Z.LENGTH_SYMBOL(284, 5, 227) = $Z.LENGTH_SYMBOL_base_7_times(power)
prfn _length_285 (): $Z.LENGTH_SYMBOL(285, 0, 258) = $Z.LENGTH_SYMBOL_last()
prfn _distance_4 (power: $AR.POW2(1, 2)): $Z.DISTANCE_SYMBOL(4, 1, 5) = $Z.DISTANCE_SYMBOL_base_2_times(power)
prfn _distance_29 (power: $AR.POW2(13, 8192)): $Z.DISTANCE_SYMBOL(29, 13, 24577) = $Z.DISTANCE_SYMBOL_base_3_times(power)

prfn _ranges {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (length: $Z.LENGTH_SYMBOL(sym, extra_bits, base), length_bits: $Z.BITS(source, p, extra_bits, value)): [3 <= base + value; base + value <= 258] void =
  $Z.length_range(length, length_bits)

prfn _distance_ranges {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (distance: $Z.DISTANCE_SYMBOL(sym, extra_bits, base), distance_bits: $Z.BITS(source, p, extra_bits, value)): [1 <= base + value; base + value <= 32768] void =
  $Z.distance_range(distance, distance_bits)
