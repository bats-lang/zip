#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A copy starts with a length symbol: the literal class is refused *)
prfn _fact {litlen,dist,source,output,next,after:$A.cells}{p,sym,used,length_extra_bits,length_base,length_extra_value,dist_sym,dist_used,dist_extra_bits,dist_base,dist_extra_value,end_bit:nat | sym == 285 || length_base + length_extra_value <= 257}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used),
   class: $Z.SYMBOL_CLASS($Z.symbol_literal(), sym),
   length_symbol: $Z.LENGTH_SYMBOL(sym, length_extra_bits, length_base),
   length_bits: $Z.BITS(source, p + used, length_extra_bits, length_extra_value),
   dist_decoded: $Z.DECSYM(dist, source, p + used + length_extra_bits, dist_sym, dist_used),
   dist_symbol: $Z.DISTANCE_SYMBOL(dist_sym, dist_extra_bits, dist_base),
   dist_bits: $Z.BITS(source, p + used + length_extra_bits + dist_used, dist_extra_bits, dist_extra_value),
   copied: $Z.COPY(output, dist_base + dist_extra_value, length_base + length_extra_value, next),
   rest: $Z.SYMS(litlen, dist, source, p + used + length_extra_bits + dist_used + dist_extra_bits, next, after, end_bit))
  : $Z.SYMS(litlen, dist, source, p, output, after, end_bit) =
  $Z.SYMS_copy(decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied, rest)

implement main0 () = ()
