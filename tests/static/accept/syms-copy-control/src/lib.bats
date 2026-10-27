#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The copy symbols of the rejects with every fact right are accepted: a length symbol, its extra bits, a distance symbol, its extra bits and the copy *)
prfn _control {litlen,dist,source,output,next,after:$A.cells}{p,sym,used,length_extra_bits,length_base,length_extra_value,dist_sym,dist_used,dist_extra_bits,dist_base,dist_extra_value,end_bit:nat | sym == 285 || length_base + length_extra_value <= 257}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used), class: $Z.SYMBOL_CLASS($Z.symbol_length(), sym),
   length_symbol: $Z.LENGTH_SYMBOL(sym, length_extra_bits, length_base), length_bits: $Z.BITS(source, p + used, length_extra_bits, length_extra_value),
   dist_decoded: $Z.DECSYM(dist, source, p + used + length_extra_bits, dist_sym, dist_used), dist_symbol: $Z.DISTANCE_SYMBOL(dist_sym, dist_extra_bits, dist_base),
   dist_bits: $Z.BITS(source, p + used + length_extra_bits + dist_used, dist_extra_bits, dist_extra_value),
   copied: $Z.COPY(output, dist_base + dist_extra_value, length_base + length_extra_value, next),
   rest: $Z.SYMS(litlen, dist, source, p + used + length_extra_bits + dist_used + dist_extra_bits, next, after, end_bit))
  : $Z.SYMS(litlen, dist, source, p, output, after, end_bit) =
  $Z.SYMS_copy(decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied, rest)

prfn _end {litlen,dist,source,output:$A.cells}{p,sym,used:nat}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used), class: $Z.SYMBOL_CLASS($Z.symbol_end_of_block(), sym)): $Z.SYMS(litlen, dist, source, p, output, output, p + used) =
  $Z.SYMS_end(decoded, class)

prfn _literal {litlen,dist,source,output,next,after:$A.cells}{p,sym,used,end_bit:nat}
  (decoded: $Z.DECSYM(litlen, source, p, sym, used), class: $Z.SYMBOL_CLASS($Z.symbol_literal(), sym),
   appended: $A.APPEND(output, $A.ccons(sym, $A.cnil()), next), rest: $Z.SYMS(litlen, dist, source, p + used, next, after, end_bit))
  : $Z.SYMS(litlen, dist, source, p, output, after, end_bit) =
  $Z.SYMS_literal(decoded, class, appended, rest)

prfn _lemma {litlen,dist,source:$A.cells}{p:nat}{output,first,second:$A.cells}{first_end,second_end:nat}
  (litlen_fit: $Z.LENGTHS_FIT(litlen, 15), dist_fit: $Z.LENGTHS_FIT(dist, 15), a: $Z.SYMS(litlen, dist, source, p, output, first, first_end), b: $Z.SYMS(litlen, dist, source, p, output, second, second_end))
  : [first_end == second_end] $A.CELLS_EQ(first, second) =
  $Z.syms_functional(litlen_fit, dist_fit, a, b)
