#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The code length code lengths are for symbols 0 to 18: from 1 is refused *)
prfn _fact {source,values,order,code_length_code,all_lengths,litlen,dist,before,after:$A.cells}{p,hlit,hdist,hclen,data_start,end_bit:nat | hlit <= 29; hdist <= 29}
  (hlit_bits: $Z.BITS(source, p, 5, hlit),
   hdist_bits: $Z.BITS(source, p + 5, 5, hdist),
   hclen_bits: $Z.BITS(source, p + 10, 4, hclen),
   read: $Z.READ_LENGTHS3(source, p + 14, hclen + 4, values),
   order_proof: $Z.CL_ORDER(order),
   from_proof: $Z.CODE_LENGTHS_FROM(order, hclen + 4, values, 1, code_length_code),
   code_fit: $Z.LENGTHS_FIT(code_length_code, 7),
   code_full: $Z.LENGTHS_FULL(code_length_code, 7),
   lengths_proof: $Z.CODE_LENGTHS(code_length_code, source, p + 14 + 3 * (hclen + 4), $A.cnil(), hlit + 257 + hdist + 1, all_lengths, data_start),
   litlen_len: $A.CLEN(litlen, hlit + 257),
   split: $A.APPEND(litlen, dist, all_lengths),
   litlen_usable: $Z.LITLEN_USABLE(litlen),
   dist_usable: $Z.DIST_USABLE(dist),
   syms: $Z.SYMS(litlen, dist, source, data_start, before, after, end_bit))
  : $Z.BLOCK($Z.block_dynamic(), source, p, before, after, end_bit) =
  $Z.BLOCK_dynamic(hlit_bits, hdist_bits, hclen_bits, read, order_proof, from_proof, code_fit, code_full, lengths_proof, litlen_len, split, litlen_usable, dist_usable, syms)

implement main0 () = ()
