#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The stored block starts at the next byte boundary at or after the header: LEN at a byte before p is refused *)
prfn _too_early {source:$A.cells}{p,data_byte,len,nlen:nat | 8 * data_byte + 8 <= p; len + nlen == 65535}{before,data,after:$A.cells}
  (len_bits: $Z.BITS(source, 8 * data_byte, 16, len), nlen_bits: $Z.BITS(source, 8 * data_byte + 16, 16, nlen),
   slice: $Z.SLICE(source, data_byte + 4, len, data), append: $A.APPEND(before, data, after))
  : $Z.BLOCK($Z.block_stored(), source, p, before, after, 8 * (data_byte + 4 + len)) =
  $Z.BLOCK_stored{source}{p, data_byte, len, nlen}{before, data, after}(len_bits, nlen_bits, slice, append)

implement main0 () = ()
