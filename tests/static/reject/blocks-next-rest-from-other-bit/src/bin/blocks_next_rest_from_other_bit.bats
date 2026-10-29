#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The blocks after a non-final block start where it ends: another bit is refused *)
prfn _other_bit {source:$A.cells}{p,btype,end_bit:nat}{before,middle,after:$A.cells}
  (bfinal: $Z.BITS(source, p, 1, 0), btype_bits: $Z.BITS(source, p + 1, 2, btype), kind: $Z.BTYPE($Z.block_stored(), btype),
   block: $Z.BLOCK($Z.block_stored(), source, p + 3, before, middle, end_bit), rest: $Z.BLOCKS(source, end_bit + 1, middle, after))
  : $Z.BLOCKS(source, p, before, after) =
  $Z.BLOCKS_next(bfinal, btype_bits, kind, block, rest)

implement main0 () = ()
