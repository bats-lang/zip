#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* BLOCKS_next needs BFINAL 0: a first bit that is 1 is refused *)
prfn _final {source:$A.cells}{p,btype,end_bit:nat}{before,middle,after:$A.cells}
  (bfinal: $Z.BITS(source, p, 1, 1), btype_bits: $Z.BITS(source, p + 1, 2, btype), kind: $Z.BTYPE($Z.block_stored(), btype),
   block: $Z.BLOCK($Z.block_stored(), source, p + 3, before, middle, end_bit), rest: $Z.BLOCKS(source, end_bit, middle, after))
  : $Z.BLOCKS(source, p, before, after) =
  $Z.BLOCKS_next(bfinal, btype_bits, kind, block, rest)

implement main0 () = ()
