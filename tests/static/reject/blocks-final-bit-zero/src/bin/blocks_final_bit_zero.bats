#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* BLOCKS_last needs BFINAL 1: a first bit that is 0 is refused *)
prfn _not_final {source:$A.cells}{p,btype,end_bit:nat}{before,after:$A.cells}
  (bfinal: $Z.BITS(source, p, 1, 0), btype_bits: $Z.BITS(source, p + 1, 2, btype), kind: $Z.BTYPE($Z.block_stored(), btype), block: $Z.BLOCK($Z.block_stored(), source, p + 3, before, after, end_bit))
  : $Z.BLOCKS(source, p, before, after) =
  $Z.BLOCKS_last(bfinal, btype_bits, kind, block)

implement main0 () = ()
