#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The two BTYPE bits follow BFINAL at p + 1: bits at p + 2 are refused *)
prfn _shifted {source:$A.cells}{p,btype,end_bit:nat}{before,after:$A.cells}
  (bfinal: $Z.BITS(source, p, 1, 1), btype_bits: $Z.BITS(source, p + 2, 2, btype), kind: $Z.BTYPE($Z.block_stored(), btype), block: $Z.BLOCK($Z.block_stored(), source, p + 3, before, after, end_bit))
  : $Z.BLOCKS(source, p, before, after) =
  $Z.BLOCKS_last(bfinal, btype_bits, kind, block)

implement main0 () = ()
