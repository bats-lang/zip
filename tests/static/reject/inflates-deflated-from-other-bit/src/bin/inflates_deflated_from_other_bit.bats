#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A Deflate stream starts at bit 0 *)
prfn _from_bit_eight {compressed,output:$A.cells} (blocks: $Z.BLOCKS(compressed, 8, $A.cnil(), output)): $Z.INFLATES($Z.inflate_deflated(), compressed, output) =
  $Z.INFLATES_deflated(blocks)

implement main0 () = ()
