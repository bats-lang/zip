#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A Deflate stream is not a stored entry: INFLATES_deflated builds the deflated kind *)
prfn _claimed_stored {compressed,output:$A.cells} (blocks: $Z.BLOCKS(compressed, 0, $A.cnil(), output)): $Z.INFLATES($Z.inflate_stored(), compressed, output) =
  $Z.INFLATES_deflated(blocks)

implement main0 () = ()
