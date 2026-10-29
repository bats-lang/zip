#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A Deflate stream starts with no output: blocks that start from some output are refused *)
prfn _from_output {compressed,output:$A.cells} (blocks: $Z.BLOCKS(compressed, 0, $A.ccons(1, $A.cnil()), output)): $Z.INFLATES($Z.inflate_deflated(), compressed, output) =
  $Z.INFLATES_deflated(blocks)

implement main0 () = ()
