#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* the size beside the output is the size in its type, not another one *)
fn _made {compressed,output:$A.cells}{l:agz}
  (inflates: $Z.INFLATES($Z.inflate_deflated(), compressed, output), output_len: $A.CLEN(output, 4) | output: $A.barr(l, 4, output)): $Z.inflated_cells(compressed) =
  $Z.inflated_cells_done(inflates, output_len | output, 5)

implement main0 () = ()
