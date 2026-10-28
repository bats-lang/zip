#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* an output of more than a barr can hold is the answer too large *)
fn _made {compressed,output:$A.cells}{l:agz}
  (inflates: $Z.INFLATES($Z.inflate_deflated(), compressed, output), output_len: $A.CLEN(output, 1048577) | output: $A.barr(l, 1048577, output)): $Z.inflated_cells(compressed) =
  $Z.inflated_cells_done(inflates, output_len | output, 1048577)

implement main0 () = ()
