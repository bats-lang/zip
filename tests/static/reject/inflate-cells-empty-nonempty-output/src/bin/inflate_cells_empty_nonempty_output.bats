#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* the empty answer says the output is no cell at all *)
fn _made {compressed:$A.cells} (inflates: $Z.INFLATES($Z.inflate_deflated(), compressed, $A.ccons(1, $A.cnil())) | ): $Z.inflated_cells(compressed) =
  $Z.inflated_cells_empty(inflates | )

implement main0 () = ()
