#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* the barr of the compressed cells holds 1 MiB at most *)
fn _call {l:agz}{cs:$A.cells} (size: $A.CLEN(cs, 1048577) | compressed: !$A.cborrow(l, 1048577, cs)): $Z.inflated_cells(cs) =
  $Z.inflate_cells_proved(size | compressed, 1048577)

implement main0 () = ()
