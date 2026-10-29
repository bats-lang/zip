#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* the length given is the length of the cells *)
fn _call {l:agz}{cs:$A.cells}{n:nat | n <= 1048575} (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): $Z.inflated_cells(cs) =
  $Z.inflate_cells_proved(size | compressed, n + 1)

implement main0 () = ()
