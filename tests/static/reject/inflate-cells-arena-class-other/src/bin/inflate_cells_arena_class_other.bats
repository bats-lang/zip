#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* the class proof is of the size the arena has: 4 MiB is not 16 MiB *)
fn _call {l:agz}{n:nat}{cs:$A.cells} (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): $Z.inflated_cells_arena(cs) =
  $Z.inflate_cells_arena_proved(size, $A.Arena4MiB() | compressed, n, 16777216)

implement main0 () = ()
