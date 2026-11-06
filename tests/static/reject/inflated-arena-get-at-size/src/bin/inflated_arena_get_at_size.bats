#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* a cell of the output is below its size: the cell at the size is not one *)
fn _call {output,junk,buffer:$A.cells}{l:agz}{max,size:nat | size <= max}
  (output_len: $A.CLEN(output, size), appended: $A.APPEND(output, junk, buffer) | buffer: !$A.barr(l, max, buffer), size: int size): int = let
  val (found | v) = $Z.inflated_arena_get(output_len, appended | buffer, size)
in v end

implement main0 () = ()
