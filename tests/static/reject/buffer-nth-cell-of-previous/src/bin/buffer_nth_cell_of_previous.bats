#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The cell is a cell of the chunk: a cell of the earlier cells is refused *)
prfn _of_previous {previous,chunk,consumed:$A.cells}{start,index,value:nat}
  (at: $Z.BUFFER_AT(previous, chunk, consumed, start), found: $A.NTH(previous, index, value)): $A.NTH(consumed, start + index, value) =
  $Z.buffer_nth(at, found)

implement main0 () = ()
