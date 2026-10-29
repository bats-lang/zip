#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Cell i of the chunk is cell start + i of the consumed cells: start + i + 1 is refused *)
prfn _off {previous,chunk,consumed:$A.cells}{start,index,value:nat}
  (at: $Z.BUFFER_AT(previous, chunk, consumed, start), found: $A.NTH(chunk, index, value)): $A.NTH(consumed, start + index + 1, value) =
  $Z.buffer_nth(at, found)

implement main0 () = ()
