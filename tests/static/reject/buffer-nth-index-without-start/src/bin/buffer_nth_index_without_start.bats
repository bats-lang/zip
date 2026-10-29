#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The chunk starts after the earlier cells: index alone is refused *)
prfn _no_start {previous,chunk,consumed:$A.cells}{start,index,value:nat}
  (at: $Z.BUFFER_AT(previous, chunk, consumed, start), found: $A.NTH(chunk, index, value)): $A.NTH(consumed, index, value) =
  $Z.buffer_nth(at, found)

implement main0 () = ()
