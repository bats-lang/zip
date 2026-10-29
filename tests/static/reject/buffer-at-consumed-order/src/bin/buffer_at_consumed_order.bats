#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The consumed cells are the earlier cells and then the chunk: the chunk first is refused *)
prfn _order {previous,chunk,consumed:$A.cells}{start:nat}
  (len: $A.CLEN(previous, start), appended: $A.APPEND(chunk, previous, consumed)): $Z.BUFFER_AT(previous, chunk, consumed, start) =
  $Z.BUFFER_AT_mk(len, appended)

implement main0 () = ()
