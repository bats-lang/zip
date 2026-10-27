#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The start is the number of cells before the chunk: another number is refused *)
prfn _start {previous,chunk,consumed:$A.cells}{start,other:nat}
  (len: $A.CLEN(previous, other), appended: $A.APPEND(previous, chunk, consumed)): $Z.BUFFER_AT(previous, chunk, consumed, start) =
  $Z.BUFFER_AT_mk(len, appended)

implement main0 () = ()
