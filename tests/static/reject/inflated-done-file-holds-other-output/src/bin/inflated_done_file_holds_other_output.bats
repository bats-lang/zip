#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
#use zip as Z
#target native begin

(* the file holds the output the proof names *)
fn _made {compressed,output,other:$A.cells}{start,size_in,size:nat | size <= 2147483647}
  (inflates: $Z.INFLATES($Z.inflate_deflated(), compressed, output), compressed_len: $A.CLEN(compressed, size_in), output_len: $A.CLEN(output, size),
   file_read: $F.FILE_READ(compressed, start, size_in), holds: $F.FILE_HOLDS(other) | size: int size): $Z.inflated(start, size_in) =
  $Z.inflated_done(inflates, compressed_len, output_len, file_read, holds | size)

end

implement main0 () = ()
