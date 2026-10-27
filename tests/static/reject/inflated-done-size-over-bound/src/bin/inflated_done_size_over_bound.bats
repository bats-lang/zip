#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
#use zip as Z
#target native begin

(* the output of the reader and writer forms is at most 2147483647 bytes *)
fn _made {compressed,output:$A.cells}{start,size_in:nat}
  (inflates: $Z.INFLATES($Z.inflate_deflated(), compressed, output), compressed_len: $A.CLEN(compressed, size_in), output_len: $A.CLEN(output, 2147483648),
   file_read: $F.FILE_READ(compressed, start, size_in), holds: $F.FILE_HOLDS(output) | size: int 2147483648): $Z.inflated(start, size_in) =
  $Z.inflated_done(inflates, compressed_len, output_len, file_read, holds | size)

end

implement main0 () = ()
