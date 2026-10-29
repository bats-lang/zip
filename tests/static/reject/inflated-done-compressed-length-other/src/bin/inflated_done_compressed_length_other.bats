#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
staload Z = "zip/src/lib.sats"
#target native begin

(* the compressed cells have as many bytes as the range *)
fn _made {compressed,output:$A.cells}{start,size_in,size:nat | size <= 2147483647}
  (inflates: $Z.INFLATES($Z.inflate_deflated(), compressed, output), compressed_len: $A.CLEN(compressed, size_in + 1), output_len: $A.CLEN(output, size),
   file_read: $F.FILE_READ(compressed, start, size_in), holds: $F.FILE_HOLDS(output) | size: int size): $Z.inflated(start, size_in) =
  $Z.inflated_done(inflates, compressed_len, output_len, file_read, holds | size)

end

implement main0 () = ()
