#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
staload Z = "zip/src/lib.sats"
#target native begin

(* a reader that ended read the range of its fate *)
fn _ended {compressed:$A.cells}{start,size_in:nat} (file_read: $F.FILE_READ(compressed, start + 1, size_in) | ): $Z.reader_fate(start, size_in) =
  $Z.reader_ended(file_read | )

end

implement main0 () = ()
