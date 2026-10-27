#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
#use zip as Z
#target native begin

(* the reader has consumed nothing yet *)
fn _call {start,size_in:nat}
  (reader: $F.content_reader($A.ccons(1, $A.cnil()), start, size_in), writer: $F.content_writer($A.cnil()), start: int start, size_in: int size_in): $Z.inflated(start, size_in) =
  $Z.inflate_proved(reader, writer, start, size_in)

end

implement main0 () = ()
