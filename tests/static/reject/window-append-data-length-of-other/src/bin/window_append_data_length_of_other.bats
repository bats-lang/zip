#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The length given must be of the data appended *)
prfn _other_len {output,window,data,other,next:$A.cells}{count:nat}
  (w: $Z.WINDOW(output, window), appended: $A.APPEND(output, data, next), len: $A.CLEN(other, count)): $Z.WINDOW_AFTER_APPEND(window, data, next) =
  $Z.window_append(w, appended, len)

implement main0 () = ()
