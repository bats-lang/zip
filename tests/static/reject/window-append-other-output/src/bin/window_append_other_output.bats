#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The window must be the window of the output appended to *)
prfn _other_output {output,other,window,data,next:$A.cells}{count:nat}
  (w: $Z.WINDOW(other, window), appended: $A.APPEND(output, data, next), len: $A.CLEN(data, count)): $Z.WINDOW_AFTER_APPEND(window, data, next) =
  $Z.window_append(w, appended, len)

implement main0 () = ()
