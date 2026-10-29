#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The cells appended to the window are the cells appended to the output *)
prfn _other_data {output,window,data,other,next:$A.cells}{count:nat}
  (w: $Z.WINDOW(output, window), appended: $A.APPEND(output, data, next), len: $A.CLEN(data, count)): $Z.WINDOW_AFTER_APPEND(window, other, next) =
  $Z.window_append(w, appended, len)

implement main0 () = ()
