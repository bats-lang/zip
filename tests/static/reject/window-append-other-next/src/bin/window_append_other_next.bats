#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The window after is of the output after the append *)
prfn _other_next {output,window,data,next,other:$A.cells}{count:nat}
  (w: $Z.WINDOW(output, window), appended: $A.APPEND(output, data, next), len: $A.CLEN(data, count)): $Z.WINDOW_AFTER_APPEND(window, data, other) =
  $Z.window_append(w, appended, len)

implement main0 () = ()
