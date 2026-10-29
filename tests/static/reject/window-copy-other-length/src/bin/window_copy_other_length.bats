#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The copy in the window has the length of the copy in the output *)
prfn _other_length {output,window,after:$A.cells}{distance,length:nat | distance <= 32768}
  (w: $Z.WINDOW(output, window), copied: $Z.COPY(output, distance, length, after)): $Z.WINDOW_AFTER_COPY(window, distance, length + 1, after) =
  $Z.window_copy(w, copied)

implement main0 () = ()
