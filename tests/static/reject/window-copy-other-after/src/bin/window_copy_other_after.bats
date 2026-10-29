#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The window after is of the output after the copy *)
prfn _other_after {output,window,after,other:$A.cells}{distance,length:nat | distance <= 32768}
  (w: $Z.WINDOW(output, window), copied: $Z.COPY(output, distance, length, after)): $Z.WINDOW_AFTER_COPY(window, distance, length, other) =
  $Z.window_copy(w, copied)

implement main0 () = ()
