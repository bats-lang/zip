#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The window must be of the output copied in *)
prfn _other_output {output,other,window,after:$A.cells}{distance,length:nat | distance <= 32768}
  (w: $Z.WINDOW(other, window), copied: $Z.COPY(output, distance, length, after)): $Z.WINDOW_AFTER_COPY(window, distance, length, after) =
  $Z.window_copy(w, copied)

implement main0 () = ()
