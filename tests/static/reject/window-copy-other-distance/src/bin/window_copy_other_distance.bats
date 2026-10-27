#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The copy in the window has the distance of the copy in the output *)
prfn _other_distance {output,window,after:$A.cells}{distance,length:nat | distance <= 32768}
  (w: $Z.WINDOW(output, window), copied: $Z.COPY(output, distance, length, after)): $Z.WINDOW_AFTER_COPY(window, distance + 1, length, after) =
  $Z.window_copy(w, copied)

implement main0 () = ()
