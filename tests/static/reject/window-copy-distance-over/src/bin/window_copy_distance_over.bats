#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A distance reaches back at most 32768 cells: 32769 is refused *)
prfn _too_far {output,window,after:$A.cells}{length:nat}
  (w: $Z.WINDOW(output, window), copied: $Z.COPY(output, 32769, length, after)): $Z.WINDOW_AFTER_COPY(window, 32769, length, after) =
  $Z.window_copy(w, copied)

implement main0 () = ()
