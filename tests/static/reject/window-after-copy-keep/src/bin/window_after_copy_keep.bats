#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The window after a copy keeps 32768 cells: 32767 is refused *)
prfn _keep {window,after,both,next_window:$A.cells}{distance,length:nat}
  (copied: $Z.COPY(window, distance, length, both), taken: $Z.TAKE_LAST(both, 32767, next_window), w: $Z.WINDOW(after, next_window)): $Z.WINDOW_AFTER_COPY(window, distance, length, after) =
  $Z.WINDOW_AFTER_COPY_mk(copied, taken, w)

implement main0 () = ()
