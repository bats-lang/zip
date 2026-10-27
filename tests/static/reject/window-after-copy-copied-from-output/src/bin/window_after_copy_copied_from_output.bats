#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The copy is read from the window: a copy of the output is another cells *)
prfn _from_output {window,output,after,both,next_window:$A.cells}{distance,length:nat}
  (copied: $Z.COPY(output, distance, length, both), taken: $Z.TAKE_LAST(both, 32768, next_window), w: $Z.WINDOW(after, next_window)): $Z.WINDOW_AFTER_COPY(window, distance, length, after) =
  $Z.WINDOW_AFTER_COPY_mk(copied, taken, w)

implement main0 () = ()
