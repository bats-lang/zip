#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The window after is of the output after: the cut cells must be its window *)
prfn _other_window {window,data,next,both,next_window,other:$A.cells}
  (appended: $A.APPEND(window, data, both), taken: $Z.TAKE_LAST(both, 32768, next_window), w: $Z.WINDOW(next, other)): $Z.WINDOW_AFTER_APPEND(window, data, next) =
  $Z.WINDOW_AFTER_APPEND_mk(appended, taken, w)

implement main0 () = ()
