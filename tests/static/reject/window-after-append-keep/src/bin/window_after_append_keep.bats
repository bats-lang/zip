#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The window after an append keeps 32768 cells: 32767 is refused *)
prfn _keep {window,data,next,both,next_window:$A.cells}
  (appended: $A.APPEND(window, data, both), taken: $Z.TAKE_LAST(both, 32767, next_window), w: $Z.WINDOW(next, next_window)): $Z.WINDOW_AFTER_APPEND(window, data, next) =
  $Z.WINDOW_AFTER_APPEND_mk(appended, taken, w)

implement main0 () = ()
