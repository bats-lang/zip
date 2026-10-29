#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The cells cut are the window followed by the data: the data first is refused *)
prfn _order {window,data,next,both,next_window:$A.cells}
  (appended: $A.APPEND(data, window, both), taken: $Z.TAKE_LAST(both, 32768, next_window), w: $Z.WINDOW(next, next_window)): $Z.WINDOW_AFTER_APPEND(window, data, next) =
  $Z.WINDOW_AFTER_APPEND_mk(appended, taken, w)

implement main0 () = ()
