#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The window after an append is the window of the output after, and the lemmas of the window are used *)
prfn _append {output,window,data,next:$A.cells}{count:nat}
  (w: $Z.WINDOW(output, window), appended: $A.APPEND(output, data, next), len: $A.CLEN(data, count)): $Z.WINDOW_AFTER_APPEND(window, data, next) =
  $Z.window_append(w, appended, len)

prfn _copy {output,window,after:$A.cells}{distance,length:nat | distance <= 32768}
  (w: $Z.WINDOW(output, window), copied: $Z.COPY(output, distance, length, after)): $Z.WINDOW_AFTER_COPY(window, distance, length, after) =
  $Z.window_copy(w, copied)

prfn _after_append {window,data,next,both,next_window:$A.cells}
  (appended: $A.APPEND(window, data, both), taken: $Z.TAKE_LAST(both, 32768, next_window), w: $Z.WINDOW(next, next_window)): $Z.WINDOW_AFTER_APPEND(window, data, next) =
  $Z.WINDOW_AFTER_APPEND_mk(appended, taken, w)

prfn _after_copy {window,after,both,next_window:$A.cells}{distance,length:nat}
  (copied: $Z.COPY(window, distance, length, both), taken: $Z.TAKE_LAST(both, 32768, next_window), w: $Z.WINDOW(after, next_window)): $Z.WINDOW_AFTER_COPY(window, distance, length, after) =
  $Z.WINDOW_AFTER_COPY_mk(copied, taken, w)
