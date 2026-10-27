#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The window keeps 32768 cells: a TAKE_LAST of 32767 is not a WINDOW *)
prfn _short_keep {output,window:$A.cells} (taken: $Z.TAKE_LAST(output, 32767, window)): $Z.WINDOW(output, window) = $Z.WINDOW_mk(taken)

implement main0 () = ()
