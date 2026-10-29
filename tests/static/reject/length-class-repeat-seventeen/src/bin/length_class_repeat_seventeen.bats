#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Only symbol 16 repeats the previous length *)
prfn _seventeen (): $Z.LENGTH_CLASS($Z.length_repeat_previous(), 17) = $Z.LENGTH_CLASS_repeat_previous()

implement main0 () = ()
