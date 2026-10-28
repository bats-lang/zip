#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* Only symbol 16 repeats the previous length *)
prfn _seventeen (): $Z.LENGTH_CLASS($Z.length_repeat_previous(), 17) = $Z.LENGTH_CLASS_repeat_previous()

implement main0 () = ()
