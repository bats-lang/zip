#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The whole is the earlier cells followed by the later: another cells is refused *)
prfn _other_whole {earlier,later,whole,other:$A.cells}{p,width,value:nat}
  (appended: $A.APPEND(earlier, later, whole), bits: $Z.BITS(earlier, p, width, value)): $Z.BITS(other, p, width, value) =
  $Z.bits_in_prefix(appended, bits)

implement main0 () = ()
