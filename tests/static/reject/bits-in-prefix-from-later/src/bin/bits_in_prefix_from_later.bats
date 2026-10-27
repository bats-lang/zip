#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The bits are of the earlier cells: bits of the later cells are not bits of the whole at the same position *)
prfn _from_later {earlier,later,whole:$A.cells}{p,width,value:nat}
  (appended: $A.APPEND(earlier, later, whole), bits: $Z.BITS(later, p, width, value)): $Z.BITS(whole, p, width, value) =
  $Z.bits_in_prefix(appended, bits)

implement main0 () = ()
