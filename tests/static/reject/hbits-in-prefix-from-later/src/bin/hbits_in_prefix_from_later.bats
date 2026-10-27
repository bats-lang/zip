#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The Huffman bits are of the earlier cells *)
prfn _from_later {earlier,later,whole:$A.cells}{p,width,code:nat}
  (appended: $A.APPEND(earlier, later, whole), bits: $Z.HBITS(later, p, width, code)): $Z.HBITS(whole, p, width, code) =
  $Z.hbits_in_prefix(appended, bits)

implement main0 () = ()
