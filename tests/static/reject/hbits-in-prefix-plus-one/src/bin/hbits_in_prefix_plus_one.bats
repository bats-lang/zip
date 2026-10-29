#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The Huffman bits read from the earlier cells are the same code in the whole *)
prfn _plus_one {earlier,later,whole:$A.cells}{p,width,code:nat}
  (appended: $A.APPEND(earlier, later, whole), bits: $Z.HBITS(earlier, p, width, code)): $Z.HBITS(whole, p, width, code + 1) =
  $Z.hbits_in_prefix(appended, bits)

implement main0 () = ()
