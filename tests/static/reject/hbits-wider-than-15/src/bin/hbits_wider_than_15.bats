#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A Huffman code has at most 15 bits: HBITS_snoc refuses width 16 *)
prfn _sixteen {source:$A.cells}{p,code:nat} (rest: $Z.HBITS(source, p, 15, code), last: $Z.BIT(source, p + 15, 0)): $Z.HBITS(source, p, 16, 2 * code) =
  $Z.HBITS_snoc(rest, last)

implement main0 () = ()
