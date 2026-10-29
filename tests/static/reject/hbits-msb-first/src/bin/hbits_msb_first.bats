#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Huffman codes are packed most significant bit first (3.1.1): bits 1 then 0 are the code 2, not 1 *)
prfn _msb_first {source:$A.cells} (first: $Z.BIT(source, 0, 1), second: $Z.BIT(source, 1, 0)): $Z.HBITS(source, 0, 2, 1) =
  $Z.HBITS_snoc($Z.HBITS_snoc($Z.HBITS_nil(), first), second)

implement main0 () = ()
