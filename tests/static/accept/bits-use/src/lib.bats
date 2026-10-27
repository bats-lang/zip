#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The bits of the byte 5 (101, least significant first): bit 0 is 1, bit 1 is 0; read as BITS they are 1, as HBITS 2 *)
prfn _bit_zero {source:$A.cells} (found: $A.NTH(source, 0, 5)): $Z.BIT(source, 0, 1) =
  $Z.BIT_mk(found, $Z.BYTE_BIT_here{2}{1}())

prfn _bit_one {source:$A.cells} (found: $A.NTH(source, 0, 5)): $Z.BIT(source, 1, 0) =
  $Z.BIT_mk(found, $Z.BYTE_BIT_there{2, 0}{0, 1}($Z.BYTE_BIT_here{1}{0}()))

prfn _bits {source:$A.cells} (first: $Z.BIT(source, 0, 1), second: $Z.BIT(source, 1, 0)): $Z.BITS(source, 0, 2, 1) =
  $Z.BITS_cons(first, $Z.BITS_cons(second, $Z.BITS_nil()))

prfn _hbits {source:$A.cells} (first: $Z.BIT(source, 0, 1), second: $Z.BIT(source, 1, 0)): $Z.HBITS(source, 0, 2, 2) =
  $Z.HBITS_snoc($Z.HBITS_snoc($Z.HBITS_nil(), first), second)

prfn _functional {source:$A.cells}{p,width,first_value,second_value:nat}
  (first: $Z.BITS(source, p, width, first_value), second: $Z.BITS(source, p, width, second_value)): [first_value == second_value] void =
  $Z.bits_functional(first, second)
