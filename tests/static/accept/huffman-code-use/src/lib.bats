#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* RFC 1951 3.2.2 on lengths 1, 2, 2: the symbols get the codes 0, 10 and 11; the third is the 2-bit code 3 *)
(* lengths = $A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))): next_code[1] = 0, next_code[2] = 2 * (0 + 1) = 2 *)
prfn _one_length_one (): $Z.BL_COUNT($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 1, 1) =
  $Z.BL_COUNT_mk($A.CLEN_cons($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))),
    $Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_zero()))))

prfn _first_code_of_two (): $Z.NEXT_CODE($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 2) =
  $Z.NEXT_CODE_next($Z.NEXT_CODE_first(), _one_length_one())

prfn _rank_of_third (): $Z.COUNT_BEFORE($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 2, 1) =
  $Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_zero()))

prfn _third_is_at_two (): $A.NTH($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 2) = $A.NTH_there($A.NTH_there($A.NTH_here()))

prfn _third_code (): $Z.CODE($A.ccons(1, $A.ccons(2, $A.ccons(2, $A.cnil()))), 2, 3, 2) = $Z.CODE_mk(_third_is_at_two(), _first_code_of_two(), _rank_of_third())

prfn _the_lemmas {lengths:$A.cells}{len,first_count,second_count,first_code,second_code:nat}
  (first: $Z.BL_COUNT(lengths, len, first_count), second: $Z.BL_COUNT(lengths, len, second_count),
   first_next: $Z.NEXT_CODE(lengths, len, first_code), second_next: $Z.NEXT_CODE(lengths, len, second_code))
  : [first_count == second_count; first_code == second_code] void = let
    prval () = $Z.bl_count_functional(first, second)
    prval () = $Z.next_code_functional(first_next, second_next)
  in () end
