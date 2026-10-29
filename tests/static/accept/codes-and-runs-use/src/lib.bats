#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* RUN and SLICE on small cells; the fixed code lengths as four runs and one; the shapes of a code on lengths 1, 1 (complete), 0, 1, 0 (single) and 0, 0 (empty) *)
prfn _run (): $Z.RUN(2, 7, $A.cnil(), $A.ccons(7, $A.ccons(7, $A.cnil()))) = $Z.RUN_cons($Z.RUN_cons($Z.RUN_zero()))

prfn _slice (): $Z.SLICE($A.ccons(5, $A.ccons(6, $A.ccons(7, $A.cnil()))), 1, 2, $A.ccons(6, $A.ccons(7, $A.cnil()))) =
  $Z.SLICE_cons($A.NTH_there($A.NTH_here()), $Z.SLICE_cons($A.NTH_there($A.NTH_there($A.NTH_here())), $Z.SLICE_nil()))

prfn _fixed_litlen {lengths,after_144,after_112,after_24:$A.cells}
  (first: $Z.RUN(144, 8, after_144, lengths), second: $Z.RUN(112, 9, after_112, after_144), third: $Z.RUN(24, 7, after_24, after_112), fourth: $Z.RUN(8, 8, $A.cnil(), after_24))
  : $Z.FIXED_LITLEN(lengths) = $Z.FIXED_LITLEN_mk(first, second, third, fourth)

prfn _fixed_dist {lengths:$A.cells} (run: $Z.RUN(32, 5, $A.cnil(), lengths)): $Z.FIXED_DIST(lengths) = $Z.FIXED_DIST_mk(run)

prfn _two_ones (): $Z.BL_COUNT($A.ccons(1, $A.ccons(1, $A.cnil())), 1, 2) =
  $Z.BL_COUNT_mk($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil())), $Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_zero())))

prfn _full (): $Z.LENGTHS_FULL($A.ccons(1, $A.ccons(1, $A.cnil())), 1) = $Z.LENGTHS_FULL_mk($Z.NEXT_CODE_first(), _two_ones(), $AR.POW2_succ($AR.POW2_zero()))

prfn _single (): $Z.LENGTHS_SINGLE($A.ccons(0, $A.ccons(1, $A.ccons(0, $A.cnil())))) =
  $Z.LENGTHS_SINGLE_mk($A.CLEN_cons($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil()))),
    $Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_zero()))),
    $Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_miss($Z.COUNT_BEFORE_zero()))))

prfn _empty (): $Z.LENGTHS_EMPTY($A.ccons(0, $A.ccons(0, $A.cnil()))) =
  $Z.LENGTHS_EMPTY_mk($A.CLEN_cons($A.CLEN_cons($A.CLEN_nil())), $Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_hit($Z.COUNT_BEFORE_zero())))

prfn _litlen_full {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 15), full: $Z.LENGTHS_FULL(lengths, 15)): $Z.LITLEN_USABLE(lengths) = $Z.LITLEN_USABLE_full(fit, full)
prfn _litlen_single {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 15), single: $Z.LENGTHS_SINGLE(lengths)): $Z.LITLEN_USABLE(lengths) = $Z.LITLEN_USABLE_single(fit, single)
prfn _dist_full {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 15), full: $Z.LENGTHS_FULL(lengths, 15)): $Z.DIST_USABLE(lengths) = $Z.DIST_USABLE_full(fit, full)
prfn _dist_single {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 15), single: $Z.LENGTHS_SINGLE(lengths)): $Z.DIST_USABLE(lengths) = $Z.DIST_USABLE_single(fit, single)
prfn _dist_empty {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 15), empty: $Z.LENGTHS_EMPTY(lengths)): $Z.DIST_USABLE(lengths) = $Z.DIST_USABLE_empty(fit, empty)
