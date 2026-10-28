#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The run is 3 plus the two extra bits: 2 plus is refused *)
prfn _fact {code_length_code,source,so_far,next,lengths,run:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit,previous:nat | 1 <= so_far_count; so_far_count + 3 + extra_value <= total}
  (so_far_len: $A.CLEN(so_far, so_far_count),
   decoded: $Z.DECSYM(code_length_code, source, p, sym, used),
   class: $Z.LENGTH_CLASS($Z.length_repeat_previous(), sym),
   extra: $Z.BITS(source, p + used, 2, extra_value),
   previous_length: $A.NTH(so_far, so_far_count - 1, previous),
   run_of: $Z.RUN(2 + extra_value, previous, $A.cnil(), run),
   appended: $A.APPEND(so_far, run, next),
   rest: $Z.CODE_LENGTHS(code_length_code, source, p + used + 2, next, total, lengths, end_bit))
  : $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit) =
  $Z.CODE_LENGTHS_repeat_previous(so_far_len, decoded, class, extra, previous_length, run_of, appended, rest)

implement main0 () = ()
