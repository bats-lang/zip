#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* The next code starts after the 3 extra bits: after 7 is refused *)
prfn _fact {code_length_code,source,so_far,next,lengths,run:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit:nat | so_far_count + 3 + extra_value <= total}
  (so_far_len: $A.CLEN(so_far, so_far_count),
   decoded: $Z.DECSYM(code_length_code, source, p, sym, used),
   class: $Z.LENGTH_CLASS($Z.length_zeros_short(), sym),
   extra: $Z.BITS(source, p + used, 3, extra_value),
   run_of: $Z.RUN(3 + extra_value, 0, $A.cnil(), run),
   appended: $A.APPEND(so_far, run, next),
   rest: $Z.CODE_LENGTHS(code_length_code, source, p + used + 7, next, total, lengths, end_bit))
  : $Z.CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit) =
  $Z.CODE_LENGTHS_zeros_short(so_far_len, decoded, class, extra, run_of, appended, rest)

implement main0 () = ()
