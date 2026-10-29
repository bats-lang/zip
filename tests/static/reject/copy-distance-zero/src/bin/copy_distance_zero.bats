#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A distance is at least 1: COPY_step refuses 0 *)
prfn _zero {output,next,after:$A.cells}{output_count,length,copied:nat}
  (clen: $A.CLEN(output, output_count), found: $A.NTH(output, output_count, copied), appended: $A.APPEND(output, $A.ccons(copied, $A.cnil()), next), rest: $Z.COPY(next, 0, length, after))
  : $Z.COPY(output, 0, length + 1, after) =
  $Z.COPY_step{output, next, after}{output_count, 0, length, copied}(clen, found, appended, rest)

implement main0 () = ()
