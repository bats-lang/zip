#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* A distance reaches back at most the whole output so far: output_count + 1 is refused *)
prfn _too_far {output,next,after:$A.cells}{output_count,length,copied:nat}
  (clen: $A.CLEN(output, output_count), found: $A.NTH(output, 0, copied), appended: $A.APPEND(output, $A.ccons(copied, $A.cnil()), next), rest: $Z.COPY(next, output_count + 1, length, after))
  : $Z.COPY(output, output_count + 1, length + 1, after) =
  $Z.COPY_step{output, next, after}{output_count, output_count + 1, length, copied}(clen, found, appended, rest)

implement main0 () = ()
