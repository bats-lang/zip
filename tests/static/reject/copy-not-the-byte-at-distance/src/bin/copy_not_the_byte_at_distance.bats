#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* The byte copied is the one distance back from the end: the one at distance - 1 is refused *)
prfn _off_by_one {output,next,after:$A.cells}{output_count,distance,length,copied:nat | 1 <= distance; distance <= output_count; distance >= 2}
  (clen: $A.CLEN(output, output_count), found: $A.NTH(output, output_count - distance + 1, copied), appended: $A.APPEND(output, $A.ccons(copied, $A.cnil()), next), rest: $Z.COPY(next, distance, length, after))
  : $Z.COPY(output, distance, length + 1, after) =
  $Z.COPY_step{output, next, after}{output_count, distance, length, copied}(clen, found, appended, rest)

implement main0 () = ()
