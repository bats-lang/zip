#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* Bits read from the first chunk are bits of the whole consumed sequence; the buffer's cell is a cell of the consumed cells; the reservoir is bits of them *)
prfn _in_prefix {earlier,later,whole:$A.cells}{p,width,value:nat}
  (appended: $A.APPEND(earlier, later, whole), bits: $Z.BITS(earlier, p, width, value)): $Z.BITS(whole, p, width, value) =
  $Z.bits_in_prefix(appended, bits)

prfn _hin_prefix {earlier,later,whole:$A.cells}{p,width,code:nat}
  (appended: $A.APPEND(earlier, later, whole), bits: $Z.HBITS(earlier, p, width, code)): $Z.HBITS(whole, p, width, code) =
  $Z.hbits_in_prefix(appended, bits)

prfn _buffer {previous,chunk,consumed:$A.cells}{start,index,value:nat}
  (at: $Z.BUFFER_AT(previous, chunk, consumed, start), found: $A.NTH(chunk, index, value)): $A.NTH(consumed, start + index, value) =
  $Z.buffer_nth(at, found)

prfn _buffer_at {previous,chunk,consumed:$A.cells}{start:nat}
  (len: $A.CLEN(previous, start), appended: $A.APPEND(previous, chunk, consumed)): $Z.BUFFER_AT(previous, chunk, consumed, start) =
  $Z.BUFFER_AT_mk(len, appended)

prfn _reservoir {consumed:$A.cells}{p,count,value:nat} (bits: $Z.BITS(consumed, p, count, value)): $Z.RESERVOIR(consumed, p, count, value) =
  $Z.RESERVOIR_mk(bits)

prfn _first_byte_of_two (found: $A.NTH($A.ccons(5, $A.cnil()), 0, 5), appended: $A.APPEND($A.ccons(5, $A.cnil()), $A.ccons(7, $A.cnil()), $A.ccons(5, $A.ccons(7, $A.cnil())))): $A.NTH($A.ccons(5, $A.ccons(7, $A.cnil())), 0, 5) =
  $A.NTH_here()
