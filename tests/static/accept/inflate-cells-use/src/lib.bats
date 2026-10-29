#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* every answer of the in-memory forms is matched, and the output is a barr whose cells the proof names *)
fn _answer {compressed:$A.cells} (answer: $Z.inflated_cells(compressed)): int =
  case+ answer of
  | ~$Z.inflated_cells_done(inflates, output_len | output, output_size) => ($A.barr_free(output); 1)
  | ~$Z.inflated_cells_empty(inflates | ) => 2
  | ~$Z.inflated_cells_malformed() => 3
  | ~$Z.inflated_cells_too_large() => 4

fn _inflate {l:agz}{n:nat | n <= 1048576}{cs:$A.cells} (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): int =
  _answer($Z.inflate_cells_proved(size | compressed, n))

fn _inflate_stored {l:agz}{n:nat | n <= 1048576}{cs:$A.cells} (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): int =
  _answer($Z.inflate_stored_cells_proved(size | compressed, n))
