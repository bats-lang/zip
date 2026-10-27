#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* the answer too large is a case of its own: a match that leaves it out is refused *)
fn _answer {compressed:$A.cells} (answer: $Z.inflated_cells(compressed)): int =
  case+ answer of
  | ~$Z.inflated_cells_done(inflates, output_len | output) => ($A.barr_free(output); 1)
  | ~$Z.inflated_cells_empty(inflates | ) => 2
  | ~$Z.inflated_cells_malformed() => 3

implement main0 () = ()
