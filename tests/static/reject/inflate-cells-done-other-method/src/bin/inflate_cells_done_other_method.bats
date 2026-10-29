#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* the output of a Deflate stream is not the output of a stored entry *)
fn _stored {compressed:$A.cells} (answer: $Z.inflated_cells(compressed)): int =
  case+ answer of
  | ~$Z.inflated_cells_done(inflates, output_len | output, output_size) => let
      prval stored: [kept:$A.cells] $Z.INFLATES($Z.inflate_stored(), compressed, kept) = inflates
    in ($A.barr_free(output); 1) end
  | ~$Z.inflated_cells_empty(inflates | ) => 2
  | ~$Z.inflated_cells_malformed() => 3
  | ~$Z.inflated_cells_too_large() => 4

implement main0 () = ()
