#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use zip as Z

(* the output barr holds the cells the proof names, not others *)
fn _other {compressed,other:$A.cells} (answer: $Z.inflated_cells(compressed)): int =
  case+ answer of
  | ~$Z.inflated_cells_done(inflates, output_len | output) => let
      val taken: [l:agz][size:pos] $A.barr(l, size, other) = output
    in ($A.barr_free(taken); 1) end
  | ~$Z.inflated_cells_empty(inflates | ) => 2
  | ~$Z.inflated_cells_malformed() => 3
  | ~$Z.inflated_cells_too_large() => 4

implement main0 () = ()
