#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* every answer of the arena forms is matched (keyword: arena-output); the output is a prefix of the piece of the arena, read with its
   proof by inflated_arena_get, and given back with the arena by inflated_arena_release *)
fn _answer {compressed:$A.cells} (answer: $Z.inflated_cells_arena(compressed)): int =
  case+ answer of
  | ~$Z.inflated_arena_done(inflates, output_len, appended, lent | arena, output, size) => let
      val (found | first) = $Z.inflated_arena_get(output_len, appended | output, 0)
      val () = $Z.inflated_arena_release(lent | arena, output)
    in 1 end
  | ~$Z.inflated_arena_empty(inflates | ) => 2
  | ~$Z.inflated_arena_malformed() => 3
  | ~$Z.inflated_arena_too_large() => 4
  | ~$Z.inflated_arena_no_memory() => 5

(* the compressed data is not bounded by 1 MiB, and the output is up to the largest class *)
fn _inflate {l:agz}{n:nat}{cs:$A.cells} (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): int =
  _answer($Z.inflate_cells_arena_proved(size, $A.Arena16MiB() | compressed, n, 16777216))

fn _inflate_stored {l:agz}{n:nat}{cs:$A.cells} (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): int =
  _answer($Z.inflate_stored_cells_arena_proved(size, $A.Arena4MiB() | compressed, n, 4194304))
