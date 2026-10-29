#include "share/atspre_staload.hats"
staload Z = "zip/src/lib.sats"

(* A match on an entry's compression that leaves deflated out *)
fn _decoder_name (method: $Z.compression): string =
  case+ method of
  | $Z.Stored() => "stored"

implement main0 () = ()
