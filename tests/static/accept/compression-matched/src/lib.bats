#include "share/atspre_staload.hats"
#use array as A
#use result as R
#use zip as Z

(* Each compression names its decoder *)
fn _decoder_name (method: $Z.compression): string =
  case+ method of
  | $Z.Stored() => "stored"
  | $Z.Deflated() => "raw deflate"

(* An entry of the directory carries its compression to find_data_at
   and on to its span *)
fn _span_compression {l:agz}{z:int}{s:int}{k:nat}
  (hdr: !$A.arr(byte, l, 30), refs: $Z.zip_refs(z, s, k), z: int z): string =
  case+ refs of
  | ~$Z.zip_refs_nil() => "none"
  | ~$Z.zip_refs_cons(h, cs, method, u, _, _, rest) => let
      val () = $Z.zip_refs_free(rest)
    in
      case+ $Z.find_data_at(hdr, h, cs, method, u, z) of
      | ~$R.some(~$Z.zip_span_mk(_, _, found, _)) => _decoder_name(found)
      | ~$R.none() => "none"
    end
