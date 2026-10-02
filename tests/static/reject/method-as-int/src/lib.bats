#include "share/atspre_staload.hats"
#use array as A
#use result as R
#use zip as Z

(* An entry's compression is a choice, not a method number *)
fn _data_of_method_8 {l:agz} (hdr: !$A.arr(byte, l, 30)): void =
  case+ $Z.find_data_at(hdr, 0, 0, 8, 0, 30) of
  | ~$R.some(~$Z.zip_span_mk(_, _, _, _)) => ()
  | ~$R.none() => ()
