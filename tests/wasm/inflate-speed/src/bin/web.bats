#target wasm binary
#include "share/atspre_staload.hats"
#use array as A
#use sha256 as H
#use zip as Z

(* The speed of inflate_cells_proved in wasm (keyword: inflate-speed; tests/wasm/inflate-speed/run.mjs). This package is
   unsafe only to take the stream's bytes from the host through the module's memory and to hand the digest back: the
   host asks for room (bats_inflate_prepare), writes the compressed bytes there, and calls bats_inflate_run, the call
   it times. It is never published. *)

$UNSAFE begin
%{
static void *kept_stream = 0;
static void *kept_digest = 0;
static void kept_stream_set(void *p) { kept_stream = p; }
static void *kept_stream_get(void) { return kept_stream; }
static void kept_digest_set(void *p) { kept_digest = p; }
static void *kept_digest_get(void) { return kept_digest; }
%}
extern fun kept_stream_set (p: ptr): void = "mac#kept_stream_set"
extern fun kept_stream_get (): ptr = "mac#kept_stream_get"
extern fun kept_digest_set (p: ptr): void = "mac#kept_digest_set"
extern fun kept_digest_get (): ptr = "mac#kept_digest_get"
end

(* room for n bytes of the compressed stream: its address in the module's memory, for the host to write *)
#pub fun inflate_prepare {n:pos | n <= 1048576} (n: int n): ptr = "ext#bats_inflate_prepare"

(* inflate the n bytes the host wrote: the size of the output, minus one when the stream is refused as malformed, minus two
   when it does not fit; the sha256 of the output is at bats_inflate_digest *)
#pub fun inflate_run {n:pos | n <= 1048576} (n: int n): int = "ext#bats_inflate_run"

(* the 64 hex digits of the last output's sha256 *)
#pub fun inflate_digest (): ptr = "ext#bats_inflate_digest"

$UNSAFE begin

implement inflate_prepare {n} (n) = let
  val a = $A.alloc<byte>(n)
  val p = $UNSAFE.castvwtp0{ptr}(a)
  val () = kept_stream_set(p)
in p end

fn finish_answer {c:$A.cells}{ld:agz} (answer: $Z.inflated_cells(c), digest: !$A.arr(byte, ld, 64)): int =
  case+ answer of
  | ~$Z.inflated_cells_done(_, _ | out, size) => let
      val a = $A.barr_to_arr(out)
      val () = $H.hash(a, size, digest)
      val () = $A.free<byte>(a)
    in size end
  | ~$Z.inflated_cells_empty(_ | ) => 0
  | ~$Z.inflated_cells_malformed() => ~1
  | ~$Z.inflated_cells_too_large() => ~2

implement inflate_run {n} (n) = let
  val stream = $UNSAFE.castvwtp0{[l:agz] $A.arr(byte, l, n)}(kept_stream_get())
  val (size_pf | barr) = $A.barr_of_arr(stream)
  val @(fz, b) = $A.barr_freeze(barr)
  val answer = $Z.inflate_cells_proved(size_pf | b, n)
  val () = $A.cborrow_drop(fz, b)
  val () = $A.free<byte>($A.barr_to_arr($A.barr_thaw(fz)))
  val digest = $A.alloc<byte>(64)
  val digest_ptr = $UNSAFE.castvwtp1{ptr}(digest)
  val () = kept_digest_set(digest_ptr)
  val size = finish_answer(answer, digest)
  val _ = $UNSAFE.castvwtp0{ptr}(digest)
in size end

end

implement inflate_digest () = kept_digest_get()

implement main0 () = ()
