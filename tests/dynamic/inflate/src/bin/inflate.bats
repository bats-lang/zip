#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
#use result as R
#use sha256 as H
#use str as S
#use zip as Z

(* The decoders against zlib (keyword: inflate-zlib). data/NN.deflate is a raw deflate stream made by zlib or by hand
   (generate.py); data/NN.expect is "s|o sha256 size": zlib's inflation of it, and whether every block is stored (the
   stored decoders take it) or not (they refuse it). Each stream goes through the four decoders (stored or full, reader
   and writer or in memory). refuse/NN.deflate are streams every decoder refuses; refuse/NN.expect is the fate of the
   reader for the stored and for the full decoder (c closed before its end, e ended). The number of streams is the
   generator's: a missing file fails. *)

#define DATA_COUNT 63
#define REFUSE_COUNT 13

fn fail (name: string, index: int, what: string): bool = let
  val () = println! ("FAIL ", name, " ", index, ": ", what)
in false end

(* ---- the paths, as frozen arrays ---- *)

datavtype held(int) =
  | {l:agz}{n:pos | n < 1048576} held_mk(n) of ($A.frozen(byte, l, n, 1), $A.borrow(byte, l, n), int n)

fn held_new {l:agz}{n:pos | n < 1048576} (a: $A.arr(byte, l, n), n: int n): held(n) = let
  val @(fz, b) = $A.freeze<byte>(a)
in held_mk(fz, b, n) end

fn held_free {n:pos} (h: held(n)): void = let
  val ~held_mk(fz, b, _) = h
  val () = $A.drop<byte>(fz, b)
in $A.free<byte>($A.thaw<byte>(fz)) end

fn digit (n: int): char = int2char0(48 + n)

fn data_stream_path (i: int): held(15) = let
  var p = @[char][15]('d', 'a', 't', 'a', '/', digit(i / 10), digit(i mod 10), '.', 'd', 'e', 'f', 'l', 'a', 't', 'e')
in held_new($S.from_char_array(p, 15), 15) end

fn data_expect_path (i: int): held(14) = let
  var p = @[char][14]('d', 'a', 't', 'a', '/', digit(i / 10), digit(i mod 10), '.', 'e', 'x', 'p', 'e', 'c', 't')
in held_new($S.from_char_array(p, 14), 14) end

fn refuse_stream_path (i: int): held(17) = let
  var p = @[char][17]('r', 'e', 'f', 'u', 's', 'e', '/', digit(i / 10), digit(i mod 10), '.', 'd', 'e', 'f', 'l', 'a', 't', 'e')
in held_new($S.from_char_array(p, 17), 17) end

fn refuse_expect_path (i: int): held(16) = let
  var p = @[char][16]('r', 'e', 'f', 'u', 's', 'e', '/', digit(i / 10), digit(i mod 10), '.', 'e', 'x', 'p', 'e', 'c', 't')
in held_new($S.from_char_array(p, 16), 16) end

fn out_path (): held(12) = let
  var p = @[char][12]('i', 'n', 'f', 'l', 'a', 't', 'e', 'd', '.', 'b', 'i', 'n')
in held_new($S.from_char_array(p, 12), 12) end

(* the size of the file, or minus one *)
fn held_size {n:pos} (h: !held(n)): [s:int] int s =
  case+ h of
  | @held_mk(fz, b, n) => let
      val r = (case+ $F.file_size(b, n) of ~$R.ok(s) => s | ~$R.err(_) => ~1)
    in fold@(h); r end

fn held_open {n:pos} (h: !held(n)): $R.result($F.fd, $F.io_error) =
  case+ h of
  | @held_mk(fz, b, n) => let
      val r = $F.file_open(b, n, $F.ReadOnly(), $F.OpenExisting(), 0)
    in fold@(h); r end

fn held_reader {n:pos}{s:nat} (h: !held(n), s: int s): $R.result($F.content_reader($A.cnil(), 0, s), $F.io_error) =
  case+ h of
  | @held_mk(fz, b, n) => let
      val r = $F.content_reader_open_range(b, n, 0, s)
    in fold@(h); r end

fn held_writer {n:pos} (h: !held(n)): $R.result($F.content_writer($A.cnil()), $F.io_error) =
  case+ h of
  | @held_mk(fz, b, n) => let
      val r = $F.content_create(b, n, 420)
    in fold@(h); r end

(* ---- a file in memory ---- *)

fun copy_bytes {ls:agz}{ns:pos}{ld:agz}{nd:pos}{j,m,at:nat | j <= m; m <= ns; at + m <= nd} .<m - j>.
  (src: !$A.arr(byte, ls, ns), dst: !$A.arr(byte, ld, nd), j: int j, m: int m, at: int at): void =
  if j >= m then ()
  else let
    val () = $A.set<byte>(dst, at + j, $A.get<byte>(src, j))
  in copy_bytes(src, dst, j + 1, m, at) end

fun load_chunks {ld:agz}{nd:pos}{lc:agz}{i:nat | i <= nd} .<nd - i>.
  (f: !$F.fd, dst: !$A.arr(byte, ld, nd), chunk: !$A.arr(byte, lc, 8192), nd: int nd, i: int i): bool =
  if i >= nd then true
  else (case+ $F.file_read(f, chunk, 8192) of
    | ~$R.err(_) => false
    | ~$R.ok(k) =>
      if k <= 0 then false
      else if i + k > nd then let
        val () = copy_bytes(chunk, dst, 0, nd - i, i)
      in load_chunks(f, dst, chunk, nd, nd) end
      else let
        val () = copy_bytes(chunk, dst, 0, k, i)
      in load_chunks(f, dst, chunk, nd, i + k) end)

datavtype blob =
  | blob_none
  | {l:agz}{n:pos | n <= 1048576} blob_some of ($A.arr(byte, l, n), int n)

fn blob_free (b: blob): void =
  case+ b of
  | ~blob_none() => ()
  | ~blob_some(a, _) => $A.free<byte>(a)

(* the whole file, at most a mebibyte; none when it is empty, longer or unreadable *)
fn load_file {n:pos} (h: !held(n)): blob = let
  val size = held_size(h)
in
  if size <= 0 then blob_none()
  else if size > 1048576 then blob_none()
  else (case+ held_open(h) of
    | ~$R.err(_) => blob_none()
    | ~$R.ok(f) => let
        val dst = $A.alloc<byte>(size)
        val chunk = $A.alloc<byte>(8192)
        val ok = load_chunks(f, dst, chunk, size, 0)
        val () = $A.free<byte>(chunk)
        val () = $R.discard<int><$F.io_error>($F.file_close(f))
      in
        if ok then blob_some(dst, size) else (let val () = $A.free<byte>(dst) in blob_none() end)
      end)
end

(* ---- sha256 of a file, of an array ---- *)

fun hash_chunks {lc:agz}{fuel:nat} .<fuel>. (f: !$F.fd, c: !$H.ctx, chunk: !$A.arr(byte, lc, 8192), fuel: int fuel): bool =
  if fuel <= 0 then false
  else (case+ $F.file_read(f, chunk, 8192) of
    | ~$R.err(_) => false
    | ~$R.ok(k) => if k <= 0 then true else let val () = $H.update(c, chunk, k) in hash_chunks(f, c, chunk, fuel - 1) end)

(* the 64 hex digits of the file's sha256, and whether it could be read *)
fn hash_file {n:pos}{lo:agz} (h: !held(n), out: !$A.arr(byte, lo, 64)): bool =
  case+ held_open(h) of
  | ~$R.err(_) => false
  | ~$R.ok(f) => let
      val c = $H.init()
      val chunk = $A.alloc<byte>(8192)
      val ok = hash_chunks(f, c, chunk, 1000000)
      val () = $A.free<byte>(chunk)
      val () = $R.discard<int><$F.io_error>($F.file_close(f))
      val () = $H.finish(c, out)
    in ok end

(* ---- the expectation ---- *)

fun digits_value {l:agz}{n:pos}{i:nat | i <= n} .<n - i>. (a: !$A.arr(byte, l, n), n: int n, i: int i, acc: int): int =
  if i >= n then acc
  else let
    val d = byte2int0($A.get<byte>(a, i)) - 48
  in
    if d < 0 then acc else if d > 9 then acc else if acc > 100000000 then acc else digits_value(a, n, i + 1, acc * 10 + d)
  end

fun hex_equal {l1:agz}{n1:pos}{l2:agz}{at,i:nat | i <= 64} .<64 - i>.
  (a: !$A.arr(byte, l1, n1), n1: int n1, at: int at, b: !$A.arr(byte, l2, 64), i: int i): bool =
  if i >= 64 then true
  else if at + i < n1 then (if byte2int0($A.get<byte>(a, at + i)) = byte2int0($A.get<byte>(b, i)) then hex_equal(a, n1, at, b, i + 1) else false)
  else false

(* whether the output of size size and hash digest (64 hex digits) is what the expectation file e says, as its n bytes *)
fn matches {le:agz}{ne:pos}{ld:agz} (e: !$A.arr(byte, le, ne), ne: int ne, digest: !$A.arr(byte, ld, 64), size: int): bool =
  if ne < 68 then false
  else hex_equal(e, ne, 2, digest, 0) && digits_value(e, ne, 67, 0) = size

fn expected_stored {le:agz}{ne:pos} (e: !$A.arr(byte, le, ne)): bool = byte2int0($A.get<byte>(e, 0)) = 115

(* ---- the fates, as numbers ---- *)

fn failure_code (f: $Z.inflate_failure): int =
  case+ f of
  | $Z.failure_malformed() => 0
  | $Z.failure_read() => 1
  | $Z.failure_write() => 2
  | $Z.failure_too_large() => 3

fn reader_code {start,size_in:nat} (r: $Z.reader_fate(start, size_in)): int =
  case+ r of
  | ~$Z.reader_ended(_ | ) => 101
  | ~$Z.reader_closed_early() => 99
  | ~$Z.reader_lost(_) => 108

fn writer_code (w: $Z.writer_fate): int =
  case+ w of
  | ~$Z.writer_held(_ | ) => 1
  | ~$Z.writer_lost(_) => 0

(* what the reader and writer form answered: 1 done with that size; 2 stopped, malformed, with the reader fate letter code
   and whether the writer's file was closed; 3 anything else *)
datavtype run_answer =
  | run_done of (int)
  | run_malformed of (int, int)
  | run_other of ()

fn answer_of {s:nat} (answer: $Z.inflated(0, s)): run_answer =
  case+ answer of
  | ~$Z.inflated_done(_, _, _, _, _ | size) => run_done(size)
  | ~$Z.inflated_decoded_unsaved(_, _ | _) => run_other()
  | ~$Z.inflated_stopped(failure, reader_fate, writer_fate) =>
    if failure_code(failure) = 0 then run_malformed(reader_code(reader_fate), writer_code(writer_fate))
    else let
      val _ = reader_code(reader_fate)
      val _ = writer_code(writer_fate)
    in run_other() end

fn run_stream {n:pos | n < 1048576}{s:int} (stored_only: bool, stream: !held(n), size_in: int s, out: !held(12)): run_answer =
  if size_in < 0 then run_other()
  else (case+ held_reader(stream, size_in) of
    | ~$R.err(_) => run_other()
    | ~$R.ok(reader) =>
      (case+ held_writer(out) of
       | ~$R.err(_) => (let val () = $F.content_reader_close(reader) in run_other() end)
       | ~$R.ok(writer) =>
         if stored_only then answer_of($Z.inflate_stored_proved(reader, writer, 0, size_in))
         else answer_of($Z.inflate_proved(reader, writer, 0, size_in))))

(* the in-memory form: 1 done with that size, the output hashed into digest; 2 malformed; 3 anything else *)
fn memory_answer {c:$A.cells}{lo:agz} (answer: $Z.inflated_cells(c), digest: !$A.arr(byte, lo, 64)): @(int, int) =
  case+ answer of
  | ~$Z.inflated_cells_done(_, _ | out, size) => let
      val a = $A.barr_to_arr(out)
      val () = $H.hash(a, size, digest)
      val () = $A.free<byte>(a)
    in @(1, size) end
  | ~$Z.inflated_cells_empty(_ | ) => let
      val () = $H.finish($H.init(), digest)
    in @(1, 0) end
  | ~$Z.inflated_cells_malformed() => @(2, 0)
  | ~$Z.inflated_cells_too_large() => @(3, 0)

fn memory_stream {l:agz}{n:pos | n <= 1048576}{lo:agz} (stored_only: bool, stream: $A.arr(byte, l, n), n: int n, digest: !$A.arr(byte, lo, 64)): @(int, int) = let
  val (size_pf | barr) = $A.barr_of_arr(stream)
  val @(fz, b) = $A.barr_freeze(barr)
  val result =
    (if stored_only then memory_answer($Z.inflate_stored_cells_proved(size_pf | b, n), digest)
     else memory_answer($Z.inflate_cells_proved(size_pf | b, n), digest))
  val () = $A.cborrow_drop(fz, b)
  val () = $A.free<byte>($A.barr_to_arr($A.barr_thaw(fz)))
in result end

(* ---- one stream through one decoder ---- *)

(* what the reader and writer form's answer is worth: the output hashed into digest and compared with the expectation e *)
fn files_verdict {le:agz}{ne:pos}{ld:agz}
  (name: string, index: int, take: bool, answer: run_answer, e: !$A.arr(byte, le, ne), ne: int ne, out: !held(12), digest: !$A.arr(byte, ld, 64)): bool =
  case+ answer of
  | ~run_done(size) =>
    if take then (if hash_file(out, digest) then (if matches(e, ne, digest, size) then true else fail(name, index, "files: the output is not zlib's")) else fail(name, index, "files: the output cannot be read"))
    else fail(name, index, "files: a stream the stored decoder cannot take was taken")
  | ~run_malformed(_, _) => (if take then fail(name, index, "files: refused") else true)
  | ~run_other() => fail(name, index, "files: another answer")

(* the reader and writer form on a stream of the data directory: whether it did what the expectation e says *)
fn check_files {n:pos | n < 1048576}{le:agz}{ne:pos}
  (name: string, index: int, stored_only: bool, stream: !held(n), e: !$A.arr(byte, le, ne), ne: int ne, out: !held(12)): bool = let
  val take = (if stored_only then expected_stored(e) else true)
  val digest = $A.alloc<byte>(64)
  val ok = files_verdict(name, index, take, run_stream(stored_only, stream, held_size(stream), out), e, ne, out, digest)
  val () = $A.free<byte>(digest)
in ok end

fn memory_verdict {le:agz}{ne:pos}{ld:agz}
  (name: string, index: int, take: bool, stored_only: bool, loaded: blob, e: !$A.arr(byte, le, ne), ne: int ne, digest: !$A.arr(byte, ld, 64)): bool =
  case+ loaded of
  | ~blob_none() => fail(name, index, "memory: the stream cannot be loaded")
  | ~blob_some(a, size_in) => let
      val @(code, size) = memory_stream(stored_only, a, size_in, digest)
    in
      if code = 1 then
        (if take then (if matches(e, ne, digest, size) then true else fail(name, index, "memory: the output is not zlib's")) else fail(name, index, "memory: a stream the stored decoder cannot take was taken"))
      else if code = 2 then (if take then fail(name, index, "memory: refused") else true)
      else fail(name, index, "memory: another answer")
    end

fn check_memory {n:pos | n < 1048576}{le:agz}{ne:pos}
  (name: string, index: int, stored_only: bool, stream: !held(n), e: !$A.arr(byte, le, ne), ne: int ne): bool = let
  val take = (if stored_only then expected_stored(e) else true)
  val digest = $A.alloc<byte>(64)
  val ok = memory_verdict(name, index, take, stored_only, load_file(stream), e, ne, digest)
  val () = $A.free<byte>(digest)
in ok end

(* the kind of the first block of the stream: 0 stored, 1 fixed, 2 dynamic, 3 reserved or unreadable *)
fn first_kind {n:pos | n < 1048576} (stream: !held(n)): int =
  case+ load_file(stream) of
  | ~blob_none() => 3
  | ~blob_some(a, _) => let
      val k = (byte2int0($A.get<byte>(a, 0)) / 2) mod 4
      val () = $A.free<byte>(a)
    in k end

(* a stream of the data directory through the four decoders: its first block kind, or minus one *)
fn data_case (i: int): int = let
  val stream = data_stream_path(i)
  val expect = data_expect_path(i)
  val out = out_path()
  val kind = first_kind(stream)
  val ok = (case+ load_file(expect) of
    | ~blob_none() => fail("data", i, "the expectation cannot be loaded")
    | ~blob_some(e, ne) => let
        val a = check_files("stored", i, true, stream, e, ne, out)
        val b = check_files("full", i, false, stream, e, ne, out)
        val c = check_memory("stored", i, true, stream, e, ne)
        val d = check_memory("full", i, false, stream, e, ne)
        val () = $A.free<byte>(e)
      in a && b && c && d end)
  val () = held_free(stream)
  val () = held_free(expect)
  val () = held_free(out)
in if ok then kind else ~1 end

(* ---- the streams every decoder refuses ---- *)

fn check_refused_files {n:pos | n < 1048576}{le:agz}{ne:pos}
  (index: int, stored_only: bool, stream: !held(n), e: !$A.arr(byte, le, ne), ne: int ne, out: !held(12)): bool =
  if ne < 2 then fail("refuse", index, "the expectation is short")
  else let
  val letter = (if stored_only then byte2int0($A.get<byte>(e, 0)) else byte2int0($A.get<byte>(e, 1)))
  val name = (if stored_only then "refuse stored" else "refuse full")
in
  case+ run_stream(stored_only, stream, held_size(stream), out) of
  | ~run_malformed(reader, writer) =>
    if reader != letter then fail(name, index, "the reader's fate is not the expected one")
    else if writer != 1 then fail(name, index, "the writer's file was not closed")
    else true
  | ~run_done(_) => fail(name, index, "taken")
  | ~run_other() => fail(name, index, "another answer than malformed")
end

fn refused_verdict {ld:agz} (name: string, index: int, stored_only: bool, loaded: blob, digest: !$A.arr(byte, ld, 64)): bool =
  case+ loaded of
  | ~blob_none() => true
  | ~blob_some(a, size_in) => let
      val @(code, _) = memory_stream(stored_only, a, size_in, digest)
    in if code = 2 then true else fail(name, index, "not refused as malformed") end

fn check_refused_memory {n:pos | n < 1048576} (index: int, stored_only: bool, stream: !held(n)): bool = let
  val name = (if stored_only then "refuse stored memory" else "refuse full memory")
  val digest = $A.alloc<byte>(64)
  val ok = refused_verdict(name, index, stored_only, load_file(stream), digest)
  val () = $A.free<byte>(digest)
in ok end

fn refuse_case (i: int): bool = let
  val stream = refuse_stream_path(i)
  val expect = refuse_expect_path(i)
  val out = out_path()
  val ok = (case+ load_file(expect) of
    | ~blob_none() => fail("refuse", i, "the expectation cannot be loaded")
    | ~blob_some(e, ne) => let
        val a = check_refused_files(i, true, stream, e, ne, out)
        val b = check_refused_files(i, false, stream, e, ne, out)
        val () = $A.free<byte>(e)
      in a && b && check_refused_memory(i, true, stream) && check_refused_memory(i, false, stream) end)
  val () = held_free(stream)
  val () = held_free(expect)
  val () = held_free(out)
in ok end

(* ---- all of them ---- *)

fun run_data {i,n:nat | i <= n} .<n - i>. (i: int i, n: int n, bad: int, stored: int, fixed: int, dynamic: int): @(int, int, int, int) =
  if i >= n then @(bad, stored, fixed, dynamic)
  else let
    val kind = data_case(i)
  in
    if kind = 0 then run_data(i + 1, n, bad, stored + 1, fixed, dynamic)
    else if kind = 1 then run_data(i + 1, n, bad, stored, fixed + 1, dynamic)
    else if kind = 2 then run_data(i + 1, n, bad, stored, fixed, dynamic + 1)
    else run_data(i + 1, n, bad + 1, stored, fixed, dynamic)
  end

fun run_refuse {i,n:nat | i <= n} .<n - i>. (i: int i, n: int n, bad: int): int =
  if i >= n then bad
  else run_refuse(i + 1, n, if refuse_case(i) then bad else bad + 1)

implement main0 () = let
  val @(bad, stored, fixed, dynamic) = run_data(0, DATA_COUNT, 0, 0, 0, 0)
  val refused_bad = run_refuse(0, REFUSE_COUNT, 0)
  val () = println! ("first blocks: ", stored, " stored, ", fixed, " fixed, ", dynamic, " dynamic")
in
  if bad = 0 && refused_bad = 0 && stored > 0 && fixed > 0 && dynamic > 0
  then println! ("inflate: all cases pass")
  else exit_void(1)
end
