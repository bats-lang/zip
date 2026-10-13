(* zip -- ZIP central directory parser *)
(* Finds an archive's entries by reading only the ranges each step names.
   Pure computation. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   Types
   ============================================================ *)

(* Ranged reading: an archive of z bytes need not be in memory at once.
   find_cd reads its end (the last t bytes), find_ref its central
   directory, find_data an entry's local header; each result names the
   next range to read, proven inside the archive.

   The results are linear: a datatype's cell is never freed (there is no
   GC), so each is consumed by a ~ pattern (zip_cd_mk, zip_ref_mk,
   zip_span_mk) when its caller is done with it. *)

(* How an entry's data is stored, decoded once from its method field:
   method 0 stores it as it is, method 8 deflates it (raw deflate). An
   entry with any other method is left out, so no entry here has one. *)
#pub datatype compression =
  | Stored
  | Deflated

(* The central directory of a z-byte archive: [c, c + s), inside it,
   holding d entries *)
#pub datavtype zip_cd(z:int, s:int) =
  | {c:nat | c + s <= z}{d:nat | d < 65536} zip_cd_mk(z, s) of (int c, int s, int d)

(* An entry of a z-byte archive, from its central directory: its local
   header at h, its compressed size s, its compression,
   uncompressed size u, and its name [no, no + nl) in the archive (in the
   central directory; a name is 1 to 65535 bytes, the length of the name
   find_ref was given) *)
#pub datavtype zip_ref(z:int) =
  | {h:nat | h + 30 <= z}{s:nat}{u:nat}{no:nat}{nl:pos | no + nl <= z; nl < 65536}
    zip_ref_mk(z) of (int h, int s, compression, int u, int no, int nl)

(* An entry's compressed data [d, d + s) inside a z-byte archive, its
   compression and its uncompressed size *)
#pub datavtype zip_span(z:int) =
  | {d,s:nat | d + s <= z}{u:nat}
    zip_span_mk(z) of (int d, int s, compression, int u)

(* The entries of the s-byte central directory of a z-byte archive,
   each record checked once, by cd_refs: an entry's local header at h,
   its compressed size cs, compression, uncompressed size u, and its name
   [no, no + nl) in the directory; k entries *)
#pub datavtype zip_refs(z:int, s:int, k:int) =
  | zip_refs_nil(z, s, 0) of ()
  | {k:nat}{h:nat | h + 30 <= z}{cs:nat}{u:nat}{no:nat}{nl:pos | no + nl <= s; nl < 65536}
    zip_refs_cons(z, s, k + 1) of (int h, int cs, compression, int u, int no, int nl, zip_refs(z, s, k))

(* The most bytes at an archive's end that its end-of-central-directory
   record (22 bytes and a comment of at most 65535) spans, and, before
   it, a ZIP64 end of central directory locator (20 bytes) and the
   ZIP64 record it names (56 bytes, with no extensible data) *)
#pub stadef ZIP_TAIL_MAX = 65633

(* ============================================================
   Public API
   ============================================================ *)

(* The central directory of a z-byte archive whose last t bytes are tail
   (read from offset z - t; t = min(z, ZIP_TAIL_MAX) finds any record),
   or none when tail holds no end-of-central-directory record or the
   directory it names is empty or outside the archive.

   An archive in ZIP64 form (APPNOTE 4.3.14 and 4.3.15) is read: when the
   end record's entry count is 0xFFFF or its directory size or offset
   0xFFFFFFFF, and the 20 bytes before it are a ZIP64 locator, the
   ZIP64 end record the locator names (inside tail) gives the real
   values, as libzip and Python's zipfile read them. A ZIP64 record
   whose values are 2^32 or more, which has 65536 entries or more, or
   lies outside tail, names no directory (none). *)
#pub fun find_cd
  {l:agz}{t:pos}{z:int | t <= z}
  (tail: !$A.arr(byte, l, t), t: int t, z: int z): $R.option([s:pos] zip_cd(z, s))

(* The directory's size *)
#pub fun cd_size {z,s:int} (dir: !zip_cd(z, s)): int s

(* The directory's offset *)
#pub fun cd_offset {z,s:int} (dir: !zip_cd(z, s)): [c:nat | c + s <= z] int c

(* The entry named name in the central directory cd (read from the
   directory's offset), or none when there is none or its local header
   is outside the archive or its method is neither 0 (stored) nor 8
   (deflated) *)
#pub fun find_ref
  {l:agz}{z:int}{s:pos}{lb:agz}{nb:pos}
  (cd: !$A.arr(byte, l, s), dir: !zip_cd(z, s), z: int z,
   name: !$A.borrow(byte, lb, nb), name_len: int nb): $R.option(zip_ref(z))

(* Where the entry's local header is *)
#pub fun ref_header {z:int} (r: !zip_ref(z)): [h:nat | h + 30 <= z] int h

(* The entry's compressed data, given hdr, its 30-byte local header (read
   from the ref's h), or none when hdr is not a local header or the data
   is outside the archive *)
#pub fun find_data
  {l:agz}{z:int}
  (hdr: !$A.arr(byte, l, 30), r: !zip_ref(z), z: int z): $R.option(zip_span(z))

(* Every entry of the central directory cd (read from the directory's
   offset), in order, or none when a record is not an entry record or
   runs past the directory. An entry that find_ref could never return
   (an empty name, a local header outside the archive, a method neither
   0 nor 8, a negative size) is left out. An entry whose sizes or offset
   are 0xFFFFFFFF has the real ones in its ZIP64 extra field (id 1,
   APPNOTE 4.5.3); a value of 2^31 or more is left out as a negative
   one is. *)
#pub fun cd_refs
  {l:agz}{z:int}{s:pos}
  (cd: !$A.arr(byte, l, s), dir: !zip_cd(z, s), z: int z): $R.option([k:nat] zip_refs(z, s, k))

#pub fun zip_refs_free {z,s:int}{k:nat} (rs: zip_refs(z, s, k)): void

(* Whether the name [no, no + nl) in cd is name *)
#pub fun cd_name_eq
  {l:agz}{s:pos}{no:nat}{nl:pos | no + nl <= s}{lb:agz}{nb:pos}
  (cd: !$A.arr(byte, l, s), no: int no, nl: int nl,
   name: !$A.borrow(byte, lb, nb), nb: int nb): bool

(* find_data for the entry whose local header is at h, of compressed
   size cs, compression method and uncompressed size u (a zip_refs
   entry's) *)
#pub fun find_data_at
  {l:agz}{z:int}{h:nat | h + 30 <= z}{cs:nat}{u:nat}
  (hdr: !$A.arr(byte, l, 30), h: int h, cs: int cs, method: compression, u: int u, z: int z): $R.option(zip_span(z))

(* ============================================================
   Internal byte reading
   ============================================================ *)

(* Little-endian reads at a proven offset. *)
fn _u8 {l:agz}{n:pos}{o:nat | o < n}
  (arr: !$A.arr(byte, l, n), off: int o): [v:nat | v < 256] int v =
  $AR.low_byte(byte2int0($A.get<byte>(arr, off)))

fn _u16 {l:agz}{n:pos}{o:nat | o + 2 <= n}
  (arr: !$A.arr(byte, l, n), off: int o): [v:nat | v < 65536] int v =
  _u8(arr, off) + 256 * _u8(arr, off + 1)

(* The 32-bit field as a signed int (two's complement), computed without
   overflow: the high byte contributes b3 - 256 when its top bit is set.
   An offset or size is at most the archive's size, so one whose top bit
   is set (negative here) is out of range. *)
fn _u32 {l:agz}{n:pos}{o:nat | o + 4 <= n}
  (arr: !$A.arr(byte, l, n), off: int o): [v:int] int v = let
  val lo = _u8(arr, off) + 256 * _u8(arr, off + 1) + 65536 * _u8(arr, off + 2)
  val b3 = _u8(arr, off + 3)
  val hi = (if b3 < 128 then b3 else b3 - 256): [h:int | ~128 <= h; h < 128] int h
in lo + 16777216 * hi end

(* The compression a method field names, or none for a method this
   reader does not take: the one place the field's numbers are read *)
fn _compression_of (method: int): $R.option(compression) =
  if method = 0 then $R.some(Stored())
  else if method = 8 then $R.some(Deflated())
  else $R.none()


(* The 64-bit little endian number at o of arr, when o + 8 <= limit <= n
   and its high half is 0 and its low half is at most 2^31 - 1; else -1 *)
fn _u64 {l:agz}{n:pos}{o,limit:int} (arr: !$A.arr(byte, l, n), n: int n, o: int o, limit: int limit): [v:int] int v =
  if o < 0 then ~1
  else if o + 8 > limit then ~1
  else if o + 8 > n then ~1
  else let
    val low = _u32(arr, o)
    val high = _u32(arr, o + 4)
  in
    if high <> 0 then ~1
    else if low < 0 then ~1
    else low
  end

(* The data [start, limit) of the ZIP64 extended information extra field
   (id 1) in arr[p, u), as its start and end, or -1 and -1 when there is
   none or a field runs past u *)
fun _extra_zip64 {l:agz}{n:pos}{u:nat | u <= n}{p:nat | p <= u} .<u - p>.
  (arr: !$A.arr(byte, l, n), n: int n, p: int p, u: int u): [a,b:int] @(int a, int b) =
  if p + 4 > u then @(~1, ~1)
  else let
    val id = _u16(arr, p)
    val size = _u16(arr, p + 2)
    val next = p + 4 + size
  in
    if next > u then @(~1, ~1)
    else if id = 1 then @(p + 4, next)
    else _extra_zip64(arr, n, next, u)
  end

(* An entry record at c of the s-byte directory cd (its 46 bytes inside
   it): its uncompressed size, compressed size and local header's offset.
   A field of 0xFFFFFFFF (-1 here) is the next 8 bytes of the record's
   ZIP64 extra field, in that order, present for the saturated fields
   only (APPNOTE 4.5.3); -1 when it is not there or does not fit. *)
fn _entry_fields64 {l:agz}{s:pos}{c:nat | c + 46 <= s}{u0,cs0,h0:int}
  (cd: !$A.arr(byte, l, s), s: int s, c: int c, u0: int u0, cs0: int cs0, h0: int h0): [u,cs,h:int] @(int u, int cs, int h) = let
  val extra_start = c + 46 + _u16(cd, c + 28)
  val extra_end = extra_start + _u16(cd, c + 30)
  val @(start, limit) = (if extra_end > s then @(~1, ~1) else _extra_zip64(cd, s, extra_start, extra_end)): [a,b:int] @(int a, int b)
  val u1 = (if u0 = ~1 then _u64(cd, s, start, limit) else u0): [v:int] int v
  val after_u = (if u0 = ~1 then start + 8 else start): [a:int] int a
  val cs1 = (if cs0 = ~1 then _u64(cd, s, after_u, limit) else cs0): [v:int] int v
  val after_cs = (if cs0 = ~1 then after_u + 8 else after_u): [a:int] int a
  val h1 = (if h0 = ~1 then _u64(cd, s, after_cs, limit) else h0): [v:int] int v
in @(u1, cs1, h1) end

fn _entry_fields {l:agz}{s:pos}{c:nat | c + 46 <= s}
  (cd: !$A.arr(byte, l, s), s: int s, c: int c): [u,cs,h:int] @(int u, int cs, int h) = let
  val u0 = _u32(cd, c + 24)
  val cs0 = _u32(cd, c + 20)
  val h0 = _u32(cd, c + 42)
in
  if u0 = ~1 then _entry_fields64(cd, s, c, u0, cs0, h0)
  else if cs0 = ~1 then _entry_fields64(cd, s, c, u0, cs0, h0)
  else if h0 = ~1 then _entry_fields64(cd, s, c, u0, cs0, h0)
  else @(u0, cs0, h0)
end

(* ============================================================
   Internal: compare array region with borrow
   ============================================================ *)

(* data[off + k] = name[k] for every k < nb; off + nb <= n is proven. *)
fn _name_eq
  {l:agz}{n:pos}{lb:agz}{nb:pos}{o:nat | o + nb <= n}
  (data: !$A.arr(byte, l, n), off: int o,
   name: !$A.borrow(byte, lb, nb), nb: int nb): bool = let
  fun loop {k:nat | k <= nb} .<nb - k>.
    (data: !$A.arr(byte, l, n), name: !$A.borrow(byte, lb, nb), k: int k): bool =
    if k >= nb then true
    else if byte2int0($A.get<byte>(data, off + k)) = byte2int0($A.read<byte>(name, k)) then loop(data, name, k + 1)
    else false
in loop(data, name, 0) end

(* ============================================================
   Implementations
   ============================================================ *)

(* The directory the classic end record's fields name *)
fn _classic {z:int}{d:nat | d < 65536}{s,c:int} (z: int z, d: int d, s: int s, c: int c): $R.option([size:pos] zip_cd(z, size)) =
  if c < 0 then $R.none()
  else if s <= 0 then $R.none()
  else if c > z - s then $R.none()
  else $R.some(zip_cd_mk(c, s, d))

(* The central directory a ZIP64 end of central directory record gives, for
   the end record at e of tail[0, t) (the ZIP64 locator is the 20 bytes
   before it, the record is where the locator says, inside tail) *)
fn _find_cd64 {l:agz}{t:pos}{z:int | t <= z}{e:nat | e + 22 <= t}
  (tail: !$A.arr(byte, l, t), t: int t, z: int z, e: int e): $R.option([s:pos] zip_cd(z, s)) =
  if e < 20 then $R.none()
  else if _u32(tail, e - 20) <> 117853008 then $R.none()
  else let
    val record_at = _u64(tail, t, e - 12, e)
    val q = record_at - (z - t)
  in
    if record_at < 0 then $R.none()
    else if q < 0 then $R.none()
    else if q + 56 > e - 20 then $R.none()
    else if _u32(tail, q) <> 101075792 then $R.none()
    else let
      val d = _u64(tail, t, q + 32, q + 56)
      val s = _u64(tail, t, q + 40, q + 56)
      val c = _u64(tail, t, q + 48, q + 56)
    in
      if d < 0 then $R.none()
      else if d >= 65536 then $R.none()
      else if c < 0 then $R.none()
      else if s <= 0 then $R.none()
      else if c > z - s then $R.none()
      else $R.some(zip_cd_mk(c, s, d))
    end
  end

implement find_cd {l}{t}{z} (tail, t, z) = let
  (* Scan backwards from the last position a record fits *)
  fun loop {i:int | i >= ~1; i + 22 <= t} .<i + 1>.
    (tail: !$A.arr(byte, l, t), i: int i): $R.option([s:pos] zip_cd(z, s)) =
    if i < 0 then $R.none()
    else if _u32(tail, i) = 101010256 then let
      val d = _u16(tail, i + 10)
      val s = _u32(tail, i + 12)
      val c = _u32(tail, i + 16)
    in
      (* a field at its maximum may be the real value, or may say that the
         ZIP64 record has it: the locator before the end record tells *)
      if d = 65535 || s = ~1 || c = ~1 then
        (if i >= 20 then
           (if _u32(tail, i - 20) = 117853008 then _find_cd64(tail, t, z, i)
            else _classic(z, d, s, c))
         else _classic(z, d, s, c))
      else _classic(z, d, s, c)
    end
    else loop(tail, i - 1)
in
  if t < 22 then $R.none() else loop(tail, t - 22)
end

implement cd_size {z,s} (dir) = let
  val+ @zip_cd_mk(_, n, _) = dir
  val n1 = n
  prval () = fold@(dir)
in n1 end

implement cd_offset {z,s} (dir) = let
  val+ @zip_cd_mk(c, _, _) = dir
  val c1 = c
  prval () = fold@(dir)
in c1 end

implement find_ref {l}{z}{s}{lb}{nb} (cd, dir, z, name, name_len) = let
  (* Entry record at c, with r entries left in the directory *)
  fun loop {co:nat | co + s <= z}{c:nat | c <= s}{r:nat} .<r>.
    (cd: !$A.arr(byte, l, s), s: int s, co: int co, c: int c, r: int r,
     name: !$A.borrow(byte, lb, nb)): $R.option(zip_ref(z)) =
    if r <= 0 then $R.none()
    else if c + 46 > s then $R.none()
    else if _u32(cd, c) <> 33639248 then $R.none()
    else let
      val nl = _u16(cd, c + 28)
      val next = c + 46 + nl + _u16(cd, c + 30) + _u16(cd, c + 32)
    in
      if c + 46 + nl > s then $R.none()
      else if nl <> name_len then
        (if next > s then $R.none() else loop(cd, s, co, next, r - 1, name))
      else if _name_eq(cd, c + 46, name, name_len) then let
        val @(u, cs, h) = _entry_fields(cd, s, c)
        val method = _compression_of(_u16(cd, c + 10))
      in
        case+ method of
        | ~$R.none() => $R.none()
        | ~$R.some(method) =>
          if h < 0 then $R.none()
          else if cs < 0 then $R.none()
          else if u < 0 then $R.none()
          else if h > z - 30 then $R.none()
          else $R.some(zip_ref_mk(h, cs, method, u, co + c + 46, nl))
      end
      else if next > s then $R.none()
      else loop(cd, s, co, next, r - 1, name)
    end
  val+ @zip_cd_mk(co, s, d) = dir
  val co1 = co and s1 = s and d1 = d
  prval () = fold@(dir)
in loop(cd, s1, co1, 0, d1, name) end

implement ref_header {z} (r) = let
  val+ @zip_ref_mk(h, _, _, _, _, _) = r
  val h1 = h
  prval () = fold@(r)
in h1 end

implement find_data_at {l}{z}{h}{cs}{u} (hdr, h, cs, method, u, z) =
  if _u32(hdr, 0) <> 67324752 then $R.none()
  else let
    val d = h + 30 + _u16(hdr, 26) + _u16(hdr, 28)
  in
    if d > z - cs then $R.none()
    else $R.some(zip_span_mk(d, cs, method, u))
  end

implement find_data {l}{z} (hdr, r, z) = let
  val+ @zip_ref_mk(h0, cs0, method0, u0, _, _) = r
  val h = h0 and cs = cs0 and method = method0 and u = u0
  prval () = fold@(r)
in find_data_at(hdr, h, cs, method, u, z) end

implement cd_refs {l}{z}{s} (cd, dir, z) = let
  (* rs reversed onto acc *)
  fun rev {k,a:nat} .<k>.
    (rs: zip_refs(z, s, k), acc: zip_refs(z, s, a)): zip_refs(z, s, k + a) =
    case+ rs of
    | ~zip_refs_nil() => acc
    | ~zip_refs_cons(h, cs, m, u, no, nl, rest) => rev(rest, zip_refs_cons(h, cs, m, u, no, nl, acc))
  (* The entries from the record at c, with r records left, onto acc
     (newest first) *)
  fun loop {c:nat | c <= s}{r:nat}{a:nat} .<r>.
    (cd: !$A.arr(byte, l, s), s: int s, c: int c, r: int r, acc: zip_refs(z, s, a))
    : $R.option([k:nat] zip_refs(z, s, k)) =
    if r <= 0 then $R.some(rev(acc, zip_refs_nil()))
    else if c + 46 > s then let val () = zip_refs_free(acc) in $R.none() end
    else if _u32(cd, c) <> 33639248 then let val () = zip_refs_free(acc) in $R.none() end
    else let
      val nl = _u16(cd, c + 28)
      val next = c + 46 + nl + _u16(cd, c + 30) + _u16(cd, c + 32)
    in
      if next > s then let val () = zip_refs_free(acc) in $R.none() end
      else let
        val @(u, cs, h) = _entry_fields(cd, s, c)
        val method = _compression_of(_u16(cd, c + 10))
      in
        case+ method of
        | ~$R.none() => loop(cd, s, next, r - 1, acc)
        | ~$R.some(method) =>
          if nl <= 0 then loop(cd, s, next, r - 1, acc)
          else if h < 0 then loop(cd, s, next, r - 1, acc)
          else if cs < 0 then loop(cd, s, next, r - 1, acc)
          else if u < 0 then loop(cd, s, next, r - 1, acc)
          else if h > z - 30 then loop(cd, s, next, r - 1, acc)
          else loop(cd, s, next, r - 1, zip_refs_cons(h, cs, method, u, c + 46, nl, acc))
      end
    end
  val+ @zip_cd_mk(_, s, d) = dir
  val s1 = s and d1 = d
  prval () = fold@(dir)
in loop(cd, s1, 0, d1, zip_refs_nil()) end

implement zip_refs_free {z,s}{k} (rs) = let
  fun free {k:nat} .<k>. (rs: zip_refs(z, s, k)): void =
    case+ rs of
    | ~zip_refs_nil() => ()
    | ~zip_refs_cons(_, _, _, _, _, _, rest) => free(rest)
in free(rs) end

implement cd_name_eq {l}{s}{no}{nl}{lb}{nb} (cd, no, nl, name, nb) =
  if nl <> nb then false else _name_eq(cd, no, name, nb)
