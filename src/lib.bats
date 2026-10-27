(* zip -- ZIP central directory parser *)
(* Finds an archive's entries by reading only the ranges each step names.
   Pure computation. *)

#include "share/atspre_staload.hats"

#use array as A
#use file as F
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

(* ============================================================
   RFC 1951 as relations (quire#608, zip#64): bits, the canonical Huffman code, the alphabets
   ============================================================ *)

(* The rest of the relations (copies, symbols, the code length run, blocks, the window's
   lemmas, the decoders) need array#82 (APPEND, CELLS_EQ) and file#76 (the reader and the
   writer): their approved declarations are in design/rfc1951-declarations.txt, added to
   this file when those are published (zip#64). *)

(* Bit reading, RFC 1951 3.1.1. Bits are numbered from 0, the least
   significant bit of cell 0 first: bit p is bit (p mod 8) of cell (p div 8). *)

(* BYTE_BIT(byte, bit_index, bit): bit bit_index of the byte, by halving *)
#pub dataprop BYTE_BIT(int, int, int) =
  | {half:nat}{bit:nat | bit < 2} BYTE_BIT_here(2 * half + bit, 0, bit)
  | {half,bit_index:nat}{bit,low:nat | bit < 2; low < 2} BYTE_BIT_there(2 * half + low, bit_index + 1, bit) of BYTE_BIT(half, bit_index, bit)

(* BIT(source, p, bit): bit p of the cells *)
#pub dataprop BIT($A.cells, int, int) =
  | {source:$A.cells}{p,byte_index,bit_index,byte,bit:nat | bit_index < 8; p == 8 * byte_index + bit_index; bit < 2}
    BIT_mk(source, p, bit) of ($A.NTH(source, byte_index, byte), BYTE_BIT(byte, bit_index, bit))

(* BITS(source, p, width, value): the width bits from bit p, data elements
   packed least significant bit first (3.1.1), are the number value (at most
   16 bits, the most any element has, so value < 2 to the 16 and the 32-bit
   solver holds) *)
#pub dataprop BITS($A.cells, int, int, int) =
  | {source:$A.cells}{p:nat} BITS_nil(source, p, 0, 0)
  | {source:$A.cells}{p,width,value,bit:nat | width < 16; bit < 2}
    BITS_cons(source, p, width + 1, bit + 2 * value) of (BIT(source, p, bit), BITS(source, p + 1, width, value))

(* HBITS(source, p, width, code): the width bits from bit p, Huffman codes
   packed most significant bit first (3.1.1), are the code: each next bit is
   the code's new last bit *)
#pub dataprop HBITS($A.cells, int, int, int) =
  | {source:$A.cells}{p:nat} HBITS_nil(source, p, 0, 0)
  | {source:$A.cells}{p,width,code,bit:nat | width < 15; bit < 2}
    HBITS_snoc(source, p, width + 1, 2 * code + bit) of (HBITS(source, p, width, code), BIT(source, p + width, bit))

#pub prfun bit_functional {source:$A.cells}{p,first_bit,second_bit:nat} (BIT(source, p, first_bit), BIT(source, p, second_bit)): [first_bit == second_bit] void

#pub prfun bits_functional {source:$A.cells}{p,width,first_value,second_value:nat} (BITS(source, p, width, first_value), BITS(source, p, width, second_value)): [first_value == second_value] void

#pub prfun hbits_functional {source:$A.cells}{p,width,first_code,second_code:nat} (HBITS(source, p, width, first_code), HBITS(source, p, width, second_code)): [first_code == second_code] void

(* A bit of a byte has one value (keyword: bits) *)
prfun _byte_bit_functional {byte,bit_index,first_bit,second_bit:nat} .<bit_index>.
  (first: BYTE_BIT(byte, bit_index, first_bit), second: BYTE_BIT(byte, bit_index, second_bit)): [first_bit == second_bit] void =
  case+ first of
  | BYTE_BIT_here() => (case+ second of BYTE_BIT_here() => ())
  | BYTE_BIT_there(first_rest) =>
    (case+ second of BYTE_BIT_there(second_rest) => _byte_bit_functional(first_rest, second_rest))

prfun _bit_functional {source:$A.cells}{p,first_bit,second_bit:nat} .<>.
  (first: BIT(source, p, first_bit), second: BIT(source, p, second_bit)): [first_bit == second_bit] void =
  (case+ first of
   | BIT_mk(first_nth, first_byte_bit) =>
     (case+ second of
      | BIT_mk(second_nth, second_byte_bit) => let
          prval () = $A.nth_functional(first_nth, second_nth)
        in _byte_bit_functional(first_byte_bit, second_byte_bit) end))

primplement bit_functional {source}{p,first_bit,second_bit} (first, second) = _bit_functional(first, second)

prfun _bits_functional {source:$A.cells}{p,width,first_value,second_value:nat} .<width>.
  (first: BITS(source, p, width, first_value), second: BITS(source, p, width, second_value)): [first_value == second_value] void =
  case+ first of
  | BITS_nil() => (case+ second of BITS_nil() => ())
  | BITS_cons(first_bit, first_rest) =>
    (case+ second of
     | BITS_cons(second_bit, second_rest) => let
         prval () = bit_functional(first_bit, second_bit)
       in _bits_functional(first_rest, second_rest) end)

primplement bits_functional {source}{p,width,first_value,second_value} (first, second) = _bits_functional(first, second)

prfun _hbits_functional {source:$A.cells}{p,width,first_code,second_code:nat} .<width>.
  (first: HBITS(source, p, width, first_code), second: HBITS(source, p, width, second_code)): [first_code == second_code] void =
  case+ first of
  | HBITS_nil() => (case+ second of HBITS_nil() => ())
  | HBITS_snoc(first_rest, first_bit) =>
    (case+ second of
     | HBITS_snoc(second_rest, second_bit) => let
         prval () = bit_functional(first_bit, second_bit)
       in _hbits_functional(first_rest, second_rest) end)

primplement hbits_functional {source}{p,width,first_code,second_code} (first, second) = _hbits_functional(first, second)

(* Cells built from cells *)

(* SLICE(source, start, width, part): the width cells from cell start are part *)
#pub dataprop SLICE($A.cells, int, int, $A.cells) =
  | {source:$A.cells}{start:nat} SLICE_nil(source, start, 0, $A.cnil())
  | {source:$A.cells}{start,width:nat}{head:int}{rest:$A.cells}
    SLICE_cons(source, start, width + 1, $A.ccons(head, rest)) of ($A.NTH(source, start, head), SLICE(source, start + 1, width, rest))

(* RUN(count, value, rest, all): all is count cells value and then rest *)
#pub dataprop RUN(int, int, $A.cells, $A.cells) =
  | {value:int}{rest:$A.cells} RUN_zero(0, value, rest, rest)
  | {count:nat}{value:int}{rest,all:$A.cells} RUN_cons(count + 1, value, rest, $A.ccons(value, all)) of RUN(count, value, rest, all)

(* The canonical Huffman code, RFC 1951 3.2.2: lengths is the code length of
   each symbol (cell s is the length of symbol s, 0 for none). *)

(* COUNT_BEFORE(lengths, until, len, count): count of the first until lengths are len *)
#pub dataprop COUNT_BEFORE($A.cells, int, int, int) =
  | {lengths:$A.cells}{len:int} COUNT_BEFORE_zero(lengths, 0, len, 0)
  | {rest:$A.cells}{until,count:nat}{len:int} COUNT_BEFORE_hit($A.ccons(len, rest), until + 1, len, count + 1) of COUNT_BEFORE(rest, until, len, count)
  | {rest:$A.cells}{until,count:nat}{len,other:int | other != len} COUNT_BEFORE_miss($A.ccons(other, rest), until + 1, len, count) of COUNT_BEFORE(rest, until, len, count)

(* BL_COUNT(lengths, len, count): bl_count[len] of 3.2.2, count symbols have length len *)
#pub dataprop BL_COUNT($A.cells, int, int) =
  | {lengths:$A.cells}{symbols,len,count:nat | len >= 1} BL_COUNT_mk(lengths, len, count) of ($A.CLEN(lengths, symbols), COUNT_BEFORE(lengths, symbols, len, count))

(* NEXT_CODE(lengths, len, first_code): next_code[len] of 3.2.2, the first code of length len *)
#pub dataprop NEXT_CODE($A.cells, int, int) =
  | {lengths:$A.cells} NEXT_CODE_first(lengths, 1, 0)
  | {lengths:$A.cells}{len,first_code,count:nat | len >= 1}
    NEXT_CODE_next(lengths, len + 1, 2 * (first_code + count)) of (NEXT_CODE(lengths, len, first_code), BL_COUNT(lengths, len, count))

(* CODE(lengths, sym, code, len): symbol sym is assigned the code, of len
   bits (1 to 15): the first code of its length and one more for each
   earlier symbol of that length *)
#pub dataprop CODE($A.cells, int, int, int) =
  | {lengths:$A.cells}{sym,len,start,rank:nat | len >= 1; len <= 15}
    CODE_mk(lengths, sym, start + rank, len) of ($A.NTH(lengths, sym, len), NEXT_CODE(lengths, len, start), COUNT_BEFORE(lengths, sym, len, rank))

(* LEN_FIT(lengths, maxlen): the codes of length 1 to maxlen are not
   over-subscribed, next_code[len] + bl_count[len] <= 2 to the len for each *)
#pub dataprop LEN_FIT($A.cells, int) =
  | {lengths:$A.cells} LEN_FIT_zero(lengths, 0)
  | {lengths:$A.cells}{len,first_code,count,power:nat | first_code + count <= power}
    LEN_FIT_step(lengths, len + 1) of (LEN_FIT(lengths, len), NEXT_CODE(lengths, len + 1, first_code), BL_COUNT(lengths, len + 1, count), $AR.POW2(len + 1, power))

(* AT_MOST(lengths, maxlen): no length is over maxlen *)
#pub dataprop AT_MOST($A.cells, int) =
  | {maxlen:nat} AT_MOST_nil($A.cnil(), maxlen)
  | {rest:$A.cells}{maxlen,len:nat | len <= maxlen} AT_MOST_cons($A.ccons(len, rest), maxlen) of AT_MOST(rest, maxlen)

(* LENGTHS_FIT(lengths, maxlen): the lengths are all at most maxlen and
   not over-subscribed: the codes are prefix-free. The one hypothesis of
   decsym_functional, for the maxlen the code was checked to (15, or 7
   for the code length code) *)
#pub dataprop LENGTHS_FIT($A.cells, int) =
  | {lengths:$A.cells}{maxlen:nat} LENGTHS_FIT_mk(lengths, maxlen) of (AT_MOST(lengths, maxlen), LEN_FIT(lengths, maxlen))

(* The shapes of a code that 3.2.7 and zlib take: complete (every code of
   maxlen bits is used), a single code of one bit, or no code at all *)
#pub dataprop LENGTHS_FULL($A.cells, int) =
  | {lengths:$A.cells}{maxlen,first_code,count,power:nat | maxlen >= 1; first_code + count == power}
    LENGTHS_FULL_mk(lengths, maxlen) of (NEXT_CODE(lengths, maxlen, first_code), BL_COUNT(lengths, maxlen, count), $AR.POW2(maxlen, power))
#pub dataprop LENGTHS_SINGLE($A.cells) =
  | {lengths:$A.cells}{symbols:pos} LENGTHS_SINGLE_mk(lengths) of ($A.CLEN(lengths, symbols), COUNT_BEFORE(lengths, symbols, 0, symbols - 1), COUNT_BEFORE(lengths, symbols, 1, 1))
#pub dataprop LENGTHS_EMPTY($A.cells) =
  | {lengths:$A.cells}{symbols:nat} LENGTHS_EMPTY_mk(lengths) of ($A.CLEN(lengths, symbols), COUNT_BEFORE(lengths, symbols, 0, symbols))

(* The code of the literal/length alphabet and of the distance alphabet
   of a dynamic block: prefix-free, and complete or the single one-bit
   code; the distance code may also be empty (3.2.7) *)
#pub dataprop LITLEN_USABLE($A.cells) =
  | {lengths:$A.cells} LITLEN_USABLE_full(lengths) of (LENGTHS_FIT(lengths, 15), LENGTHS_FULL(lengths, 15))
  | {lengths:$A.cells} LITLEN_USABLE_single(lengths) of (LENGTHS_FIT(lengths, 15), LENGTHS_SINGLE(lengths))
#pub dataprop DIST_USABLE($A.cells) =
  | {lengths:$A.cells} DIST_USABLE_full(lengths) of (LENGTHS_FIT(lengths, 15), LENGTHS_FULL(lengths, 15))
  | {lengths:$A.cells} DIST_USABLE_single(lengths) of (LENGTHS_FIT(lengths, 15), LENGTHS_SINGLE(lengths))
  | {lengths:$A.cells} DIST_USABLE_empty(lengths) of (LENGTHS_FIT(lengths, 15), LENGTHS_EMPTY(lengths))

(* DECSYM(lengths, source, p, sym, used): the bits of source from bit p, in
   Huffman order, are the code of sym: sym is what they decode to, and
   used bits were read *)
#pub dataprop DECSYM($A.cells, $A.cells, int, int, int) =
  | {lengths,source:$A.cells}{p,sym,used,code:nat | used >= 1; used <= 15}
    DECSYM_mk(lengths, source, p, sym, used) of (HBITS(source, p, used, code), CODE(lengths, sym, code, used))

#pub prfun bl_count_functional {lengths:$A.cells}{len,first_count,second_count:nat} (BL_COUNT(lengths, len, first_count), BL_COUNT(lengths, len, second_count)): [first_count == second_count] void

#pub prfun next_code_functional {lengths:$A.cells}{len,first_code,second_code:nat} (NEXT_CODE(lengths, len, first_code), NEXT_CODE(lengths, len, second_code)): [first_code == second_code] void

#pub prfun code_functional {lengths:$A.cells}{sym,first_code,first_len,second_code,second_len:nat}
  (CODE(lengths, sym, first_code, first_len), CODE(lengths, sym, second_code, second_len)): [first_code == second_code; first_len == second_len] void
(* A bit sequence decodes to one symbol (the code is prefix-free) *)
#pub prfun decsym_functional {lengths,source:$A.cells}{maxlen,p,first_sym,first_used,second_sym,second_used:nat}
  (LENGTHS_FIT(lengths, maxlen), DECSYM(lengths, source, p, first_sym, first_used), DECSYM(lengths, source, p, second_sym, second_used)): [first_sym == second_sym; first_used == second_used] void

(* Proofs of the canonical code (keyword: huffman-code). The code of a symbol
   is its length's first code and the number of earlier symbols of that
   length; a code is a prefix of no longer code because each length's first
   code is twice the end of the one before (3.2.2). *)

prfun _clen_functional {cells:$A.cells}{first,second:nat} .<first>.
  (first_len: $A.CLEN(cells, first), second_len: $A.CLEN(cells, second)): [first == second] void =
  case+ first_len of
  | $A.CLEN_nil() => (case+ second_len of $A.CLEN_nil() => ())
  | $A.CLEN_cons(first_rest) => (case+ second_len of $A.CLEN_cons(second_rest) => _clen_functional(first_rest, second_rest))

prfun _count_before_functional {lengths:$A.cells}{until:nat}{len:int}{first_count,second_count:nat} .<until>.
  (first: COUNT_BEFORE(lengths, until, len, first_count), second: COUNT_BEFORE(lengths, until, len, second_count)): [first_count == second_count] void =
  case+ first of
  | COUNT_BEFORE_zero() => (case+ second of COUNT_BEFORE_zero() => ())
  | COUNT_BEFORE_hit(first_rest) =>
    (case+ second of
     | COUNT_BEFORE_hit(second_rest) => _count_before_functional(first_rest, second_rest)
     | COUNT_BEFORE_miss(_) => ())
  | COUNT_BEFORE_miss(first_rest) =>
    (case+ second of
     | COUNT_BEFORE_hit(_) => ()
     | COUNT_BEFORE_miss(second_rest) => _count_before_functional(first_rest, second_rest))

prfun _bl_count_functional {lengths:$A.cells}{len,first_count,second_count:nat} .<>.
  (first: BL_COUNT(lengths, len, first_count), second: BL_COUNT(lengths, len, second_count)): [first_count == second_count] void =
  (case+ first of
   | BL_COUNT_mk(first_len, first_before) =>
     (case+ second of
      | BL_COUNT_mk(second_len, second_before) => let
          prval () = _clen_functional(first_len, second_len)
        in _count_before_functional(first_before, second_before) end))

primplement bl_count_functional {lengths}{len,first_count,second_count} (first, second) = _bl_count_functional(first, second)

prfun _next_code_functional {lengths:$A.cells}{len,first_code,second_code:nat} .<len>.
  (first: NEXT_CODE(lengths, len, first_code), second: NEXT_CODE(lengths, len, second_code)): [first_code == second_code] void =
  case+ first of
  | NEXT_CODE_first() => (case+ second of NEXT_CODE_first() => () | NEXT_CODE_next(_, _) => ())
  | NEXT_CODE_next(first_rest, first_count) =>
    (case+ second of
     | NEXT_CODE_first() => ()
     | NEXT_CODE_next(second_rest, second_count) => let
         prval () = _next_code_functional(first_rest, second_rest)
         prval () = bl_count_functional(first_count, second_count)
       in () end)

primplement next_code_functional {lengths}{len,first_code,second_code} (first, second) = _next_code_functional(first, second)

primplement code_functional {lengths}{sym,first_code,first_len,second_code,second_len} (first, second) =
  (case+ first of
   | CODE_mk(first_nth, first_next, first_before) =>
     (case+ second of
      | CODE_mk(second_nth, second_next, second_before) => let
          prval () = $A.nth_functional(first_nth, second_nth)
          prval () = next_code_functional(first_next, second_next)
          prval () = _count_before_functional(first_before, second_before)
        in () end))

(* A symbol of length len has fewer earlier symbols of its length than a later point has *)
prfun _count_before_strict {lengths:$A.cells}{first_sym,second_sym:nat | first_sym < second_sym}{len:int}{first_rank,second_rank:nat} .<first_sym>.
  (found: $A.NTH(lengths, first_sym, len), first: COUNT_BEFORE(lengths, first_sym, len, first_rank), second: COUNT_BEFORE(lengths, second_sym, len, second_rank))
  : [first_rank < second_rank] void =
  case+ found of
  | $A.NTH_here() =>
    (case+ first of
     | COUNT_BEFORE_zero() =>
       (case+ second of
        | COUNT_BEFORE_hit(_) => ()
        | COUNT_BEFORE_miss(_) => ()))
  | $A.NTH_there(found_rest) =>
    (case+ first of
     | COUNT_BEFORE_hit(first_rest) =>
       (case+ second of
        | COUNT_BEFORE_hit(second_rest) => _count_before_strict(found_rest, first_rest, second_rest)
        | COUNT_BEFORE_miss(_) => ())
     | COUNT_BEFORE_miss(first_rest) =>
       (case+ second of
        | COUNT_BEFORE_hit(_) => ()
        | COUNT_BEFORE_miss(second_rest) => _count_before_strict(found_rest, first_rest, second_rest)))

(* The symbol's rank among the symbols of its length is below the length's count *)
prfun _rank_below_count {lengths:$A.cells}{sym:nat}{len:int}{rank,total:nat} .<>.
  (found: $A.NTH(lengths, sym, len), before: COUNT_BEFORE(lengths, sym, len, rank), count: BL_COUNT(lengths, len, total)): [rank < total] void =
  case+ count of
  | BL_COUNT_mk(count_len, count_before) => let
      prval () = $A.nth_in_len(found, count_len)
    in _count_before_strict(found, before, count_before) end

dataprop _LEN_AT(cells: $A.cells, len: int, first_code: int, count: int) =
  | {cells:$A.cells}{len,first_code,count:nat} _LEN_AT_mk(cells, len, first_code, count) of (NEXT_CODE(cells, len, first_code), BL_COUNT(cells, len, count))

prfun _len_fit_at {lengths:$A.cells}{maxlen,len:nat | 1 <= len; len <= maxlen} .<maxlen>.
  (fit: LEN_FIT(lengths, maxlen)): [first_code,count:nat] _LEN_AT(lengths, len, first_code, count) =
  case+ fit of
  | LEN_FIT_step(fit_rest, next_code, bl_count, _) =>
    sif len == maxlen then _LEN_AT_mk(next_code, bl_count) else _len_fit_at(fit_rest)

prfun _at_most_nth {lengths:$A.cells}{maxlen,index:nat}{value:int} .<index>.
  (at_most: AT_MOST(lengths, maxlen), found: $A.NTH(lengths, index, value)): [0 <= value; value <= maxlen] void =
  case+ found of
  | $A.NTH_here() => (case+ at_most of AT_MOST_cons(_) => ())
  | $A.NTH_there(found_rest) => (case+ at_most of AT_MOST_cons(at_most_rest) => _at_most_nth(at_most_rest, found_rest))

(* A code of the shorter length is greater than the first bits of any longer code's first code (3.2.2: next_code[len + 1] = 2 * (next_code[len] + bl_count[len])) *)
prfun _shorter_below {source,lengths:$A.cells}{p,short,long,short_code,long_value,short_first,short_count,long_first:nat | 1 <= short; short < long; short_code < short_first + short_count} .<long>.
  (short_bits: HBITS(source, p, short, short_code), long_bits: HBITS(source, p, long, long_value),
   short_next: NEXT_CODE(lengths, short, short_first), short_counted: BL_COUNT(lengths, short, short_count),
   long_next: NEXT_CODE(lengths, long, long_first)): [long_value < long_first] void =
  case+ long_bits of
  | HBITS_snoc(long_rest, _) =>
    (case+ long_next of
     | NEXT_CODE_next(next_rest, count_rest) =>
       sif long == short + 1 then let
         prval () = hbits_functional(short_bits, long_rest)
         prval () = next_code_functional(short_next, next_rest)
         prval () = bl_count_functional(short_counted, count_rest)
       in () end
       else let
         prval () = _shorter_below(short_bits, long_rest, short_next, short_counted, next_rest)
       in () end)

prfun _decsym_prefix {lengths,source:$A.cells}{maxlen,p,short_sym,short_used,long_sym,long_used:nat | short_used < long_used} .<>.
  (at_most: AT_MOST(lengths, maxlen), fit: LEN_FIT(lengths, maxlen), short: DECSYM(lengths, source, p, short_sym, short_used), long: DECSYM(lengths, source, p, long_sym, long_used)): [false] void =
  case+ short of
  | DECSYM_mk(short_bits, short_code) =>
    (case+ long of
     | DECSYM_mk(long_bits, long_code) =>
       (case+ short_code of
        | CODE_mk(short_found, short_next, short_before) =>
          (case+ long_code of
           | CODE_mk(long_found, long_next, long_before) => let
               prval () = _at_most_nth(at_most, short_found)
               prval _LEN_AT_mk(fit_next, fit_count) = _len_fit_at{lengths}{maxlen,short_used}(fit)
               prval () = _next_code_functional(short_next, fit_next)
               prval () = _rank_below_count(short_found, short_before, fit_count)
               prval () = _shorter_below(short_bits, long_bits, short_next, fit_count, long_next)
             in () end)))

primplement decsym_functional {lengths,source}{maxlen,p,first_sym,first_used,second_sym,second_used} (fit, first, second) =
  (case+ fit of
   | LENGTHS_FIT_mk(at_most, len_fit) =>
     sif first_used < second_used then let
       prval () = _decsym_prefix(at_most, len_fit, first, second)
     in () end
     else sif second_used < first_used then let
       prval () = _decsym_prefix(at_most, len_fit, second, first)
     in () end
     else
       (case+ first of
        | DECSYM_mk(first_bits, first_code) =>
          (case+ second of
           | DECSYM_mk(second_bits, second_code) =>
             (case+ first_code of
              | CODE_mk(first_found, first_next, first_before) =>
                (case+ second_code of
                 | CODE_mk(second_found, second_next, second_before) => let
                     prval () = hbits_functional(first_bits, second_bits)
                     prval () = next_code_functional(first_next, second_next)
                   in
                     sif first_sym < second_sym then let
                       prval () = _count_before_strict(first_found, first_before, second_before)
                     in () end
                     else sif second_sym < first_sym then let
                       prval () = _count_before_strict(second_found, second_before, first_before)
                     in () end
                     else ()
                   end)))))

(* The alphabets of the compressed data, RFC 1951 3.2.5 and 3.2.6 *)

(* What a literal/length symbol is *)
#pub datasort symbol_class =
  | symbol_literal of ()
  | symbol_end_of_block of ()
  | symbol_length of ()

#pub dataprop SYMBOL_CLASS(symbol_class, int) =
  | {sym:nat | sym <= 255} SYMBOL_CLASS_literal(symbol_literal(), sym)
  | SYMBOL_CLASS_end_of_block(symbol_end_of_block(), 256)
  | {sym:int | 257 <= sym; sym <= 285} SYMBOL_CLASS_length(symbol_length(), sym)

(* Symbol 284 with 31 extra bits would be the length 258, which RFC 1951 3.2.5
   gives to symbol 285 alone (zlib accepts it; SYMS_copy refuses it: only what
   the RFC allows has a constructor).
   LENGTH_SYMBOL(sym, extra_bits, base): length symbol sym (257 to 285) has
   extra_bits extra bits and its match lengths start at base (the table of
   3.2.5): symbols 257 to 264 have none; then four symbols for each extra
   bit count 1 to 5, whose bases are 4, 5, 6 and 7 times 2 to the extra
   bit count, plus 3; symbol 285 is the length 258 alone *)
#pub dataprop LENGTH_SYMBOL(int, int, int) =
  | {sym:int | 257 <= sym; sym <= 264} LENGTH_SYMBOL_short(sym, 0, sym - 254)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_base_4_times(261 + 4 * extra_bits, extra_bits, 4 * power + 3) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_base_5_times(262 + 4 * extra_bits, extra_bits, 5 * power + 3) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_base_6_times(263 + 4 * extra_bits, extra_bits, 6 * power + 3) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_base_7_times(264 + 4 * extra_bits, extra_bits, 7 * power + 3) of $AR.POW2(extra_bits, power)
  | LENGTH_SYMBOL_last(285, 0, 258)

(* DISTANCE_SYMBOL(sym, extra_bits, base): distance symbol sym (0 to 29),
   the table of 3.2.5: symbols 0 to 3 have no extra bits; then two symbols
   for each extra bit count 1 to 13, whose bases are 2 and 3 times 2 to the
   extra bit count, plus 1 *)
#pub dataprop DISTANCE_SYMBOL(int, int, int) =
  | {sym:nat | sym < 4} DISTANCE_SYMBOL_short(sym, 0, sym + 1)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 13} DISTANCE_SYMBOL_base_2_times(2 * extra_bits + 2, extra_bits, 2 * power + 1) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 13} DISTANCE_SYMBOL_base_3_times(2 * extra_bits + 3, extra_bits, 3 * power + 1) of $AR.POW2(extra_bits, power)

(* FIXED_LITLEN(lengths) and FIXED_DIST(lengths): the code lengths of the
   fixed Huffman codes (3.2.6): 144 of 8 bits, 112 of 9, 24 of 7 and 8 of 8;
   and 32 distance codes of 5 bits *)
#pub dataprop FIXED_LITLEN($A.cells) =
  | {lengths,after_144,after_112,after_24:$A.cells}
    FIXED_LITLEN_mk(lengths) of (RUN(144, 8, after_144, lengths), RUN(112, 9, after_112, after_144), RUN(24, 7, after_24, after_112), RUN(8, 8, $A.cnil(), after_24))
#pub dataprop FIXED_DIST($A.cells) =
  | {lengths:$A.cells} FIXED_DIST_mk(lengths) of RUN(32, 5, $A.cnil(), lengths)

(* The dynamic block's header, RFC 1951 3.2.7 *)

(* CL_ORDER(order): the order in which the code length code's lengths are
   stored: 16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15 *)
#pub dataprop CL_ORDER($A.cells) =
  | CL_ORDER_mk($A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil()))))))))))))))))))))

(* READ_LENGTHS3(source, p, count, values): count lengths of 3 bits each from bit p *)
#pub dataprop READ_LENGTHS3($A.cells, int, int, $A.cells) =
  | {source:$A.cells}{p:nat} READ_LENGTHS3_nil(source, p, 0, $A.cnil())
  | {source:$A.cells}{p,count,value:nat}{rest:$A.cells}
    READ_LENGTHS3_cons(source, p, count + 1, $A.ccons(value, rest)) of (BITS(source, p, 3, value), READ_LENGTHS3(source, p + 3, count, rest))

(* NOT_IN_PREFIX(order, count, sym): sym is none of the first count cells of order *)
#pub dataprop NOT_IN_PREFIX($A.cells, int, int) =
  | {order:$A.cells}{sym:int} NOT_IN_PREFIX_zero(order, 0, sym)
  | {order:$A.cells}{count:nat}{head,sym:int | head != sym} NOT_IN_PREFIX_cons($A.ccons(head, order), count + 1, sym) of NOT_IN_PREFIX(order, count, sym)

(* CODE_LENGTH_OF(order, sym, count, values, len): the code length code
   gives symbol sym the length len: the value stored for it among the
   count read (value i belongs to symbol order[i]), or 0 when none is stored *)
#pub dataprop CODE_LENGTH_OF($A.cells, int, int, $A.cells, int) =
  | {order,values:$A.cells}{sym,position,count,len:nat} CODE_LENGTH_OF_stored(order, sym, count, values, len) of ($A.NTH(order, position, sym), $A.NTH(values, position, len))
  | {order,values:$A.cells}{sym,count:nat} CODE_LENGTH_OF_absent(order, sym, count, values, 0) of NOT_IN_PREFIX(order, count, sym)

(* CODE_LENGTHS_FROM(order, count, values, first_sym, lengths): lengths is
   the code length code's lengths of the symbols first_sym to 18 *)
#pub dataprop CODE_LENGTHS_FROM($A.cells, int, $A.cells, int, $A.cells) =
  | {order,values:$A.cells}{count:nat} CODE_LENGTHS_FROM_end(order, count, values, 19, $A.cnil())
  | {order,values,rest:$A.cells}{count,first_sym,len:nat | first_sym < 19}
    CODE_LENGTHS_FROM_cons(order, count, values, first_sym, $A.ccons(len, rest)) of (CODE_LENGTH_OF(order, first_sym, count, values, len), CODE_LENGTHS_FROM(order, count, values, first_sym + 1, rest))

(* What a code length symbol is (3.2.7) *)
#pub datasort length_class =
  | length_literal of ()
  | length_repeat_previous of ()
  | length_zeros_short of ()
  | length_zeros_long of ()

#pub dataprop LENGTH_CLASS(length_class, int) =
  | {sym:nat | sym <= 15} LENGTH_CLASS_literal(length_literal(), sym)
  | LENGTH_CLASS_repeat_previous(length_repeat_previous(), 16)
  | LENGTH_CLASS_zeros_short(length_zeros_short(), 17)
  | LENGTH_CLASS_zeros_long(length_zeros_long(), 18)

(* CODE_LENGTHS_SIZED(code_length_code, source, p, so_far, total, lengths, end_bit, steps):
   the code lengths so far, decoded by the code length code from bit p, go on
   until there are total of them, lengths, ending at bit end_bit, in steps + 1
   decodes (the count is what a lemma's termination metric reads, as BLOCKS_SIZED);
   a repeat or run never goes past total, and the repeat of the previous length
   needs one (3.2.7) *)
#pub dataprop CODE_LENGTHS_SIZED($A.cells, $A.cells, int, $A.cells, int, $A.cells, int, int) =
  | {code_length_code,source:$A.cells}{p,total:nat}{so_far:$A.cells} CODE_LENGTHS_SIZED_done(code_length_code, source, p, so_far, total, so_far, p, 0) of $A.CLEN(so_far, total)
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,end_bit,steps:nat | so_far_count < total}{so_far,next,lengths:$A.cells}
    CODE_LENGTHS_SIZED_literal(code_length_code, source, p, so_far, total, lengths, end_bit, steps + 1)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_literal(), sym),
        $A.APPEND(so_far, $A.ccons(sym, $A.cnil()), next), CODE_LENGTHS_SIZED(code_length_code, source, p + used, next, total, lengths, end_bit, steps))
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit,previous,steps:nat | 1 <= so_far_count; so_far_count + 3 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
    CODE_LENGTHS_SIZED_repeat_previous(code_length_code, source, p, so_far, total, lengths, end_bit, steps + 1)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_repeat_previous(), sym),
        BITS(source, p + used, 2, extra_value), $A.NTH(so_far, so_far_count - 1, previous),
        RUN(3 + extra_value, previous, $A.cnil(), run), $A.APPEND(so_far, run, next), CODE_LENGTHS_SIZED(code_length_code, source, p + used + 2, next, total, lengths, end_bit, steps))
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit,steps:nat | so_far_count + 3 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
    CODE_LENGTHS_SIZED_zeros_short(code_length_code, source, p, so_far, total, lengths, end_bit, steps + 1)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_zeros_short(), sym),
        BITS(source, p + used, 3, extra_value),
        RUN(3 + extra_value, 0, $A.cnil(), run), $A.APPEND(so_far, run, next), CODE_LENGTHS_SIZED(code_length_code, source, p + used + 3, next, total, lengths, end_bit, steps))
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit,steps:nat | so_far_count + 11 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
    CODE_LENGTHS_SIZED_zeros_long(code_length_code, source, p, so_far, total, lengths, end_bit, steps + 1)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_zeros_long(), sym),
        BITS(source, p + used, 7, extra_value),
        RUN(11 + extra_value, 0, $A.cnil(), run), $A.APPEND(so_far, run, next), CODE_LENGTHS_SIZED(code_length_code, source, p + used + 7, next, total, lengths, end_bit, steps))

(* CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit): as
   CODE_LENGTHS_SIZED without the count; made by CODE_LENGTHS_done, _literal,
   _repeat_previous, _zeros_short and _zeros_long below. *)
#pub dataprop CODE_LENGTHS($A.cells, $A.cells, int, $A.cells, int, $A.cells, int) =
  | {code_length_code,source:$A.cells}{p,total:nat}{so_far,lengths:$A.cells}{end_bit,steps:nat}
    CODE_LENGTHS_made(code_length_code, source, p, so_far, total, lengths, end_bit) of CODE_LENGTHS_SIZED(code_length_code, source, p, so_far, total, lengths, end_bit, steps)

#pub prfun CODE_LENGTHS_done {code_length_code,source:$A.cells}{p,total:nat}{so_far:$A.cells}
  ($A.CLEN(so_far, total)): CODE_LENGTHS(code_length_code, source, p, so_far, total, so_far, p)

#pub prfun CODE_LENGTHS_literal {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,end_bit:nat | so_far_count < total}{so_far,next,lengths:$A.cells}
  ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_literal(), sym),
   $A.APPEND(so_far, $A.ccons(sym, $A.cnil()), next), CODE_LENGTHS(code_length_code, source, p + used, next, total, lengths, end_bit))
  : CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit)

#pub prfun CODE_LENGTHS_repeat_previous {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit,previous:nat | 1 <= so_far_count; so_far_count + 3 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
  ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_repeat_previous(), sym),
   BITS(source, p + used, 2, extra_value), $A.NTH(so_far, so_far_count - 1, previous),
   RUN(3 + extra_value, previous, $A.cnil(), run), $A.APPEND(so_far, run, next), CODE_LENGTHS(code_length_code, source, p + used + 2, next, total, lengths, end_bit))
  : CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit)

#pub prfun CODE_LENGTHS_zeros_short {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit:nat | so_far_count + 3 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
  ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_zeros_short(), sym),
   BITS(source, p + used, 3, extra_value),
   RUN(3 + extra_value, 0, $A.cnil(), run), $A.APPEND(so_far, run, next), CODE_LENGTHS(code_length_code, source, p + used + 3, next, total, lengths, end_bit))
  : CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit)

#pub prfun CODE_LENGTHS_zeros_long {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit:nat | so_far_count + 11 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
  ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_zeros_long(), sym),
   BITS(source, p + used, 7, extra_value),
   RUN(11 + extra_value, 0, $A.cnil(), run), $A.APPEND(so_far, run, next), CODE_LENGTHS(code_length_code, source, p + used + 7, next, total, lengths, end_bit))
  : CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit)

#pub prfun code_lengths_functional {code_length_code,source:$A.cells}{p,total:nat}{so_far,first,second:$A.cells}{first_end,second_end:nat}
  (LENGTHS_FIT(code_length_code, 7), CODE_LENGTHS(code_length_code, source, p, so_far, total, first, first_end), CODE_LENGTHS(code_length_code, source, p, so_far, total, second, second_end))
  : [first_end == second_end] $A.CELLS_EQ(first, second)

#pub prfun read_lengths3_functional {source:$A.cells}{p,count:nat}{first,second:$A.cells}
  (READ_LENGTHS3(source, p, count, first), READ_LENGTHS3(source, p, count, second)): $A.CELLS_EQ(first, second)

#pub prfun code_lengths_from_functional {order,values:$A.cells}{count,first_sym:nat | first_sym <= 19}{first,second:$A.cells}
  (CL_ORDER(order), $A.CLEN(values, count), CODE_LENGTHS_FROM(order, count, values, first_sym, first), CODE_LENGTHS_FROM(order, count, values, first_sym, second)): $A.CELLS_EQ(first, second)

(* Blocks, RFC 1951 3.2.3 *)

#pub datasort block_kind =
  | block_stored of ()
  | block_fixed of ()
  | block_dynamic of ()

(* BTYPE(kind, field): the two-bit field (3.2.3: 00, 01, 10; 11 is reserved
   and names no kind) *)
#pub dataprop BTYPE(block_kind, int) =
  | BTYPE_stored(block_stored(), 0)
  | BTYPE_fixed(block_fixed(), 1)
  | BTYPE_dynamic(block_dynamic(), 2)

(* COPY(before, distance, length, after): length bytes are each copied
   from distance back in the output so far, one after the other, so a
   copy with distance < length reads bytes it has just written *)
#pub dataprop COPY($A.cells, int, int, $A.cells) =
  | {output:$A.cells}{distance:int} COPY_done(output, distance, 0, output)
  | {output,next,after:$A.cells}{output_count,distance,length,copied:nat | 1 <= distance; distance <= output_count}
    COPY_step(output, distance, length + 1, after) of ($A.CLEN(output, output_count), $A.NTH(output, output_count - distance, copied), $A.APPEND(output, $A.ccons(copied, $A.cnil()), next), COPY(next, distance, length, after))

#pub prfun copy_functional {output:$A.cells}{distance,length:nat}{first,second:$A.cells}
  (COPY(output, distance, length, first), COPY(output, distance, length, second)): $A.CELLS_EQ(first, second)

(* SYMS_SIZED(litlen, dist, source, p, before, after, end_bit, symbols): the symbols
   from bit p, decoded by the literal/length code litlen and the distance code
   dist, up to the end-of-block symbol, take the output before to after, the
   end-of-block symbol ends at bit end_bit, and there are symbols + 1 of them (the
   count is what a lemma's termination metric reads, as BLOCKS_SIZED). A literal
   appends itself; a length symbol, its extra bits, a distance symbol and its
   extra bits are a copy. *)
#pub dataprop SYMS_SIZED($A.cells, $A.cells, $A.cells, int, $A.cells, $A.cells, int, int) =
  | {litlen,dist,source:$A.cells}{p,sym,used:nat}{output:$A.cells}
    SYMS_SIZED_end(litlen, dist, source, p, output, output, p + used, 0) of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_end_of_block(), sym))
  | {litlen,dist,source:$A.cells}{p,sym,used,end_bit,symbols:nat}{output,next,after:$A.cells}
    SYMS_SIZED_literal(litlen, dist, source, p, output, after, end_bit, symbols + 1)
    of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_literal(), sym),
        $A.APPEND(output, $A.ccons(sym, $A.cnil()), next), SYMS_SIZED(litlen, dist, source, p + used, next, after, end_bit, symbols))
  | {litlen,dist,source:$A.cells}{p,sym,used,length_extra_bits,length_base,length_extra_value,dist_sym,dist_used,dist_extra_bits,dist_base,dist_extra_value,end_bit,symbols:nat | sym == 285 || length_base + length_extra_value <= 257}{output,next,after:$A.cells}
    SYMS_SIZED_copy(litlen, dist, source, p, output, after, end_bit, symbols + 1)
    of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_length(), sym),
        LENGTH_SYMBOL(sym, length_extra_bits, length_base), BITS(source, p + used, length_extra_bits, length_extra_value),
        DECSYM(dist, source, p + used + length_extra_bits, dist_sym, dist_used), DISTANCE_SYMBOL(dist_sym, dist_extra_bits, dist_base),
        BITS(source, p + used + length_extra_bits + dist_used, dist_extra_bits, dist_extra_value),
        COPY(output, dist_base + dist_extra_value, length_base + length_extra_value, next),
        SYMS_SIZED(litlen, dist, source, p + used + length_extra_bits + dist_used + dist_extra_bits, next, after, end_bit, symbols))

(* SYMS(litlen, dist, source, p, before, after, end_bit): the symbols from bit p
   take the output before to after and the end-of-block symbol ends at end_bit.
   Made by SYMS_end, SYMS_literal and SYMS_copy below. *)
#pub dataprop SYMS($A.cells, $A.cells, $A.cells, int, $A.cells, $A.cells, int) =
  | {litlen,dist,source:$A.cells}{p:nat}{before,after:$A.cells}{end_bit,symbols:nat}
    SYMS_made(litlen, dist, source, p, before, after, end_bit) of SYMS_SIZED(litlen, dist, source, p, before, after, end_bit, symbols)

#pub prfun SYMS_end {litlen,dist,source:$A.cells}{p,sym,used:nat}{output:$A.cells}
  (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_end_of_block(), sym)): SYMS(litlen, dist, source, p, output, output, p + used)

#pub prfun SYMS_literal {litlen,dist,source:$A.cells}{p,sym,used,end_bit:nat}{output,next,after:$A.cells}
  (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_literal(), sym), $A.APPEND(output, $A.ccons(sym, $A.cnil()), next),
   SYMS(litlen, dist, source, p + used, next, after, end_bit)): SYMS(litlen, dist, source, p, output, after, end_bit)

#pub prfun SYMS_copy {litlen,dist,source:$A.cells}{p,sym,used,length_extra_bits,length_base,length_extra_value,dist_sym,dist_used,dist_extra_bits,dist_base,dist_extra_value,end_bit:nat | sym == 285 || length_base + length_extra_value <= 257}{output,next,after:$A.cells}
  (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_length(), sym),
   LENGTH_SYMBOL(sym, length_extra_bits, length_base), BITS(source, p + used, length_extra_bits, length_extra_value),
   DECSYM(dist, source, p + used + length_extra_bits, dist_sym, dist_used), DISTANCE_SYMBOL(dist_sym, dist_extra_bits, dist_base),
   BITS(source, p + used + length_extra_bits + dist_used, dist_extra_bits, dist_extra_value),
   COPY(output, dist_base + dist_extra_value, length_base + length_extra_value, next),
   SYMS(litlen, dist, source, p + used + length_extra_bits + dist_used + dist_extra_bits, next, after, end_bit)): SYMS(litlen, dist, source, p, output, after, end_bit)

#pub prfun syms_functional {litlen,dist,source:$A.cells}{p:nat}{output,first,second:$A.cells}{first_end,second_end:nat}
  (LENGTHS_FIT(litlen, 15), LENGTHS_FIT(dist, 15), SYMS(litlen, dist, source, p, output, first, first_end), SYMS(litlen, dist, source, p, output, second, second_end)): [first_end == second_end] $A.CELLS_EQ(first, second)

(* BLOCK(kind, source, p, before, after, end_bit): a block of the kind whose
   body starts at bit p (after its 3 header bits) takes the output before to
   after, and ends at bit end_bit. A constructor for each kind: the stored one
   here (3.2.4), the fixed and the dynamic with the steps that follow (keyword: blocks). *)
#pub dataprop BLOCK(block_kind, $A.cells, int, $A.cells, $A.cells, int) =
  (* skips to the byte boundary, LEN, NLEN = the complement of LEN, then LEN bytes *)
  | {source:$A.cells}{p,data_byte,len,nlen:nat | 8 * data_byte >= p; 8 * data_byte < p + 8; len + nlen == 65535}{before,data,after:$A.cells}
    BLOCK_stored(block_stored(), source, p, before, after, 8 * (data_byte + 4 + len))
    of (BITS(source, 8 * data_byte, 16, len), BITS(source, 8 * data_byte + 16, 16, nlen), SLICE(source, data_byte + 4, len, data), $A.APPEND(before, data, after))
  | {source,litlen,dist:$A.cells}{p,end_bit:nat}{before,after:$A.cells}
    BLOCK_fixed(block_fixed(), source, p, before, after, end_bit)
    of (FIXED_LITLEN(litlen), FIXED_DIST(dist), LENGTHS_FIT(litlen, 15), LENGTHS_FIT(dist, 15), SYMS(litlen, dist, source, p, before, after, end_bit))
  | {source,values,order,code_length_code,all_lengths,litlen,dist:$A.cells}{p,hlit,hdist,hclen,data_start,end_bit:nat | hlit <= 29; hdist <= 29}{before,after:$A.cells}
    BLOCK_dynamic(block_dynamic(), source, p, before, after, end_bit)
    of (BITS(source, p, 5, hlit), BITS(source, p + 5, 5, hdist), BITS(source, p + 10, 4, hclen),
        READ_LENGTHS3(source, p + 14, hclen + 4, values), CL_ORDER(order), CODE_LENGTHS_FROM(order, hclen + 4, values, 0, code_length_code),
        LENGTHS_FIT(code_length_code, 7), LENGTHS_FULL(code_length_code, 7),
        CODE_LENGTHS(code_length_code, source, p + 14 + 3 * (hclen + 4), $A.cnil(), hlit + 257 + hdist + 1, all_lengths, data_start),
        $A.CLEN(litlen, hlit + 257), $A.APPEND(litlen, dist, all_lengths), LITLEN_USABLE(litlen), DIST_USABLE(dist),
        SYMS(litlen, dist, source, data_start, before, after, end_bit))

#pub prfun slice_functional {source:$A.cells}{start,width:nat}{first,second:$A.cells}
  (SLICE(source, start, width, first), SLICE(source, start, width, second)): $A.CELLS_EQ(first, second)

#pub prfun block_functional {kind:block_kind}{source:$A.cells}{p:nat}{before,first,second:$A.cells}{first_end,second_end:nat}
  (BLOCK(kind, source, p, before, first, first_end), BLOCK(kind, source, p, before, second, second_end)): [first_end == second_end] $A.CELLS_EQ(first, second)

(* BLOCKS_SIZED(source, p, before, after, blocks): the blocks from bit p, ending
   at the one with BFINAL 1, take the output before to after, and there are
   blocks + 1 of them; the count is what a lemma's termination metric reads, as
   array's APPEND_SIZED (keyword: blocks). *)
#pub dataprop BLOCKS_SIZED($A.cells, int, $A.cells, $A.cells, int) =
  | {source:$A.cells}{p,btype,end_bit:nat}{kind:block_kind}{before,after:$A.cells}
    BLOCKS_SIZED_last(source, p, before, after, 0) of (BITS(source, p, 1, 1), BITS(source, p + 1, 2, btype), BTYPE(kind, btype), BLOCK(kind, source, p + 3, before, after, end_bit))
  | {source:$A.cells}{p,btype,end_bit,blocks:nat}{kind:block_kind}{before,middle,after:$A.cells}
    BLOCKS_SIZED_next(source, p, before, after, blocks + 1) of (BITS(source, p, 1, 0), BITS(source, p + 1, 2, btype), BTYPE(kind, btype), BLOCK(kind, source, p + 3, before, middle, end_bit), BLOCKS_SIZED(source, end_bit, middle, after, blocks))

(* BLOCKS(source, p, before, after): the blocks from bit p, ending at the one
   with BFINAL 1, take the output before to after. Made by BLOCKS_last and
   BLOCKS_next below, as APPEND is by APPEND_nil and APPEND_cons. *)
#pub dataprop BLOCKS($A.cells, int, $A.cells, $A.cells) =
  | {source:$A.cells}{p:nat}{before,after:$A.cells}{blocks:nat} BLOCKS_made(source, p, before, after) of BLOCKS_SIZED(source, p, before, after, blocks)

#pub prfun BLOCKS_last {source:$A.cells}{p,btype,end_bit:nat}{kind:block_kind}{before,after:$A.cells}
  (BITS(source, p, 1, 1), BITS(source, p + 1, 2, btype), BTYPE(kind, btype), BLOCK(kind, source, p + 3, before, after, end_bit)): BLOCKS(source, p, before, after)

#pub prfun BLOCKS_next {source:$A.cells}{p,btype,end_bit:nat}{kind:block_kind}{before,middle,after:$A.cells}
  (BITS(source, p, 1, 0), BITS(source, p + 1, 2, btype), BTYPE(kind, btype), BLOCK(kind, source, p + 3, before, middle, end_bit), BLOCKS(source, end_bit, middle, after)): BLOCKS(source, p, before, after)

#pub prfun blocks_functional {source:$A.cells}{p:nat}{before,first,second:$A.cells}
  (BLOCKS(source, p, before, first), BLOCKS(source, p, before, second)): $A.CELLS_EQ(first, second)

prfun _slice_functional {source:$A.cells}{start,width:nat}{first,second:$A.cells} .<width>.
  (first_slice: SLICE(source, start, width, first), second_slice: SLICE(source, start, width, second)): $A.CELLS_EQ(first, second) =
  case+ first_slice of
  | SLICE_nil() => (case+ second_slice of SLICE_nil() => $A.CELLS_EQ_refl())
  | SLICE_cons(first_nth, first_rest) =>
    (case+ second_slice of
     | SLICE_cons(second_nth, second_rest) => let
         prval () = $A.nth_functional(first_nth, second_nth)
       in (case+ _slice_functional(first_rest, second_rest) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl()) end)

primplement slice_functional {source}{start,width}{first,second} (first_slice, second_slice) = _slice_functional(first_slice, second_slice)

(* Proofs of the compressed data's symbols (keyword: symbols) *)

prfun _copy_functional {output:$A.cells}{distance,length:nat}{first,second:$A.cells} .<length>.
  (first_copy: COPY(output, distance, length, first), second_copy: COPY(output, distance, length, second)): $A.CELLS_EQ(first, second) =
  case+ first_copy of
  | COPY_done() => (case+ second_copy of COPY_done() => $A.CELLS_EQ_refl())
  | COPY_step(first_len, first_nth, first_append, first_rest) =>
    (case+ second_copy of
     | COPY_step(second_len, second_nth, second_append, second_rest) =>
       (let
          prval () = _clen_functional(first_len, second_len)
          prval () = $A.nth_functional(first_nth, second_nth)
        in
          (case+ $A.append_functional(first_append, second_append) of
           | $A.CELLS_EQ_refl() => _copy_functional(first_rest, second_rest))
        end))

primplement copy_functional {output}{distance,length}{first,second} (first_copy, second_copy) = _copy_functional(first_copy, second_copy)

prfun _pow2_functional {k,first,second:nat} .<k>.
  (first_pow: $AR.POW2(k, first), second_pow: $AR.POW2(k, second)): [first == second] void =
  case+ first_pow of
  | $AR.POW2_zero() => (case+ second_pow of $AR.POW2_zero() => ())
  | $AR.POW2_succ(first_rest) => (case+ second_pow of $AR.POW2_succ(second_rest) => _pow2_functional(first_rest, second_rest))

prfn _length_symbol_functional {sym,first_extra,first_base,second_extra,second_base:nat}
  (first: LENGTH_SYMBOL(sym, first_extra, first_base), second: LENGTH_SYMBOL(sym, second_extra, second_base)): [first_extra == second_extra; first_base == second_base] void =
  case+ first of
  | LENGTH_SYMBOL_short() =>
    (case+ second of
     | LENGTH_SYMBOL_short() => ()
     | LENGTH_SYMBOL_base_4_times(second_pow) => ()
     | LENGTH_SYMBOL_base_5_times(second_pow) => ()
     | LENGTH_SYMBOL_base_6_times(second_pow) => ()
     | LENGTH_SYMBOL_base_7_times(second_pow) => ()
     | LENGTH_SYMBOL_last() => ())
  | LENGTH_SYMBOL_base_4_times(first_pow) =>
    (case+ second of
     | LENGTH_SYMBOL_short() => ()
     | LENGTH_SYMBOL_base_4_times(second_pow) => _pow2_functional(first_pow, second_pow)
     | LENGTH_SYMBOL_base_5_times(second_pow) => ()
     | LENGTH_SYMBOL_base_6_times(second_pow) => ()
     | LENGTH_SYMBOL_base_7_times(second_pow) => ()
     | LENGTH_SYMBOL_last() => ())
  | LENGTH_SYMBOL_base_5_times(first_pow) =>
    (case+ second of
     | LENGTH_SYMBOL_short() => ()
     | LENGTH_SYMBOL_base_4_times(second_pow) => ()
     | LENGTH_SYMBOL_base_5_times(second_pow) => _pow2_functional(first_pow, second_pow)
     | LENGTH_SYMBOL_base_6_times(second_pow) => ()
     | LENGTH_SYMBOL_base_7_times(second_pow) => ()
     | LENGTH_SYMBOL_last() => ())
  | LENGTH_SYMBOL_base_6_times(first_pow) =>
    (case+ second of
     | LENGTH_SYMBOL_short() => ()
     | LENGTH_SYMBOL_base_4_times(second_pow) => ()
     | LENGTH_SYMBOL_base_5_times(second_pow) => ()
     | LENGTH_SYMBOL_base_6_times(second_pow) => _pow2_functional(first_pow, second_pow)
     | LENGTH_SYMBOL_base_7_times(second_pow) => ()
     | LENGTH_SYMBOL_last() => ())
  | LENGTH_SYMBOL_base_7_times(first_pow) =>
    (case+ second of
     | LENGTH_SYMBOL_short() => ()
     | LENGTH_SYMBOL_base_4_times(second_pow) => ()
     | LENGTH_SYMBOL_base_5_times(second_pow) => ()
     | LENGTH_SYMBOL_base_6_times(second_pow) => ()
     | LENGTH_SYMBOL_base_7_times(second_pow) => _pow2_functional(first_pow, second_pow)
     | LENGTH_SYMBOL_last() => ())
  | LENGTH_SYMBOL_last() =>
    (case+ second of
     | LENGTH_SYMBOL_short() => ()
     | LENGTH_SYMBOL_base_4_times(second_pow) => ()
     | LENGTH_SYMBOL_base_5_times(second_pow) => ()
     | LENGTH_SYMBOL_base_6_times(second_pow) => ()
     | LENGTH_SYMBOL_base_7_times(second_pow) => ()
     | LENGTH_SYMBOL_last() => ())

prfn _distance_symbol_functional {sym,first_extra,first_base,second_extra,second_base:nat}
  (first: DISTANCE_SYMBOL(sym, first_extra, first_base), second: DISTANCE_SYMBOL(sym, second_extra, second_base)): [first_extra == second_extra; first_base == second_base] void =
  case+ first of
  | DISTANCE_SYMBOL_short() =>
    (case+ second of
     | DISTANCE_SYMBOL_short() => ()
     | DISTANCE_SYMBOL_base_2_times(second_pow) => ()
     | DISTANCE_SYMBOL_base_3_times(second_pow) => ())
  | DISTANCE_SYMBOL_base_2_times(first_pow) =>
    (case+ second of
     | DISTANCE_SYMBOL_short() => ()
     | DISTANCE_SYMBOL_base_2_times(second_pow) => _pow2_functional(first_pow, second_pow)
     | DISTANCE_SYMBOL_base_3_times(second_pow) => ())
  | DISTANCE_SYMBOL_base_3_times(first_pow) =>
    (case+ second of
     | DISTANCE_SYMBOL_short() => ()
     | DISTANCE_SYMBOL_base_2_times(second_pow) => ()
     | DISTANCE_SYMBOL_base_3_times(second_pow) => _pow2_functional(first_pow, second_pow))

prfn _class_end_value {sym:nat} (class: SYMBOL_CLASS(symbol_end_of_block(), sym)): [sym == 256] void =
  case+ class of SYMBOL_CLASS_end_of_block() => ()

prfn _class_literal_value {sym:nat} (class: SYMBOL_CLASS(symbol_literal(), sym)): [sym <= 255] void =
  case+ class of SYMBOL_CLASS_literal() => ()

prfn _class_length_value {sym:nat} (class: SYMBOL_CLASS(symbol_length(), sym)): [257 <= sym; sym <= 285] void =
  case+ class of SYMBOL_CLASS_length() => ()

prfun _syms_sized_functional {litlen,dist,source:$A.cells}{p:nat}{output,first,second:$A.cells}{first_end,second_end,first_symbols,second_symbols:nat} .<first_symbols>.
  (litlen_fit: LENGTHS_FIT(litlen, 15), dist_fit: LENGTHS_FIT(dist, 15),
   first_proof: SYMS_SIZED(litlen, dist, source, p, output, first, first_end, first_symbols),
   second_proof: SYMS_SIZED(litlen, dist, source, p, output, second, second_end, second_symbols))
  : [first_end == second_end] $A.CELLS_EQ(first, second) =
  case+ first_proof of
  | SYMS_SIZED_end(first_dec, first_class) =>
    (case+ second_proof of
     | SYMS_SIZED_end(second_dec, second_class) =>
       (let prval () = decsym_functional(litlen_fit, first_dec, second_dec) in $A.CELLS_EQ_refl() end)
     | SYMS_SIZED_literal(second_dec, second_class, _, _) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
          prval () = _class_end_value(first_class)
          prval () = _class_literal_value(second_class)
        in $A.CELLS_EQ_refl() end)
     | SYMS_SIZED_copy(second_dec, second_class, _, _, _, _, _, _, _) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
          prval () = _class_end_value(first_class)
          prval () = _class_length_value(second_class)
        in $A.CELLS_EQ_refl() end))
  | SYMS_SIZED_literal(first_dec, first_class, first_append, first_rest) =>
    (case+ second_proof of
     | SYMS_SIZED_end(second_dec, second_class) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
          prval () = _class_literal_value(first_class)
          prval () = _class_end_value(second_class)
        in $A.CELLS_EQ_refl() end)
     | SYMS_SIZED_literal(second_dec, second_class, second_append, second_rest) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
        in
          (case+ $A.append_functional(first_append, second_append) of
           | $A.CELLS_EQ_refl() => _syms_sized_functional(litlen_fit, dist_fit, first_rest, second_rest))
        end)
     | SYMS_SIZED_copy(second_dec, second_class, _, _, _, _, _, _, _) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
          prval () = _class_literal_value(first_class)
          prval () = _class_length_value(second_class)
        in $A.CELLS_EQ_refl() end))
  | SYMS_SIZED_copy(first_dec, first_class, first_length_symbol, first_length_bits, first_dist_dec, first_dist_symbol, first_dist_bits, first_copy, first_rest) =>
    (case+ second_proof of
     | SYMS_SIZED_end(second_dec, second_class) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
          prval () = _class_length_value(first_class)
          prval () = _class_end_value(second_class)
        in $A.CELLS_EQ_refl() end)
     | SYMS_SIZED_literal(second_dec, second_class, _, _) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
          prval () = _class_length_value(first_class)
          prval () = _class_literal_value(second_class)
        in $A.CELLS_EQ_refl() end)
     | SYMS_SIZED_copy(second_dec, second_class, second_length_symbol, second_length_bits, second_dist_dec, second_dist_symbol, second_dist_bits, second_copy, second_rest) =>
       (let
          prval () = decsym_functional(litlen_fit, first_dec, second_dec)
          prval () = _length_symbol_functional(first_length_symbol, second_length_symbol)
          prval () = bits_functional(first_length_bits, second_length_bits)
          prval () = decsym_functional(dist_fit, first_dist_dec, second_dist_dec)
          prval () = _distance_symbol_functional(first_dist_symbol, second_dist_symbol)
          prval () = bits_functional(first_dist_bits, second_dist_bits)
        in
          (case+ _copy_functional(first_copy, second_copy) of
           | $A.CELLS_EQ_refl() => _syms_sized_functional(litlen_fit, dist_fit, first_rest, second_rest))
        end))

primplement syms_functional {litlen,dist,source}{p}{output,first,second}{first_end,second_end} (litlen_fit, dist_fit, first_proof, second_proof) =
  (case+ first_proof of
   | SYMS_made(first_sized) => (case+ second_proof of SYMS_made(second_sized) => _syms_sized_functional(litlen_fit, dist_fit, first_sized, second_sized)))

primplement SYMS_end {litlen,dist,source}{p,sym,used}{output} (decoded, class) = SYMS_made(SYMS_SIZED_end(decoded, class))

primplement SYMS_literal {litlen,dist,source}{p,sym,used,end_bit}{output,next,after} (decoded, class, appended, rest) =
  (case+ rest of SYMS_made(rest_sized) => SYMS_made(SYMS_SIZED_literal(decoded, class, appended, rest_sized)))

primplement SYMS_copy {litlen,dist,source}{p,sym,used,length_extra_bits,length_base,length_extra_value,dist_sym,dist_used,dist_extra_bits,dist_base,dist_extra_value,end_bit}{output,next,after}
  (decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied, rest) =
  (case+ rest of SYMS_made(rest_sized) => SYMS_made(SYMS_SIZED_copy(decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied, rest_sized)))

prfun _run_functional {count:nat}{value:int}{rest,first,second:$A.cells} .<count>.
  (first_run: RUN(count, value, rest, first), second_run: RUN(count, value, rest, second)): $A.CELLS_EQ(first, second) =
  case+ first_run of
  | RUN_zero() => (case+ second_run of RUN_zero() => $A.CELLS_EQ_refl())
  | RUN_cons(first_rest) => (case+ second_run of RUN_cons(second_rest) => (case+ _run_functional(first_rest, second_rest) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl()))

prfn _fixed_litlen_functional {first,second:$A.cells} (first_fixed: FIXED_LITLEN(first), second_fixed: FIXED_LITLEN(second)): $A.CELLS_EQ(first, second) =
  case+ first_fixed of
  | FIXED_LITLEN_mk(first_144, first_112, first_24, first_8) =>
    (case+ second_fixed of
     | FIXED_LITLEN_mk(second_144, second_112, second_24, second_8) =>
       (case+ _run_functional(first_8, second_8) of
        | $A.CELLS_EQ_refl() =>
          (case+ _run_functional(first_24, second_24) of
           | $A.CELLS_EQ_refl() =>
             (case+ _run_functional(first_112, second_112) of
              | $A.CELLS_EQ_refl() => _run_functional(first_144, second_144)))))

prfn _fixed_dist_functional {first,second:$A.cells} (first_fixed: FIXED_DIST(first), second_fixed: FIXED_DIST(second)): $A.CELLS_EQ(first, second) =
  case+ first_fixed of
  | FIXED_DIST_mk(first_run) => (case+ second_fixed of FIXED_DIST_mk(second_run) => _run_functional(first_run, second_run))

(* Proofs of the dynamic block's header (keyword: dynamic-header) *)

dataprop _NOT_IN(int, $A.cells) =
  | {x:int} _NOT_IN_nil(x, $A.cnil())
  | {x,y:int | x != y}{rest:$A.cells} _NOT_IN_cons(x, $A.ccons(y, rest)) of _NOT_IN(x, rest)

dataprop _DISTINCT($A.cells) =
  | _DISTINCT_nil($A.cnil())
  | {x:int}{rest:$A.cells} _DISTINCT_cons($A.ccons(x, rest)) of (_NOT_IN(x, rest), _DISTINCT(rest))

dataprop _BOTH_EQ($A.cells, $A.cells, $A.cells, $A.cells) =
  | {first,second:$A.cells} _BOTH_EQ_mk(first, first, second, second)

prfun _not_in_nth {x:int}{cells:$A.cells}{k:nat} .<k>.
  (notin: _NOT_IN(x, cells), found: $A.NTH(cells, k, x)): [false] void =
  case+ found of
  | $A.NTH_here() => (case+ notin of _NOT_IN_cons(_) => ())
  | $A.NTH_there(found_rest) => (case+ notin of _NOT_IN_cons(notin_rest) => _not_in_nth(notin_rest, found_rest))

prfun _distinct_nth {cells:$A.cells}{i,j:nat}{s:int} .<i>.
  (distinct: _DISTINCT(cells), first: $A.NTH(cells, i, s), second: $A.NTH(cells, j, s)): [i == j] void =
  case+ first of
  | $A.NTH_here() =>
    (case+ second of
     | $A.NTH_here() => ()
     | $A.NTH_there(second_rest) =>
       (case+ distinct of _DISTINCT_cons(notin, _) => (let prval () = _not_in_nth(notin, second_rest) in () end)))
  | $A.NTH_there(first_rest) =>
    (case+ second of
     | $A.NTH_here() =>
       (case+ distinct of _DISTINCT_cons(notin, _) => (let prval () = _not_in_nth(notin, first_rest) in () end))
     | $A.NTH_there(second_rest) =>
       (case+ distinct of _DISTINCT_cons(_, distinct_rest) => _distinct_nth(distinct_rest, first_rest, second_rest)))

prfn _cl_order_distinct {order:$A.cells} (order_proof: CL_ORDER(order)): _DISTINCT(order) =
  case+ order_proof of
  | CL_ORDER_mk() => _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))))))))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))))))))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))))))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))))))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil()))), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_cons(_NOT_IN_nil())), _DISTINCT_cons(_NOT_IN_cons(_NOT_IN_nil()), _DISTINCT_cons(_NOT_IN_nil(), _DISTINCT_nil())))))))))))))))))))

prfun _prefix_nth {order:$A.cells}{count,pos:nat | pos < count}{sym:int} .<pos>.
  (notin: NOT_IN_PREFIX(order, count, sym), found: $A.NTH(order, pos, sym)): [false] void =
  case+ found of
  | $A.NTH_here() => (case+ notin of NOT_IN_PREFIX_cons(_) => ())
  | $A.NTH_there(found_rest) => (case+ notin of NOT_IN_PREFIX_cons(notin_rest) => _prefix_nth(notin_rest, found_rest))

prfn _code_length_of_functional {order,values:$A.cells}{sym,count,first_len,second_len:nat}
  (order_proof: CL_ORDER(order), values_len: $A.CLEN(values, count),
   first: CODE_LENGTH_OF(order, sym, count, values, first_len), second: CODE_LENGTH_OF(order, sym, count, values, second_len))
  : [first_len == second_len] void =
  case+ first of
  | CODE_LENGTH_OF_stored(first_order_nth, first_values_nth) =>
    (case+ second of
     | CODE_LENGTH_OF_stored(second_order_nth, second_values_nth) => let
         prval () = _distinct_nth(_cl_order_distinct(order_proof), first_order_nth, second_order_nth)
       in $A.nth_functional(first_values_nth, second_values_nth) end
     | CODE_LENGTH_OF_absent(second_absent) => let
         prval () = $A.nth_in_len(first_values_nth, values_len)
         prval () = _prefix_nth(second_absent, first_order_nth)
       in () end)
  | CODE_LENGTH_OF_absent(first_absent) =>
    (case+ second of
     | CODE_LENGTH_OF_stored(second_order_nth, second_values_nth) => let
         prval () = $A.nth_in_len(second_values_nth, values_len)
         prval () = _prefix_nth(first_absent, second_order_nth)
       in () end
     | CODE_LENGTH_OF_absent(_) => ())

prfun _read_lengths3_clen {source:$A.cells}{p,count:nat}{values:$A.cells} .<count>.
  (read: READ_LENGTHS3(source, p, count, values)): $A.CLEN(values, count) =
  case+ read of
  | READ_LENGTHS3_nil() => $A.CLEN_nil()
  | READ_LENGTHS3_cons(_, read_rest) => $A.CLEN_cons(_read_lengths3_clen(read_rest))

prfun _read_lengths3_functional {source:$A.cells}{p,count:nat}{first,second:$A.cells} .<count>.
  (first_read: READ_LENGTHS3(source, p, count, first), second_read: READ_LENGTHS3(source, p, count, second)): $A.CELLS_EQ(first, second) =
  case+ first_read of
  | READ_LENGTHS3_nil() => (case+ second_read of READ_LENGTHS3_nil() => $A.CELLS_EQ_refl())
  | READ_LENGTHS3_cons(first_bits, first_rest) =>
    (case+ second_read of
     | READ_LENGTHS3_cons(second_bits, second_rest) =>
       (let
          prval () = bits_functional(first_bits, second_bits)
        in
          (case+ _read_lengths3_functional(first_rest, second_rest) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl())
        end))

primplement read_lengths3_functional {source}{p,count}{first,second} (first_read, second_read) = _read_lengths3_functional(first_read, second_read)

prfun _code_lengths_from_functional {order,values:$A.cells}{count,first_sym:nat | first_sym <= 19}{first,second:$A.cells} .<19 - first_sym>.
  (order_proof: CL_ORDER(order), values_len: $A.CLEN(values, count),
   first_from: CODE_LENGTHS_FROM(order, count, values, first_sym, first), second_from: CODE_LENGTHS_FROM(order, count, values, first_sym, second))
  : $A.CELLS_EQ(first, second) =
  case+ first_from of
  | CODE_LENGTHS_FROM_end() => (case+ second_from of CODE_LENGTHS_FROM_end() => $A.CELLS_EQ_refl())
  | CODE_LENGTHS_FROM_cons(first_of, first_rest) =>
    (case+ second_from of
     | CODE_LENGTHS_FROM_cons(second_of, second_rest) =>
       (let
          prval () = _code_length_of_functional(order_proof, values_len, first_of, second_of)
        in
          (case+ _code_lengths_from_functional(order_proof, values_len, first_rest, second_rest) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl())
        end))

primplement code_lengths_from_functional {order,values}{count,first_sym}{first,second} (order_proof, values_len, first_from, second_from) =
  _code_lengths_from_functional(order_proof, values_len, first_from, second_from)

prfn _length_class_literal_value {sym:nat} (class: LENGTH_CLASS(length_literal(), sym)): [sym <= 15] void =
  case+ class of LENGTH_CLASS_literal() => ()

prfn _length_class_previous_value {sym:nat} (class: LENGTH_CLASS(length_repeat_previous(), sym)): [sym == 16] void =
  case+ class of LENGTH_CLASS_repeat_previous() => ()

prfn _length_class_short_value {sym:nat} (class: LENGTH_CLASS(length_zeros_short(), sym)): [sym == 17] void =
  case+ class of LENGTH_CLASS_zeros_short() => ()

prfn _length_class_long_value {sym:nat} (class: LENGTH_CLASS(length_zeros_long(), sym)): [sym == 18] void =
  case+ class of LENGTH_CLASS_zeros_long() => ()


prfun _code_lengths_sized_functional {code_length_code,source:$A.cells}{p,total:nat}{so_far,first,second:$A.cells}{first_end,second_end,first_steps,second_steps:nat} .<first_steps>.
  (fit: LENGTHS_FIT(code_length_code, 7),
   first_proof: CODE_LENGTHS_SIZED(code_length_code, source, p, so_far, total, first, first_end, first_steps),
   second_proof: CODE_LENGTHS_SIZED(code_length_code, source, p, so_far, total, second, second_end, second_steps))
  : [first_end == second_end] $A.CELLS_EQ(first, second) =
  case+ first_proof of
  | CODE_LENGTHS_SIZED_done(a_clen) =>
    (case+ second_proof of
     | CODE_LENGTHS_SIZED_done(b_clen) => $A.CELLS_EQ_refl()
     | CODE_LENGTHS_SIZED_literal(b_clen, b_dec, b_class, b_app, b_rest) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_repeat_previous(b_clen, b_dec, b_class, b_bits, b_nth, b_run, b_app, b_rest) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_short(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_long(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end))
  | CODE_LENGTHS_SIZED_literal(a_clen, a_dec, a_class, a_app, a_rest) =>
    (case+ second_proof of
     | CODE_LENGTHS_SIZED_done(b_clen) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_literal(b_clen, b_dec, b_class, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _clen_functional(a_clen, b_clen)
        in
          (case+ $A.append_functional(a_app, b_app) of $A.CELLS_EQ_refl() => _code_lengths_sized_functional(fit, a_rest, b_rest))
        end)
     | CODE_LENGTHS_SIZED_repeat_previous(b_clen, b_dec, b_class, b_bits, b_nth, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_literal_value(a_class)
          prval () = _length_class_previous_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_short(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_literal_value(a_class)
          prval () = _length_class_short_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_long(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_literal_value(a_class)
          prval () = _length_class_long_value(b_class)
        in $A.CELLS_EQ_refl() end))
  | CODE_LENGTHS_SIZED_repeat_previous(a_clen, a_dec, a_class, a_bits, a_nth, a_run, a_app, a_rest) =>
    (case+ second_proof of
     | CODE_LENGTHS_SIZED_done(b_clen) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_literal(b_clen, b_dec, b_class, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_previous_value(a_class)
          prval () = _length_class_literal_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_repeat_previous(b_clen, b_dec, b_class, b_bits, b_nth, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _clen_functional(a_clen, b_clen)
          prval () = bits_functional(a_bits, b_bits)
          prval () = $A.nth_functional(a_nth, b_nth)
        in
          (case+ _run_functional(a_run, b_run) of $A.CELLS_EQ_refl() => (case+ $A.append_functional(a_app, b_app) of $A.CELLS_EQ_refl() => _code_lengths_sized_functional(fit, a_rest, b_rest)))
        end)
     | CODE_LENGTHS_SIZED_zeros_short(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_previous_value(a_class)
          prval () = _length_class_short_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_long(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_previous_value(a_class)
          prval () = _length_class_long_value(b_class)
        in $A.CELLS_EQ_refl() end))
  | CODE_LENGTHS_SIZED_zeros_short(a_clen, a_dec, a_class, a_bits, a_run, a_app, a_rest) =>
    (case+ second_proof of
     | CODE_LENGTHS_SIZED_done(b_clen) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_literal(b_clen, b_dec, b_class, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_short_value(a_class)
          prval () = _length_class_literal_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_repeat_previous(b_clen, b_dec, b_class, b_bits, b_nth, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_short_value(a_class)
          prval () = _length_class_previous_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_short(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _clen_functional(a_clen, b_clen)
          prval () = bits_functional(a_bits, b_bits)
        in
          (case+ _run_functional(a_run, b_run) of $A.CELLS_EQ_refl() => (case+ $A.append_functional(a_app, b_app) of $A.CELLS_EQ_refl() => _code_lengths_sized_functional(fit, a_rest, b_rest)))
        end)
     | CODE_LENGTHS_SIZED_zeros_long(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_short_value(a_class)
          prval () = _length_class_long_value(b_class)
        in $A.CELLS_EQ_refl() end))
  | CODE_LENGTHS_SIZED_zeros_long(a_clen, a_dec, a_class, a_bits, a_run, a_app, a_rest) =>
    (case+ second_proof of
     | CODE_LENGTHS_SIZED_done(b_clen) => (let prval () = _clen_functional(a_clen, b_clen) in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_literal(b_clen, b_dec, b_class, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_long_value(a_class)
          prval () = _length_class_literal_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_repeat_previous(b_clen, b_dec, b_class, b_bits, b_nth, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_long_value(a_class)
          prval () = _length_class_previous_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_short(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _length_class_long_value(a_class)
          prval () = _length_class_short_value(b_class)
        in $A.CELLS_EQ_refl() end)
     | CODE_LENGTHS_SIZED_zeros_long(b_clen, b_dec, b_class, b_bits, b_run, b_app, b_rest) => (let
          prval () = decsym_functional(fit, a_dec, b_dec)
          prval () = _clen_functional(a_clen, b_clen)
          prval () = bits_functional(a_bits, b_bits)
        in
          (case+ _run_functional(a_run, b_run) of $A.CELLS_EQ_refl() => (case+ $A.append_functional(a_app, b_app) of $A.CELLS_EQ_refl() => _code_lengths_sized_functional(fit, a_rest, b_rest)))
        end))

primplement code_lengths_functional {code_length_code,source}{p,total}{so_far,first,second}{first_end,second_end} (fit, first_proof, second_proof) =
  (case+ first_proof of
   | CODE_LENGTHS_made(first_sized) => (case+ second_proof of CODE_LENGTHS_made(second_sized) => _code_lengths_sized_functional(fit, first_sized, second_sized)))

primplement CODE_LENGTHS_done {code_length_code,source}{p,total}{so_far} (so_far_len) = CODE_LENGTHS_made(CODE_LENGTHS_SIZED_done(so_far_len))

primplement CODE_LENGTHS_literal (so_far_len, decoded, class, appended, rest) =
  (case+ rest of CODE_LENGTHS_made(rest_sized) => CODE_LENGTHS_made(CODE_LENGTHS_SIZED_literal(so_far_len, decoded, class, appended, rest_sized)))

primplement CODE_LENGTHS_repeat_previous (so_far_len, decoded, class, extra, previous, run, appended, rest) =
  (case+ rest of CODE_LENGTHS_made(rest_sized) => CODE_LENGTHS_made(CODE_LENGTHS_SIZED_repeat_previous(so_far_len, decoded, class, extra, previous, run, appended, rest_sized)))

primplement CODE_LENGTHS_zeros_short (so_far_len, decoded, class, extra, run, appended, rest) =
  (case+ rest of CODE_LENGTHS_made(rest_sized) => CODE_LENGTHS_made(CODE_LENGTHS_SIZED_zeros_short(so_far_len, decoded, class, extra, run, appended, rest_sized)))

primplement CODE_LENGTHS_zeros_long (so_far_len, decoded, class, extra, run, appended, rest) =
  (case+ rest of CODE_LENGTHS_made(rest_sized) => CODE_LENGTHS_made(CODE_LENGTHS_SIZED_zeros_long(so_far_len, decoded, class, extra, run, appended, rest_sized)))

prfun _append_sized_len {first,second,both:$A.cells}{n:nat} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n)): $A.CLEN(first, n) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => $A.CLEN_nil()
  | $A.APPEND_SIZED_cons(appended_rest) => $A.CLEN_cons(_append_sized_len(appended_rest))

prfun _append_sized_first {first_a,first_b,second_a,second_b,both:$A.cells}{n:nat} .<n>.
  (first: $A.APPEND_SIZED(first_a, first_b, both, n), second: $A.APPEND_SIZED(second_a, second_b, both, n)): $A.CELLS_EQ(first_a, second_a) =
  case+ first of
  | $A.APPEND_SIZED_nil() => (case+ second of $A.APPEND_SIZED_nil() => $A.CELLS_EQ_refl())
  | $A.APPEND_SIZED_cons(first_rest) =>
    (case+ second of
     | $A.APPEND_SIZED_cons(second_rest) =>
       (case+ _append_sized_first(first_rest, second_rest) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl()))

prfun _append_sized_second {a,first_b,second_b,both:$A.cells}{n,m:nat} .<n>.
  (first: $A.APPEND_SIZED(a, first_b, both, n), second: $A.APPEND_SIZED(a, second_b, both, m)): $A.CELLS_EQ(first_b, second_b) =
  case+ first of
  | $A.APPEND_SIZED_nil() => (case+ second of $A.APPEND_SIZED_nil() => $A.CELLS_EQ_refl())
  | $A.APPEND_SIZED_cons(first_rest) =>
    (case+ second of
     | $A.APPEND_SIZED_cons(second_rest) => _append_sized_second(first_rest, second_rest))

prfn _split_functional {first_a,first_b,second_a,second_b,both:$A.cells}{n:nat}
  (first_len: $A.CLEN(first_a, n), second_len: $A.CLEN(second_a, n), first: $A.APPEND(first_a, first_b, both), second: $A.APPEND(second_a, second_b, both))
  : _BOTH_EQ(first_a, second_a, first_b, second_b) =
  case+ first of
  | $A.APPEND_made(first_sized) =>
    (case+ second of
     | $A.APPEND_made(second_sized) =>
       (let
          prval () = _clen_functional(first_len, _append_sized_len(first_sized))
          prval () = _clen_functional(second_len, _append_sized_len(second_sized))
        in
          (case+ _append_sized_first(first_sized, second_sized) of
           | $A.CELLS_EQ_refl() => (case+ _append_sized_second(first_sized, second_sized) of $A.CELLS_EQ_refl() => _BOTH_EQ_mk()))
        end))

prfn _litlen_fit {lengths:$A.cells} (usable: LITLEN_USABLE(lengths)): LENGTHS_FIT(lengths, 15) =
  case+ usable of
  | LITLEN_USABLE_full(fit, _) => fit
  | LITLEN_USABLE_single(fit, _) => fit

prfn _dist_fit {lengths:$A.cells} (usable: DIST_USABLE(lengths)): LENGTHS_FIT(lengths, 15) =
  case+ usable of
  | DIST_USABLE_full(fit, _) => fit
  | DIST_USABLE_single(fit, _) => fit
  | DIST_USABLE_empty(fit, _) => fit

prfun _block_functional {kind:block_kind}{source:$A.cells}{p:nat}{before,first,second:$A.cells}{first_end,second_end:nat} .<>.
  (first_block: BLOCK(kind, source, p, before, first, first_end), second_block: BLOCK(kind, source, p, before, second, second_end))
  : [first_end == second_end] $A.CELLS_EQ(first, second) =
  case+ first_block of
  | BLOCK_stored(first_len, first_nlen, first_slice, first_append) =>
    (case+ second_block of
     | BLOCK_stored(second_len, second_nlen, second_slice, second_append) => let
         prval () = bits_functional(first_len, second_len)
       in
         (case+ slice_functional(first_slice, second_slice) of
          | $A.CELLS_EQ_refl() => $A.append_functional(first_append, second_append))
       end)
  | BLOCK_fixed(first_litlen, first_dist, first_litlen_fit, first_dist_fit, first_syms) =>
    (case+ second_block of
     | BLOCK_fixed(second_litlen, second_dist, second_litlen_fit, second_dist_fit, second_syms) =>
       (case+ _fixed_litlen_functional(first_litlen, second_litlen) of
        | $A.CELLS_EQ_refl() =>
          (case+ _fixed_dist_functional(first_dist, second_dist) of
           | $A.CELLS_EQ_refl() => syms_functional(first_litlen_fit, first_dist_fit, first_syms, second_syms))))
  | BLOCK_dynamic(first_hlit, first_hdist, first_hclen, first_values, first_order, first_from, first_fit, first_full, first_lengths, first_litlen_len, first_append, first_litlen_usable, first_dist_usable, first_syms) =>
    (case+ second_block of
     | BLOCK_dynamic(second_hlit, second_hdist, second_hclen, second_values, second_order, second_from, second_fit, second_full, second_lengths, second_litlen_len, second_append, second_litlen_usable, second_dist_usable, second_syms) =>
       (let
          prval () = bits_functional(first_hlit, second_hlit)
          prval () = bits_functional(first_hdist, second_hdist)
          prval () = bits_functional(first_hclen, second_hclen)
          prval first_values_len = _read_lengths3_clen(first_values)
        in
          (case+ _read_lengths3_functional(first_values, second_values) of
           | $A.CELLS_EQ_refl() =>
             (case+ first_order of
              | CL_ORDER_mk() =>
                (case+ second_order of
                 | CL_ORDER_mk() =>
                   (case+ _code_lengths_from_functional(first_order, first_values_len, first_from, second_from) of
                    | $A.CELLS_EQ_refl() =>
                      (case+ code_lengths_functional(first_fit, first_lengths, second_lengths) of
                       | $A.CELLS_EQ_refl() =>
                         (case+ _split_functional(first_litlen_len, second_litlen_len, first_append, second_append) of
                          | _BOTH_EQ_mk() => syms_functional(_litlen_fit(first_litlen_usable), _dist_fit(first_dist_usable), first_syms, second_syms)))))))
        end))

primplement block_functional {kind}{source}{p}{before,first,second}{first_end,second_end} (first_block, second_block) = _block_functional(first_block, second_block)

prfun _blocks_sized_functional {source:$A.cells}{p:nat}{before,first,second:$A.cells}{first_blocks,second_blocks:nat} .<first_blocks>.
  (first_proof: BLOCKS_SIZED(source, p, before, first, first_blocks), second_proof: BLOCKS_SIZED(source, p, before, second, second_blocks))
  : $A.CELLS_EQ(first, second) =
  case+ first_proof of
  | BLOCKS_SIZED_last(first_final, first_bits, first_btype, first_block) =>
    (case+ second_proof of
     | BLOCKS_SIZED_last(second_final, second_bits, second_btype, second_block) => let
         prval () = bits_functional(first_bits, second_bits)
       in
         (case+ first_btype of
          | BTYPE_stored() => (case+ second_btype of BTYPE_stored() => (case+ block_functional(first_block, second_block) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl()))
          | BTYPE_fixed() => (case+ second_btype of BTYPE_fixed() => (case+ block_functional(first_block, second_block) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl()))
          | BTYPE_dynamic() => (case+ second_btype of BTYPE_dynamic() => (case+ block_functional(first_block, second_block) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl())))
       end
     | BLOCKS_SIZED_next(second_final, _, _, _, _) =>
       (let
          prval () = bits_functional(first_final, second_final)
        in $A.CELLS_EQ_refl() end))
  | BLOCKS_SIZED_next(first_final, first_bits, first_btype, first_block, first_rest) =>
    (case+ second_proof of
     | BLOCKS_SIZED_last(second_final, _, _, _) =>
       (let
          prval () = bits_functional(first_final, second_final)
        in $A.CELLS_EQ_refl() end)
     | BLOCKS_SIZED_next(second_final, second_bits, second_btype, second_block, second_rest) =>
       (let
          prval () = bits_functional(first_bits, second_bits)
        in
          (case+ first_btype of
           | BTYPE_stored() => (case+ second_btype of BTYPE_stored() => (case+ block_functional(first_block, second_block) of $A.CELLS_EQ_refl() => _blocks_sized_functional(first_rest, second_rest)))
           | BTYPE_fixed() => (case+ second_btype of BTYPE_fixed() => (case+ block_functional(first_block, second_block) of $A.CELLS_EQ_refl() => _blocks_sized_functional(first_rest, second_rest)))
           | BTYPE_dynamic() => (case+ second_btype of BTYPE_dynamic() => (case+ block_functional(first_block, second_block) of $A.CELLS_EQ_refl() => _blocks_sized_functional(first_rest, second_rest))))
        end))

primplement blocks_functional {source}{p}{before,first,second} (first_proof, second_proof) =
  (case+ first_proof of
   | BLOCKS_made(first_sized) => (case+ second_proof of BLOCKS_made(second_sized) => _blocks_sized_functional(first_sized, second_sized)))

primplement BLOCKS_last {source}{p,btype,end_bit}{kind}{before,after} (final, bits, btype, block) = BLOCKS_made(BLOCKS_SIZED_last(final, bits, btype, block))

primplement BLOCKS_next {source}{p,btype,end_bit}{kind}{before,middle,after} (final, bits, btype, block, rest) =
  (case+ rest of BLOCKS_made(rest_sized) => BLOCKS_made(BLOCKS_SIZED_next(final, bits, btype, block, rest_sized)))

(* Window storage (streaming window keyword): one barr of 65536 bytes, the last 32768 bytes of output plus the half being filled, well inside barr_alloc's bound; no arena.
   The decoder keeps a window, not the output: a back-reference reaches at
   most 32768 bytes back (3.2.5). TAKE_LAST(output, keep, window): window is
   the last min(keep, count) cells of output *)
#pub dataprop TAKE_LAST($A.cells, int, $A.cells) =
  | {output:$A.cells}{count,keep:nat | count <= keep} TAKE_LAST_short(output, keep, output) of $A.CLEN(output, count)
  | {rest,window:$A.cells}{head:int}{count,keep:nat | keep <= count} TAKE_LAST_drop($A.ccons(head, rest), keep, window)
    of ($A.CLEN(rest, count), TAKE_LAST(rest, keep, window))

(* WINDOW(output, window): the window holds the last min(32768, written)
   bytes of the output so far *)
#pub dataprop WINDOW($A.cells, $A.cells) =
  | {output,window:$A.cells} WINDOW_mk(output, window) of TAKE_LAST(output, 32768, window)

(* The window lives in the decoder's 65536-byte barr: the last cells
   written are the window, starting at cell start of the barr's cells *)
#pub dataprop WINDOW_IN_BUFFER($A.cells, int, $A.cells) =
  | {buffer,window:$A.cells}{start,count:nat} WINDOW_IN_BUFFER_mk(buffer, start, window) of (SLICE(buffer, start, count, window), $A.CLEN(window, count))

#pub prfun window_functional {output,first,second:$A.cells} (WINDOW(output, first), WINDOW(output, second)): $A.CELLS_EQ(first, second)

(* The window after appending data to the output: the last 32768 of the
   window and the data, and it is the window of the output after. The
   premise CLEN(data, count) is added to the approved declaration: taking the last
   32768 cells of a sequence needs its length, and the decoder has it (a literal
   is one cell, a copy has length cells) (keyword: window). *)
#pub dataprop WINDOW_AFTER_APPEND($A.cells, $A.cells, $A.cells) =
  | {window,data,next,both,next_window:$A.cells}
    WINDOW_AFTER_APPEND_mk(window, data, next) of ($A.APPEND(window, data, both), TAKE_LAST(both, 32768, next_window), WINDOW(next, next_window))

#pub prfun window_append {output,window,data,next:$A.cells}{count:nat}
  (WINDOW(output, window), $A.APPEND(output, data, next), $A.CLEN(data, count)): WINDOW_AFTER_APPEND(window, data, next)

(* A copy read from the window is the copy read from the output: the window
   followed by the copied cells, cut to its last 32768, is the window of the
   output after the copy *)
#pub dataprop WINDOW_AFTER_COPY($A.cells, int, int, $A.cells) =
  | {window,after,both,next_window:$A.cells}{distance,length:nat}
    WINDOW_AFTER_COPY_mk(window, distance, length, after) of (COPY(window, distance, length, both), TAKE_LAST(both, 32768, next_window), WINDOW(after, next_window))

#pub prfun window_copy {output,window,after:$A.cells}{distance,length:nat | distance <= 32768}
  (WINDOW(output, window), COPY(output, distance, length, after)): WINDOW_AFTER_COPY(window, distance, length, after)

(* The input in chunks: how a buffer relates to the consumed prefix (zip#64). The
   compressed bytes are read from a reader in chunks (bats-lang/file#76). Its index is
   the cells consumed so far, and at the end of the file it closes, as the whole
   compressed sequence the proof talks about. Bits read from a prefix are bits of the
   whole sequence: *)
#pub prfun bits_in_prefix {earlier,rest,whole:$A.cells}{p,width,value:nat}
  ($A.APPEND(earlier, rest, whole), BITS(earlier, p, width, value)): BITS(whole, p, width, value)

#pub prfun hbits_in_prefix {earlier,rest,whole:$A.cells}{p,width,code:nat}
  ($A.APPEND(earlier, rest, whole), HBITS(earlier, p, width, code)): HBITS(whole, p, width, code)

(* BUFFER_AT(previous, chunk, consumed, start): the chunk in the decoder's
   buffer was the last read, consumed is the cells before it and the chunk,
   and the buffer's cell i is cell start + i of the consumed cells *)
#pub dataprop BUFFER_AT($A.cells, $A.cells, $A.cells, int) =
  | {previous,chunk,consumed:$A.cells}{start:nat} BUFFER_AT_mk(previous, chunk, consumed, start) of ($A.CLEN(previous, start), $A.APPEND(previous, chunk, consumed))

#pub prfun buffer_nth {previous,chunk,consumed:$A.cells}{start,index,value:nat}
  (BUFFER_AT(previous, chunk, consumed, start), $A.NTH(chunk, index, value)): $A.NTH(consumed, start + index, value)

(* RESERVOIR(consumed, p, count, value): the bit reservoir the decoder holds
   across chunks is the count bits from bit p of the consumed cells *)
#pub dataprop RESERVOIR($A.cells, int, int, int) =
  | {consumed:$A.cells}{p,count,value:nat} RESERVOIR_mk(consumed, p, count, value) of BITS(consumed, p, count, value)

(* Proofs of the window and of the chunked input (keyword: window) *)

prfn _take_last_len {output:$A.cells}{keep:nat}{window:$A.cells}
  (taken: TAKE_LAST(output, keep, window)): [n:nat] $A.CLEN(output, n) =
  case+ taken of
  | TAKE_LAST_short(output_len) => output_len
  | TAKE_LAST_drop(rest_len, _) => $A.CLEN_cons(rest_len)

prfun _take_last_total {cells:$A.cells}{keep,n:nat} .<n>.
  (cells_len: $A.CLEN(cells, n)): [window:$A.cells] TAKE_LAST(cells, keep, window) =
  sif n <= keep then TAKE_LAST_short(cells_len)
  else (case+ cells_len of $A.CLEN_cons(rest_len) => TAKE_LAST_drop(rest_len, _take_last_total(rest_len)))

prfun _take_last_functional {output:$A.cells}{keep,n:nat}{first,second:$A.cells} .<n>.
  (output_len: $A.CLEN(output, n), first_taken: TAKE_LAST(output, keep, first), second_taken: TAKE_LAST(output, keep, second)): $A.CELLS_EQ(first, second) =
  case+ first_taken of
  | TAKE_LAST_short(first_len) =>
    (case+ second_taken of
     | TAKE_LAST_short(_) => $A.CELLS_EQ_refl()
     | TAKE_LAST_drop(second_rest_len, _) =>
       (let prval () = _clen_functional(first_len, $A.CLEN_cons(second_rest_len)) in $A.CELLS_EQ_refl() end))
  | TAKE_LAST_drop(first_rest_len, first_rest) =>
    (case+ second_taken of
     | TAKE_LAST_short(second_len) =>
       (let prval () = _clen_functional(second_len, $A.CLEN_cons(first_rest_len)) in $A.CELLS_EQ_refl() end)
     | TAKE_LAST_drop(_, second_rest) =>
       (case+ output_len of
        | $A.CLEN_cons(rest_len) =>
          (case+ _take_last_functional(rest_len, first_rest, second_rest) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl())))

primplement window_functional {output,first,second} (first_window, second_window) =
  (case+ first_window of
   | WINDOW_mk(first_taken) =>
     (case+ second_window of
      | WINDOW_mk(second_taken) => _take_last_functional(_take_last_len(first_taken), first_taken, second_taken)))

prfun _append_total {first,second:$A.cells}{n:nat} .<n>.
  (first_len: $A.CLEN(first, n)): [both:$A.cells] $A.APPEND(first, second, both) =
  case+ first_len of
  | $A.CLEN_nil() => $A.APPEND_nil()
  | $A.CLEN_cons(rest_len) => $A.APPEND_cons(_append_total(rest_len))

prfun _append_sized_clen {first,second,both:$A.cells}{n,m:nat} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n), second_len: $A.CLEN(second, m)): $A.CLEN(both, n + m) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => second_len
  | $A.APPEND_SIZED_cons(appended_rest) => $A.CLEN_cons(_append_sized_clen(appended_rest, second_len))

prfn _append_clen {first,second,both:$A.cells}{n,m:nat}
  (appended: $A.APPEND(first, second, both), first_len: $A.CLEN(first, n), second_len: $A.CLEN(second, m)): $A.CLEN(both, n + m) =
  case+ appended of
  | $A.APPEND_made(sized) =>
    (let
       prval () = _clen_functional(first_len, _append_sized_len(sized))
     in _append_sized_clen(sized, second_len) end)

prfun _nth_in_append_left {first,second,both:$A.cells}{i,n:nat}{value:int} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n), found: $A.NTH(first, i, value)): $A.NTH(both, i, value) =
  case+ found of
  | $A.NTH_here() => (case+ appended of $A.APPEND_SIZED_cons(_) => $A.NTH_here())
  | $A.NTH_there(found_rest) => (case+ appended of $A.APPEND_SIZED_cons(appended_rest) => $A.NTH_there(_nth_in_append_left(appended_rest, found_rest)))

prfun _nth_in_append_right {first,second,both:$A.cells}{i,n:nat}{value:int} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n), found: $A.NTH(second, i, value)): $A.NTH(both, n + i, value) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => found
  | $A.APPEND_SIZED_cons(appended_rest) => $A.NTH_there(_nth_in_append_right(appended_rest, found))

primplement buffer_nth {previous,chunk,consumed}{start,index,value} (buffer, found) =
  (case+ buffer of
   | BUFFER_AT_mk(previous_len, appended) =>
     (case+ appended of
      | $A.APPEND_made(sized) =>
        (let prval () = _clen_functional(previous_len, _append_sized_len(sized)) in _nth_in_append_right(sized, found) end)))

prfun _bit_in_whole {earlier,rest,whole:$A.cells}{p,n:nat}{bit:nat} .<>.
  (appended: $A.APPEND_SIZED(earlier, rest, whole, n), found: BIT(earlier, p, bit)): BIT(whole, p, bit) =
  (case+ found of BIT_mk(found_nth, found_byte_bit) => BIT_mk(_nth_in_append_left(appended, found_nth), found_byte_bit))

prfun _bits_in_whole {earlier,rest,whole:$A.cells}{p,width,value,n:nat} .<width>.
  (appended: $A.APPEND_SIZED(earlier, rest, whole, n), bits: BITS(earlier, p, width, value)): BITS(whole, p, width, value) =
  case+ bits of
  | BITS_nil() => BITS_nil()
  | BITS_cons(bit, bits_rest) => BITS_cons(_bit_in_whole(appended, bit), _bits_in_whole(appended, bits_rest))

primplement bits_in_prefix {earlier,rest,whole}{p,width,value} (appended, bits) =
  (case+ appended of $A.APPEND_made(sized) => _bits_in_whole(sized, bits))

prfun _hbits_in_whole {earlier,rest,whole:$A.cells}{p,width,code,n:nat} .<width>.
  (appended: $A.APPEND_SIZED(earlier, rest, whole, n), bits: HBITS(earlier, p, width, code)): HBITS(whole, p, width, code) =
  case+ bits of
  | HBITS_nil() => HBITS_nil()
  | HBITS_snoc(bits_rest, bit) => HBITS_snoc(_hbits_in_whole(appended, bits_rest), _bit_in_whole(appended, bit))

primplement hbits_in_prefix {earlier,rest,whole}{p,width,code} (appended, bits) =
  (case+ appended of $A.APPEND_made(sized) => _hbits_in_whole(sized, bits))

dataprop _TAILWIN($A.cells, $A.cells, int) =
  | {window:$A.cells}{keep,count:nat} _TAILWIN_whole(window, window, keep) of $A.CLEN(window, count)
  | {pre,window,output:$A.cells}{keep,count:nat | keep <= count} _TAILWIN_cut(output, window, keep) of ($A.APPEND(pre, window, output), $A.CLEN(window, count))

dataprop _TAKE_BOTH($A.cells, $A.cells, int, $A.cells) =
  | {window,output,nw:$A.cells}{keep:nat} _TAKE_BOTH_mk(window, output, keep, nw) of (TAKE_LAST(window, keep, nw), TAKE_LAST(output, keep, nw))

prfun _append_assoc {a,b,ab,c,abc,bc:$A.cells}{n:nat} .<n>.
  (first: $A.APPEND_SIZED(a, b, ab, n), second: $A.APPEND(ab, c, abc), third: $A.APPEND(b, c, bc)): $A.APPEND(a, bc, abc) =
  case+ first of
  | $A.APPEND_SIZED_nil() => (case+ $A.append_functional(second, third) of $A.CELLS_EQ_refl() => $A.APPEND_nil())
  | $A.APPEND_SIZED_cons(first_rest) =>
    (case+ second of
     | $A.APPEND_made(second_sized) =>
       (case+ second_sized of
        | $A.APPEND_SIZED_cons(second_rest) => $A.APPEND_cons(_append_assoc(first_rest, $A.APPEND_made(second_rest), third))))

prfun _tailwin_of_take_last {output,window:$A.cells}{keep,n:nat} .<n>.
  (output_len: $A.CLEN(output, n), taken: TAKE_LAST(output, keep, window)): _TAILWIN(output, window, keep) =
  case+ taken of
  | TAKE_LAST_short(short_len) => _TAILWIN_whole(short_len)
  | TAKE_LAST_drop(rest_len, rest_taken) =>
    (case+ output_len of
     | $A.CLEN_cons(output_rest_len) =>
       (case+ _tailwin_of_take_last(output_rest_len, rest_taken) of
        | _TAILWIN_whole(_) => _TAILWIN_cut($A.APPEND_cons($A.APPEND_nil()), rest_len)
        | _TAILWIN_cut(pre_append, window_len) => _TAILWIN_cut($A.APPEND_cons(pre_append), window_len)))

prfun _take_last_prepend {pre,window,output,nw:$A.cells}{keep,count,m:nat | keep <= count} .<m>.
  (appended: $A.APPEND_SIZED(pre, window, output, m), window_len: $A.CLEN(window, count), taken: TAKE_LAST(window, keep, nw)): TAKE_LAST(output, keep, nw) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => taken
  | $A.APPEND_SIZED_cons(appended_rest) => TAKE_LAST_drop(_append_sized_clen(appended_rest, window_len), _take_last_prepend(appended_rest, window_len, taken))

prfn _tailwin_take_last {output,window:$A.cells}{keep:nat}
  (tail: _TAILWIN(output, window, keep)): [nw:$A.cells] _TAKE_BOTH(window, output, keep, nw) =
  case+ tail of
  | _TAILWIN_whole(window_len) => (case+ _take_last_total(window_len) of window_taken => _TAKE_BOTH_mk(window_taken, window_taken))
  | _TAILWIN_cut(pre_append, window_len) =>
    (case+ pre_append of
     | $A.APPEND_made(pre_sized) =>
       (case+ _take_last_total(window_len) of window_taken => _TAKE_BOTH_mk(window_taken, _take_last_prepend(pre_sized, window_len, window_taken))))

prfn _tailwin_window_len {output,window:$A.cells}{keep:nat}
  (tail: _TAILWIN(output, window, keep)): [w:nat] $A.CLEN(window, w) =
  case+ tail of
  | _TAILWIN_whole(window_len) => window_len
  | _TAILWIN_cut(_, window_len) => window_len

prfn _tailwin_append {output,window,data,next,both:$A.cells}{keep,count:nat}
  (tail: _TAILWIN(output, window, keep), output_append: $A.APPEND(output, data, next), window_append: $A.APPEND(window, data, both), data_len: $A.CLEN(data, count))
  : _TAILWIN(next, both, keep) =
  case+ tail of
  | _TAILWIN_whole(window_len) =>
    (case+ $A.append_functional(output_append, window_append) of
     | $A.CELLS_EQ_refl() => _TAILWIN_whole(_append_clen(window_append, window_len, data_len)))
  | _TAILWIN_cut(pre_append, window_len) =>
    (case+ pre_append of
     | $A.APPEND_made(pre_sized) => _TAILWIN_cut(_append_assoc(pre_sized, output_append, window_append), _append_clen(window_append, window_len, data_len)))

primplement window_append {output,window,data,next}{count} (window_proof, output_append, data_len) =
  (case+ window_proof of
   | WINDOW_mk(taken) =>
     (let
        prval output_len = _take_last_len(taken)
        prval tail = _tailwin_of_take_last(output_len, taken)
        prval window_len = _tailwin_window_len(tail)
        prval window_append = _append_total(window_len)
        prval tail_after = _tailwin_append(tail, output_append, window_append, data_len)
      in
        (case+ _tailwin_take_last(tail_after) of
         | _TAKE_BOTH_mk(both_taken, next_taken) => WINDOW_AFTER_APPEND_mk(window_append, both_taken, WINDOW_mk(next_taken)))
      end))

prfun _nth_in_tail {pre,window,output:$A.cells}{i,m:nat | m <= i}{value:int} .<m>.
  (appended: $A.APPEND_SIZED(pre, window, output, m), found: $A.NTH(output, i, value)): $A.NTH(window, i - m, value) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => found
  | $A.APPEND_SIZED_cons(appended_rest) =>
    (case+ found of $A.NTH_there(found_rest) => _nth_in_tail(appended_rest, found_rest))

prfn _window_nth {output,window:$A.cells}{keep,n,distance:nat | 1 <= distance; distance <= n; distance <= keep}{w:nat}{value:int}
  (tail: _TAILWIN(output, window, keep), output_len: $A.CLEN(output, n), window_len: $A.CLEN(window, w), found: $A.NTH(output, n - distance, value))
  : [distance <= w] $A.NTH(window, w - distance, value) =
  case+ tail of
  | _TAILWIN_whole(whole_len) =>
    (let
       prval () = _clen_functional(whole_len, window_len)
       prval () = _clen_functional(output_len, window_len)
     in found end)
  | _TAILWIN_cut(pre_append, cut_len) =>
    (case+ pre_append of
     | $A.APPEND_made(pre_sized) =>
       (let
          prval () = _clen_functional(cut_len, window_len)
          prval () = _clen_functional(output_len, _append_sized_clen(pre_sized, window_len))
        in _nth_in_tail(pre_sized, found) end))

dataprop _COPY_IN($A.cells, int, int, $A.cells, int) =
  | {window,after,both:$A.cells}{distance,length,keep:nat} _COPY_IN_mk(window, distance, length, after, keep) of (COPY(window, distance, length, both), _TAILWIN(after, both, keep))

prfun _copy_in_window {output,window,after:$A.cells}{keep,distance,length,n:nat | distance <= keep} .<length>.
  (tail: _TAILWIN(output, window, keep), output_len: $A.CLEN(output, n), copied: COPY(output, distance, length, after))
  : _COPY_IN(window, distance, length, after, keep) =
  case+ copied of
  | COPY_done() => _COPY_IN_mk(COPY_done(), tail)
  | COPY_step(step_len, step_nth, step_append, step_rest) =>
    (let
       prval () = _clen_functional(step_len, output_len)
       prval window_len = _tailwin_window_len(tail)
       prval window_nth = _window_nth{output,window}{keep,n,distance}(tail, output_len, window_len, step_nth)
       prval window_append = _append_total(window_len)
       prval one_len = $A.CLEN_cons($A.CLEN_nil())
       prval tail_after = _tailwin_append(tail, step_append, window_append, one_len)
       prval next_len = _append_clen(step_append, output_len, one_len)
     in
       (case+ _copy_in_window(tail_after, next_len, step_rest) of
        | _COPY_IN_mk(rest_copy, rest_tail) => _COPY_IN_mk(COPY_step(window_len, window_nth, window_append, rest_copy), rest_tail))
     end)

primplement window_copy {output,window,after}{distance,length} (window_proof, copied) =
  (case+ window_proof of
   | WINDOW_mk(taken) =>
     (let
        prval output_len = _take_last_len(taken)
        prval tail = _tailwin_of_take_last(output_len, taken)
      in
        (case+ _copy_in_window(tail, output_len, copied) of
         | _COPY_IN_mk(window_copied, tail_after) =>
           (case+ _tailwin_take_last(tail_after) of
            | _TAKE_BOTH_mk(both_taken, after_taken) => WINDOW_AFTER_COPY_mk(window_copied, both_taken, WINDOW_mk(after_taken))))
      end))

(* Ranges (the Done-when): a copy's distance is 1 to 32768 and its length
   3 to 258 *)
#pub prfun distance_range {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (DISTANCE_SYMBOL(sym, extra_bits, base), BITS(source, p, extra_bits, value)): [1 <= base + value; base + value <= 32768] void

#pub prfun length_range {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat}
  (LENGTH_SYMBOL(sym, extra_bits, base), BITS(source, p, extra_bits, value)): [3 <= base + value; base + value <= 258] void

(* Proofs of the ranges (keyword: copy-range): the extra bits value is below 2 to
   their number, and the table's bases are linear in that power *)

prfun _pow2_positive {k,power:nat} .<k>. (pow: $AR.POW2(k, power)): [1 <= power] void =
  case+ pow of
  | $AR.POW2_zero() => ()
  | $AR.POW2_succ(pow_rest) => _pow2_positive(pow_rest)

prfun _pow2_monotone {small,large,small_power,large_power:nat | small <= large} .<large>.
  (small_pow: $AR.POW2(small, small_power), large_pow: $AR.POW2(large, large_power)): [small_power <= large_power] void =
  case+ large_pow of
  | $AR.POW2_zero() => (case+ small_pow of $AR.POW2_zero() => ())
  | $AR.POW2_succ(large_rest) =>
    (case+ small_pow of
     | $AR.POW2_zero() => _pow2_positive(large_rest)
     | $AR.POW2_succ(small_rest) => _pow2_monotone(small_rest, large_rest))

prfun _bits_below_power {source:$A.cells}{p,width,value,power:nat} .<width>.
  (bits: BITS(source, p, width, value), pow: $AR.POW2(width, power)): [value < power] void =
  case+ bits of
  | BITS_nil() => (case+ pow of $AR.POW2_zero() => ())
  | BITS_cons(_, bits_rest) => (case+ pow of $AR.POW2_succ(pow_rest) => _bits_below_power(bits_rest, pow_rest))

prfn _pow2_thirty_two (): $AR.POW2(5, 32) =
  $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))

prfn _pow2_eight_thousand (): $AR.POW2(13, 8192) =
  $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ(
  $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))))))))))

prfun _distance_range {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat} .<>.
  (symbol: DISTANCE_SYMBOL(sym, extra_bits, base), bits: BITS(source, p, extra_bits, value)): [1 <= base + value; base + value <= 32768] void =
  case+ symbol of
  | DISTANCE_SYMBOL_short() => (case+ bits of BITS_nil() => ())
  | DISTANCE_SYMBOL_base_2_times(pow) => let
      prval () = _bits_below_power(bits, pow)
      prval () = _pow2_monotone(pow, _pow2_eight_thousand())
    in () end
  | DISTANCE_SYMBOL_base_3_times(pow) => let
      prval () = _bits_below_power(bits, pow)
      prval () = _pow2_monotone(pow, _pow2_eight_thousand())
    in () end

primplement distance_range {sym,extra_bits,base,value}{source}{p} (symbol, bits) = _distance_range(symbol, bits)

prfun _length_range {sym,extra_bits,base,value:nat}{source:$A.cells}{p:nat} .<>.
  (symbol: LENGTH_SYMBOL(sym, extra_bits, base), bits: BITS(source, p, extra_bits, value)): [3 <= base + value; base + value <= 258] void =
  case+ symbol of
  | LENGTH_SYMBOL_short() => (case+ bits of BITS_nil() => ())
  | LENGTH_SYMBOL_base_4_times(pow) => let
      prval () = _bits_below_power(bits, pow)
      prval () = _pow2_monotone(pow, _pow2_thirty_two())
    in () end
  | LENGTH_SYMBOL_base_5_times(pow) => let
      prval () = _bits_below_power(bits, pow)
      prval () = _pow2_monotone(pow, _pow2_thirty_two())
    in () end
  | LENGTH_SYMBOL_base_6_times(pow) => let
      prval () = _bits_below_power(bits, pow)
      prval () = _pow2_monotone(pow, _pow2_thirty_two())
    in () end
  | LENGTH_SYMBOL_base_7_times(pow) => let
      prval () = _bits_below_power(bits, pow)
      prval () = _pow2_monotone(pow, _pow2_thirty_two())
    in () end
  | LENGTH_SYMBOL_last() => (case+ bits of BITS_nil() => ())

primplement length_range {sym,extra_bits,base,value}{source}{p} (symbol, bits) = _length_range(symbol, bits)


(* ============================================================
   What inflating an entry's data gives, as a relation (quire#608, INFLATES)
   ============================================================ *)

(* How an entry's data is stored, as a static index: the method field 0
   (stored) or 8 (deflated), as `compression` is its dynamic form *)
#pub datasort inflate_kind =
  | inflate_stored of ()
  | inflate_deflated of ()

(* cells and cells are the same cells: the one constructor is the only way
   to have it, so a lemma's conclusion that two outputs are the same is
   this *)
#pub dataprop CELLS_EQ($A.cells, $A.cells) =
  | {cs:$A.cells} CELLS_EQ_refl(cs, cs)

(* INFLATES(kind, compressed, output): the entry's data, whose cells are
   compressed, inflates to the cells output by the method kind. The stored
   method (APPNOTE 4.4.5, method 0) keeps the bytes as they are. The
   Deflated method's constructors are added by the pieces of quire#608
   that follow (RFC 1951) *)
#pub dataprop INFLATES(inflate_kind, $A.cells, $A.cells) =
  | {cs:$A.cells} INFLATES_stored(inflate_stored(), cs, cs)
  (* the Deflate stream (RFC 1951) from bit 0, with no output before it *)
  | {compressed,output:$A.cells} INFLATES_deflated(inflate_deflated(), compressed, output) of BLOCKS(compressed, 0, $A.cnil(), output)

(* The same compressed cells, by the same method, inflate to the same
   output cells *)
#pub prfun inflates_functional {kind:inflate_kind}{compressed,first,second:$A.cells}
  (INFLATES(kind, compressed, first), INFLATES(kind, compressed, second)): CELLS_EQ(first, second)

primplement inflates_functional {kind}{compressed,first,second} (first_proof, second_proof) =
  case+ first_proof of
  | INFLATES_stored() => (case+ second_proof of INFLATES_stored() => CELLS_EQ_refl())
  | INFLATES_deflated(first_blocks) =>
    (case+ second_proof of
     | INFLATES_deflated(second_blocks) =>
       (case+ blocks_functional(first_blocks, second_blocks) of $A.CELLS_EQ_refl() => CELLS_EQ_refl()))
