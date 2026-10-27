(* zip -- ZIP central directory parser *)
(* Finds an archive's entries by reading only the ranges each step names.
   Pure computation. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* file is used by the reader and writer forms only, so a wasm build of zip never names it (keyword: decoder) *)
#target native begin

#use file as F

end (* native *)

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

(* The relations are followed by the decoders that return them (keyword: decoder, CLAUDE.md). *)

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

(* ============================================================
   The decoders that return the proof (zip#64, keyword: decoder)
   ============================================================ *)

(* ===== decoder lemmas, batch 1 ===== *)

prfun nth_of_append_left {first,second,both:$A.cells}{i,n:nat | i < n}{value:int} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n), found: $A.NTH(both, i, value)): $A.NTH(first, i, value) =
  case+ appended of
  | $A.APPEND_SIZED_cons(appended_rest) =>
    (case+ found of
     | $A.NTH_here() => $A.NTH_here()
     | $A.NTH_there(found_rest) => $A.NTH_there(nth_of_append_left(appended_rest, found_rest)))

prfun nth_of_append_right {first,second,both:$A.cells}{i,n:nat}{value:int} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n), found: $A.NTH(both, n + i, value)): $A.NTH(second, i, value) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => found
  | $A.APPEND_SIZED_cons(appended_rest) =>
    (case+ found of $A.NTH_there(found_rest) => nth_of_append_right(appended_rest, found_rest))

(* setting the cell right after the first part of an append extends the first part by that cell *)
prfun append_setc {first,second,both,both2:$A.cells}{m,n:nat}{x:int} .<m>.
  (first_len: $A.CLEN(first, m), appended: $A.APPEND_SIZED(first, second, both, n), set: $A.SETC(both, m, x, both2))
  : [next,second2:$A.cells] ($A.APPEND(first, $A.ccons(x, $A.cnil()), next), $A.APPEND(next, second2, both2)) =
  case+ first_len of
  | $A.CLEN_nil() =>
    (case+ appended of
     | $A.APPEND_SIZED_nil() =>
       (case+ set of
        | $A.SETC_here() => ($A.APPEND_nil(), $A.APPEND_cons($A.APPEND_nil()))))
  | $A.CLEN_cons(first_rest_len) =>
    (case+ appended of
     | $A.APPEND_SIZED_cons(appended_rest) =>
       (case+ set of
        | $A.SETC_there(set_rest) =>
          (let prval (snoc, rest) = append_setc(first_rest_len, appended_rest, set_rest)
           in ($A.APPEND_cons(snoc), $A.APPEND_cons(rest)) end)))

(* the first part of an append is also the first part of what follows it, composed *)
prfun append_compose {first,second,both,third,whole:$A.cells}{n:nat} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n), followed: $A.APPEND(both, third, whole))
  : [tail:$A.cells] ($A.APPEND(second, third, tail), $A.APPEND(first, tail, whole)) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => (followed, $A.APPEND_nil())
  | $A.APPEND_SIZED_cons(appended_rest) =>
    (case+ followed of
     | $A.APPEND_made(followed_sized) =>
       (case+ followed_sized of
        | $A.APPEND_SIZED_cons(followed_rest) =>
          (let prval (tail_append, whole_append) = append_compose(appended_rest, $A.APPEND_made(followed_rest))
           in (tail_append, $A.APPEND_cons(whole_append)) end)))

prfun append_nil_right {first,both:$A.cells}{n:nat} .<n>.
  (appended: $A.APPEND_SIZED(first, $A.cnil(), both, n)): $A.CELLS_EQ(first, both) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => $A.CELLS_EQ_refl()
  | $A.APPEND_SIZED_cons(appended_rest) =>
    (case+ append_nil_right(appended_rest) of $A.CELLS_EQ_refl() => $A.CELLS_EQ_refl())

(* EXT(first, whole): whole is first and then more cells, how a source grows when the reader gives more *)
dataprop EXT($A.cells, $A.cells) =
  | {first,rest,whole:$A.cells} EXT_mk(first, whole) of $A.APPEND(first, rest, whole)

prfun append_nil_refl {cells:$A.cells}{n:nat} .<>. (cells_len: $A.CLEN(cells, n)): $A.APPEND(cells, $A.cnil(), cells) =
  (case+ _append_total{cells,$A.cnil()}(cells_len) of
   | $A.APPEND_made(sized) => (case+ append_nil_right(sized) of $A.CELLS_EQ_refl() => $A.APPEND_made(sized)))

prfun ext_refl {cells:$A.cells}{n:nat} .<>. (cells_len: $A.CLEN(cells, n)): EXT(cells, cells) =
  (case+ _append_total{cells,$A.cnil()}(cells_len) of
   | $A.APPEND_made(sized) =>
     (case+ append_nil_right(sized) of $A.CELLS_EQ_refl() => EXT_mk($A.APPEND_made(sized))))

prfun ext_trans {first,second,whole:$A.cells} .<>. (left: EXT(first, second), right: EXT(second, whole)): EXT(first, whole) =
  (case+ left of
   | EXT_mk($A.APPEND_made(left_sized)) =>
     (case+ right of
      | EXT_mk(right_append) =>
        (let prval (_, composed) = append_compose(left_sized, right_append) in EXT_mk(composed) end)))

prfun bit_in_ext {earlier,whole:$A.cells}{p,bit:nat} .<>. (ext: EXT(earlier, whole), found: BIT(earlier, p, bit)): BIT(whole, p, bit) =
  (case+ ext of EXT_mk($A.APPEND_made(sized)) => _bit_in_whole(sized, found))

prfun bits_in_ext {earlier,whole:$A.cells}{p,width,value:nat} .<>. (ext: EXT(earlier, whole), bits: BITS(earlier, p, width, value)): BITS(whole, p, width, value) =
  (case+ ext of EXT_mk(appended) => bits_in_prefix(appended, bits))

prfun hbits_in_ext {earlier,whole:$A.cells}{p,width,code:nat} .<>. (ext: EXT(earlier, whole), bits: HBITS(earlier, p, width, code)): HBITS(whole, p, width, code) =
  (case+ ext of EXT_mk(appended) => hbits_in_prefix(appended, bits))

prfun nth_in_ext {earlier,whole:$A.cells}{i:nat}{value:int} .<>. (ext: EXT(earlier, whole), found: $A.NTH(earlier, i, value)): $A.NTH(whole, i, value) =
  (case+ ext of EXT_mk($A.APPEND_made(sized)) => _nth_in_append_left(sized, found))

(* counting, one more length at a time *)
prfun count_before_snoc_hit {lengths:$A.cells}{until:nat}{len:int}{count:nat} .<until>.
  (counted: COUNT_BEFORE(lengths, until, len, count), found: $A.NTH(lengths, until, len)): COUNT_BEFORE(lengths, until + 1, len, count + 1) =
  case+ counted of
  | COUNT_BEFORE_zero() => (case+ found of $A.NTH_here() => COUNT_BEFORE_hit(COUNT_BEFORE_zero()))
  | COUNT_BEFORE_hit(counted_rest) => (case+ found of $A.NTH_there(found_rest) => COUNT_BEFORE_hit(count_before_snoc_hit(counted_rest, found_rest)))
  | COUNT_BEFORE_miss(counted_rest) => (case+ found of $A.NTH_there(found_rest) => COUNT_BEFORE_miss(count_before_snoc_hit(counted_rest, found_rest)))

prfun count_before_snoc_miss {lengths:$A.cells}{until:nat}{len,other:int | other != len}{count:nat} .<until>.
  (counted: COUNT_BEFORE(lengths, until, len, count), found: $A.NTH(lengths, until, other)): COUNT_BEFORE(lengths, until + 1, len, count) =
  case+ counted of
  | COUNT_BEFORE_zero() => (case+ found of $A.NTH_here() => COUNT_BEFORE_miss(COUNT_BEFORE_zero()))
  | COUNT_BEFORE_hit(counted_rest) => (case+ found of $A.NTH_there(found_rest) => COUNT_BEFORE_hit(count_before_snoc_miss(counted_rest, found_rest)))
  | COUNT_BEFORE_miss(counted_rest) => (case+ found of $A.NTH_there(found_rest) => COUNT_BEFORE_miss(count_before_snoc_miss(counted_rest, found_rest)))

(* ===== batch 3: code lengths seen by index ===== *)

prfun run_len {count,rest_count:nat}{value:int}{rest,all:$A.cells} .<count>.
  (run: RUN(count, value, rest, all), rest_len: $A.CLEN(rest, rest_count)): $A.CLEN(all, count + rest_count) =
  case+ run of
  | RUN_zero() => rest_len
  | RUN_cons(run_rest) => $A.CLEN_cons(run_len(run_rest, rest_len))

prfun run_nth_inside {count,index:nat | index < count}{value:int}{rest,all:$A.cells} .<count>.
  (run: RUN(count, value, rest, all)): $A.NTH(all, index, value) =
  case+ run of
  | RUN_cons(run_rest) =>
    sif index == 0 then $A.NTH_here()
    else $A.NTH_there(run_nth_inside{count-1,index-1}(run_rest))

prfun run_nth_after {count,index:nat}{value,found:int}{rest,all:$A.cells} .<count>.
  (run: RUN(count, value, rest, all), found_rest: $A.NTH(rest, index, found)): $A.NTH(all, count + index, found) =
  case+ run of
  | RUN_zero() => found_rest
  | RUN_cons(run_rest) => $A.NTH_there(run_nth_after(run_rest, found_rest))

fn fixed_litlen_length {lengths:$A.cells}{i:nat | i < 288} (fixed: FIXED_LITLEN(lengths) | i: int i)
  : [v:nat | v < 256] ($A.NTH(lengths, i, v) | int v) = let
  prval FIXED_LITLEN_mk(run_first, run_second, run_third, run_fourth) = fixed
in
  if i < 144 then (run_nth_inside{144,i}(run_first) | 8)
  else if i < 256 then (run_nth_after(run_first, run_nth_inside{112,i-144}(run_second)) | 9)
  else if i < 280 then (run_nth_after(run_first, run_nth_after(run_second, run_nth_inside{24,i-256}(run_third))) | 7)
  else (run_nth_after(run_first, run_nth_after(run_second, run_nth_after(run_third, run_nth_inside{8,i-280}(run_fourth)))) | 8)
end

fn fixed_dist_length {lengths:$A.cells}{i:nat | i < 32} (fixed: FIXED_DIST(lengths) | i: int i)
  : [v:nat | v < 256] ($A.NTH(lengths, i, v) | int v) = let
  prval FIXED_DIST_mk(run) = fixed
in (run_nth_inside{32,i}(run) | 5) end

(* The code lengths of an alphabet of n symbols, read by symbol: the fixed codes' by their runs (3.2.6), the
   others' from an array of 320 lengths (a block's literal/length and distance lengths), starting at offset *)
datavtype lengths_view($A.cells, int) =
  | {lengths:$A.cells} lengths_of_fixed_litlen(lengths, 288) of (FIXED_LITLEN(lengths), $A.CLEN(lengths, 288) | )
  | {lengths:$A.cells} lengths_of_fixed_dist(lengths, 32) of (FIXED_DIST(lengths), $A.CLEN(lengths, 32) | )
  | {lengths,junk,cells:$A.cells}{l:agz}{n:nat | n <= 320} lengths_of_array(lengths, n) of ($A.CLEN(lengths, n), $A.APPEND(lengths, junk, cells) | $A.barr(l, 320, cells))

fn length_at {lengths:$A.cells}{n,i:nat | i < n} (view: !lengths_view(lengths, n), i: int i)
  : [v:nat | v < 256] ($A.NTH(lengths, i, v) | int v) =
  case+ view of
  | @lengths_of_fixed_litlen(fixed, fixed_len | ) => let val r = fixed_litlen_length(fixed | i) in fold@(view); r end
  | @lengths_of_fixed_dist(fixed, fixed_len | ) => let val r = fixed_dist_length(fixed | i) in fold@(view); r end
  | @lengths_of_array(lengths_len, appended | array) => let
      val (found | v) = $A.barr_get(array, i)
      prval $A.APPEND_made(sized) = appended
      prval () = _clen_functional(lengths_len, _append_sized_len(sized))
      val r = (nth_of_append_left(sized, found) | v)
    in fold@(view); r end

fn lengths_len {lengths:$A.cells}{n:nat} (view: !lengths_view(lengths, n)): ($A.CLEN(lengths, n) | void) =
  case+ view of
  | @lengths_of_fixed_litlen(fixed, fixed_len | ) => let val r = (fixed_len | ()) in fold@(view); r end
  | @lengths_of_fixed_dist(fixed, fixed_len | ) => let val r = (fixed_len | ()) in fold@(view); r end
  | @lengths_of_array(lengths_len, appended | array) => let val r = (lengths_len | ()) in fold@(view); r end

(* ===== batch 4: the tables of a code ===== *)

dataprop AT_MOST_UPTO($A.cells, int, int) =
  | {lengths:$A.cells}{maxlen:nat} AT_MOST_UPTO_zero(lengths, 0, maxlen)
  | {rest:$A.cells}{until,maxlen,len:nat | len <= maxlen} AT_MOST_UPTO_cons($A.ccons(len, rest), until + 1, maxlen) of AT_MOST_UPTO(rest, until, maxlen)

prfun at_most_upto_snoc {lengths:$A.cells}{until,maxlen,len:nat | len <= maxlen} .<until>.
  (upto: AT_MOST_UPTO(lengths, until, maxlen), found: $A.NTH(lengths, until, len)): AT_MOST_UPTO(lengths, until + 1, maxlen) =
  case+ upto of
  | AT_MOST_UPTO_zero() => (case+ found of $A.NTH_here() => AT_MOST_UPTO_cons(AT_MOST_UPTO_zero()))
  | AT_MOST_UPTO_cons(upto_rest) => (case+ found of $A.NTH_there(found_rest) => AT_MOST_UPTO_cons(at_most_upto_snoc(upto_rest, found_rest)))

prfun at_most_of_upto {lengths:$A.cells}{n,maxlen:nat} .<n>.
  (lengths_len: $A.CLEN(lengths, n), upto: AT_MOST_UPTO(lengths, n, maxlen)): AT_MOST(lengths, maxlen) =
  case+ lengths_len of
  | $A.CLEN_nil() => AT_MOST_nil()
  | $A.CLEN_cons(rest_len) => (case+ upto of AT_MOST_UPTO_cons(upto_rest) => AT_MOST_cons(at_most_of_upto(rest_len, upto_rest)))

fun at_most_scan {lengths:$A.cells}{n,maxlen,i:nat | i <= n} .<n - i>.
  (upto: AT_MOST_UPTO(lengths, i, maxlen) | view: !lengths_view(lengths, n), n: int n, maxlen: int maxlen, i: int i)
  : [ok:bool] (option_v(AT_MOST_UPTO(lengths, n, maxlen), ok) | bool ok) =
  if i >= n then (Some_v(upto) | true)
  else let
    val (found | v) = length_at(view, i)
  in
    if v <= maxlen then at_most_scan(at_most_upto_snoc(upto, found) | view, n, maxlen, i + 1)
    else (None_v() | false)
  end

fun count_scan {lengths:$A.cells}{n:nat}{len:int}{i,c:nat | i <= n} .<n - i>.
  (counted: COUNT_BEFORE(lengths, i, len, c) | view: !lengths_view(lengths, n), n: int n, len: int len, i: int i, c: int c)
  : [count:nat] (COUNT_BEFORE(lengths, n, len, count) | int count) =
  if i >= n then (counted | c)
  else let
    val (found | v) = length_at(view, i)
  in
    if v = len then count_scan(count_before_snoc_hit(counted, found) | view, n, len, i + 1, c + 1)
    else count_scan(count_before_snoc_miss(counted, found) | view, n, len, i + 1, c)
  end

(* 2 to the k, for the lengths a code can have, with a bound that keeps first codes in a C int *)
fn pow2_of {k:nat | k <= 15} (k: int k): [p:nat | 1 <= p; p <= 32768] ($AR.POW2(k, p) | int p) =
  if k = 0 then ($AR.POW2_zero() | 1)
  else if k = 1 then ($AR.POW2_succ($AR.POW2_zero()) | 2)
  else if k = 2 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())) | 4)
  else if k = 3 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))) | 8)
  else if k = 4 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))) | 16)
  else if k = 5 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))) | 32)
  else if k = 6 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))) | 64)
  else if k = 7 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))))) | 128)
  else if k = 8 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))))) | 256)
  else if k = 9 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))))))) | 512)
  else if k = 10 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))))))) | 1024)
  else if k = 11 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))))))))) | 2048)
  else if k = 12 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))))))))) | 4096)
  else if k = 13 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))))))))))) | 8192)
  else if k = 14 then ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))))))))))) | 16384)
  else ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))))))))))))) | 32768)

(* TABLE_UPTO(lengths, firsts, counts, upto): for each length 1 to upto, the array firsts holds next_code and the array counts bl_count (3.2.2) *)
dataprop TABLE_UPTO($A.cells, $A.cells, $A.cells, int) =
  | {lengths,firsts,counts:$A.cells} TABLE_UPTO_zero(lengths, firsts, counts, 0)
  | {lengths,firsts,counts:$A.cells}{upto,first_code,count:nat | first_code + count <= 32768}
    TABLE_UPTO_step(lengths, firsts, counts, upto + 1)
    of (TABLE_UPTO(lengths, firsts, counts, upto), $A.NTH(firsts, upto + 1, first_code), $A.NTH(counts, upto + 1, count),
        NEXT_CODE(lengths, upto + 1, first_code), BL_COUNT(lengths, upto + 1, count))

prfun table_lookup {lengths,firsts,counts:$A.cells}{upto,len:nat | 1 <= len; len <= upto}{first_code,count:int} .<upto>.
  (table: TABLE_UPTO(lengths, firsts, counts, upto), first_found: $A.NTH(firsts, len, first_code), count_found: $A.NTH(counts, len, count))
  : [0 <= first_code; 0 <= count; first_code + count <= 32768] (NEXT_CODE(lengths, len, first_code), BL_COUNT(lengths, len, count)) =
  case+ table of
  | TABLE_UPTO_step(table_rest, step_first, step_count, step_next, step_bl) =>
    sif len == upto then
      (let
         prval () = $A.nth_functional(first_found, step_first)
         prval () = $A.nth_functional(count_found, step_count)
       in (step_next, step_bl) end)
    else table_lookup{lengths,firsts,counts}{upto-1,len}{first_code,count}(table_rest, first_found, count_found)

prfun table_setc_firsts {lengths,firsts,firsts2,counts:$A.cells}{upto,index:nat | upto < index}{value:int} .<upto>.
  (table: TABLE_UPTO(lengths, firsts, counts, upto), set: $A.SETC(firsts, index, value, firsts2)): TABLE_UPTO(lengths, firsts2, counts, upto) =
  case+ table of
  | TABLE_UPTO_zero() => TABLE_UPTO_zero()
  | TABLE_UPTO_step(table_rest, step_first, step_count, step_next, step_bl) =>
    TABLE_UPTO_step(table_setc_firsts(table_rest, set), $A.setc_nth_other(set, step_first), step_count, step_next, step_bl)

prfun table_setc_counts {lengths,firsts,counts,counts2:$A.cells}{upto,index:nat | upto < index}{value:int} .<upto>.
  (table: TABLE_UPTO(lengths, firsts, counts, upto), set: $A.SETC(counts, index, value, counts2)): TABLE_UPTO(lengths, firsts, counts2, upto) =
  case+ table of
  | TABLE_UPTO_zero() => TABLE_UPTO_zero()
  | TABLE_UPTO_step(table_rest, step_first, step_count, step_next, step_bl) =>
    TABLE_UPTO_step(table_setc_counts(table_rest, set), step_first, $A.setc_nth_other(set, step_count), step_next, step_bl)

prfn table_extend {lengths,firsts,firsts2,counts,counts2:$A.cells}{upto,first_code,count:nat | first_code + count <= 32768}
  (table: TABLE_UPTO(lengths, firsts, counts, upto), set_first: $A.SETC(firsts, upto + 1, first_code, firsts2), set_count: $A.SETC(counts, upto + 1, count, counts2),
   next: NEXT_CODE(lengths, upto + 1, first_code), bl: BL_COUNT(lengths, upto + 1, count)): TABLE_UPTO(lengths, firsts2, counts2, upto + 1) =
  TABLE_UPTO_step(table_setc_counts(table_setc_firsts(table, set_first), set_count), $A.setc_nth_same(set_first), $A.setc_nth_same(set_count), next, bl)

(* the tables of a code of lengths none over maxlen *)
datavtype tables($A.cells, int) =
  | {lengths,firsts,counts:$A.cells}{maxlen:nat}{l1,l2:agz}
    tables_made(lengths, maxlen) of (TABLE_UPTO(lengths, firsts, counts, maxlen), LEN_FIT(lengths, maxlen) | $A.iarr(l1, 16, firsts), $A.iarr(l2, 16, counts))

(* the tables, or the answer that the code is over-subscribed *)
datavtype build_result($A.cells, int) =
  | {lengths:$A.cells}{maxlen:nat} build_made(lengths, maxlen) of (tables(lengths, maxlen))
  | {lengths:$A.cells}{maxlen:nat} build_over_subscribed(lengths, maxlen) of ()

fun build_loop {lengths:$A.cells}{n,maxlen,len:nat | len <= maxlen; maxlen <= 15}{firsts,counts:$A.cells}{l1,l2:agz}{first_code:nat | first_code <= 65536} .<maxlen - len>.
  (table: TABLE_UPTO(lengths, firsts, counts, len), fit: LEN_FIT(lengths, len), next: NEXT_CODE(lengths, len + 1, first_code) |
   view: !lengths_view(lengths, n), firsts: $A.iarr(l1, 16, firsts), counts: $A.iarr(l2, 16, counts), n: int n, maxlen: int maxlen, len: int len, first_code: int first_code)
  : build_result(lengths, maxlen) =
  if len >= maxlen then build_made(tables_made(table, fit | firsts, counts))
  else let
    val (counted | count) = count_scan(COUNT_BEFORE_zero() | view, n, len + 1, 0, 0)
    val (lengths_len | ()) = lengths_len(view)
    prval bl = BL_COUNT_mk(lengths_len, counted)
    val (pow_pf | power) = pow2_of(len + 1)
  in
    if first_code + count <= power then let
      val (set_first | firsts2) = $A.iarr_set(firsts, len + 1, first_code)
      val (set_count | counts2) = $A.iarr_set(counts, len + 1, count)
      prval table2 = table_extend(table, set_first, set_count, next, bl)
      prval fit2 = LEN_FIT_step(fit, next, bl, pow_pf)
      prval next2 = NEXT_CODE_next(next, bl)
    in build_loop(table2, fit2, next2 | view, firsts2, counts2, n, maxlen, len + 1, 2 * (first_code + count)) end
    else let
      val () = $A.iarr_free(firsts)
      val () = $A.iarr_free(counts)
    in build_over_subscribed() end
  end

#target native begin

(* what a file input is: the reader, a buffer holding the last chunk read, and where that chunk starts (native only) *)
datavtype external_input($A.cells, int, int, int, int) =
  | {source,previous,chunk,buffer:$A.cells}{front,count,have,first_byte,size_in:nat | have == front + count; have <= size_in; count <= 16384}{lb:agz}
    external_reading(source, front, have, first_byte, size_in)
    of ($A.CLEN(chunk, count), $A.HOLDS(buffer, chunk), $A.CLEN(previous, front), $A.APPEND(previous, chunk, source) |
        $F.content_reader(source, first_byte, size_in), $A.barr(lb, 16384, buffer))
  | {source:$A.cells}{have,first_byte,size_in:nat}
    external_limit(source, have, have, first_byte, size_in) of ($F.FILE_READ(source, first_byte, size_in), $A.CLEN(source, size_in), $A.CLEN(source, have) | )
  | {source:$A.cells}{have,first_byte,size_in:nat} external_eof(source, have, have, first_byte, size_in) of ($F.FILE_READ(source, first_byte, size_in), $A.CLEN(source, have) | )
  | {source:$A.cells}{have,first_byte,size_in:nat} external_failed(source, have, have, first_byte, size_in) of ($A.CLEN(source, have) | $F.io_error)
  | {source:$A.cells}{have,first_byte,size_in:nat} external_overrun(source, have, have, first_byte, size_in) of ($A.CLEN(source, have) | )


(* The compressed bytes consumed so far are the cells source; the byte at index front and the bytes up to have are readable
   without reading more; the entry's data is size_in bytes from first_byte of its file. A memory input holds all of them. *)
datavtype input(addr, $A.cells, int, int, int, int) =
  | {source:$A.cells}{have:pos}{l:agz} input_memory(l, source, 0, have, 0, have) of ($A.CLEN(source, have) | $A.barr(l, have, source), int have)
  | {source:$A.cells}{front,have,first_byte,size_in:nat | front <= have; have <= size_in}
    input_external(null, source, front, have, first_byte, size_in) of (int front, int have, int size_in, external_input(source, front, have, first_byte, size_in))


fn input_have {owner:addr}{source:$A.cells}{front,have,first_byte,size_in:nat} (inp: !input(owner, source, front, have, first_byte, size_in)): ($A.CLEN(source, have) | int have) =
  case+ inp of
  | @input_memory(len | cb, have) => let val r = (len | have) in fold@(inp); r end
  | @input_external(front, have, limit, ext) =>
    (case+ ext of
     | @external_reading(clen, holds, plen, app | reader, buffer) => let val r = (_append_clen(app, plen, clen) | have) in fold@(ext); fold@(inp); r end
     | @external_limit(file_read, whole_len, have_len | ) => let val r = (have_len | have) in fold@(ext); fold@(inp); r end
     | @external_eof(file_read, have_len | ) => let val r = (have_len | have) in fold@(ext); fold@(inp); r end
     | @external_failed(have_len | failure) => let val r = (have_len | have) in fold@(ext); fold@(inp); r end
     | @external_overrun(have_len | ) => let val r = (have_len | have) in fold@(ext); fold@(inp); r end)


fn input_peek {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,q:nat | front <= q; q < have}
  (inp: !input(owner, source, front, have, first_byte, size_in), q: int q): [v:nat | v < 256] ($A.NTH(source, q, v) | int v) =
  case+ inp of
  | @input_memory(len | cb, have) => let val (found | v) = $A.barr_get(cb, q) in fold@(inp); (found | v) end
  | @input_external(front, have, limit, ext) =>
    (case+ ext of
     | @external_reading(clen, holds, plen, app | reader, buffer) => let
         val (found | v) = $A.barr_get(buffer, q - front)
         prval $A.HOLDS_mk($A.APPEND_made(chunk_sized)) = holds
         prval () = _clen_functional(clen, _append_sized_len(chunk_sized))
         prval in_chunk = nth_of_append_left(chunk_sized, found)
         prval in_source = buffer_nth(BUFFER_AT_mk(plen, app), in_chunk)
       in fold@(ext); fold@(inp); (in_source | v) end)

end (* native *)

#target wasm begin

(* The compressed bytes consumed so far are the cells source; the byte at index front and the bytes up to have are readable
   without reading more; the entry's data is size_in bytes from first_byte of its file. A memory input holds all of them (keyword: input). *)
datavtype input(addr, $A.cells, int, int, int, int) =
  | {source:$A.cells}{have:pos}{l:agz} input_memory(l, source, 0, have, 0, have) of ($A.CLEN(source, have) | $A.barr(l, have, source), int have)

fn input_have {owner:addr}{source:$A.cells}{front,have,first_byte,size_in:nat} (inp: !input(owner, source, front, have, first_byte, size_in)): ($A.CLEN(source, have) | int have) =
  case+ inp of
  | @input_memory(len | cb, have) => let val r = (len | have) in fold@(inp); r end

fn input_peek {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,q:nat | front <= q; q < have}
  (inp: !input(owner, source, front, have, first_byte, size_in), q: int q): [v:nat | v < 256] ($A.NTH(source, q, v) | int v) =
  case+ inp of
  | @input_memory(len | cb, have) => let val (found | v) = $A.barr_get(cb, q) in fold@(inp); (found | v) end

end (* wasm *)

datavtype more_result(addr, $A.cells, int, int, int, int, int) =
  | {owner:addr}{source,source2:$A.cells}{front,have,first_byte,size_in,q,front2,have2:nat | front2 <= q; q < have2; have2 <= size_in}
    more_ready(owner, source, front, have, first_byte, size_in, q) of (EXT(source, source2), $A.CLEN(source2, have2) | input(owner, source2, front2, have2, first_byte, size_in))
  | {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,q,front2:nat | front2 <= have}
    more_unavailable(owner, source, front, have, first_byte, size_in, q) of (input(owner, source, front2, have, first_byte, size_in))

#target native begin

fn input_more {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,q:nat | front <= q; q == have}
  (inp: input(owner, source, front, have, first_byte, size_in), q: int q): more_result(owner, source, front, have, first_byte, size_in, q) =
  case+ inp of
  | @input_memory(len | cb, have) => (fold@(inp); more_unavailable(inp))
  | ~input_external(front0, have0, limit0, ext) =>
    (case+ ext of
     | ~external_reading(clen, holds, plen, app | reader, buffer) => let
         prval source_len = _append_clen(app, plen, clen)
       in
         case+ $F.content_read(reader, buffer, 16384) of
         | ~$F.content_read_some(chunk_len, chunk_holds, chunk_app | reader2, buffer2, count) =>
           if have0 + count <= limit0 then
             more_ready(EXT_mk(chunk_app), _append_clen(chunk_app, source_len, chunk_len) |
               input_external(have0, have0 + count, limit0, external_reading(chunk_len, chunk_holds, source_len, chunk_app | reader2, buffer2)))
           else let
             val () = $F.content_reader_close(reader2)
             val () = $A.barr_free(buffer2)
           in more_unavailable(input_external(have0, have0, limit0, external_overrun(source_len | ))) end
         | ~$F.content_read_limit(file_read, whole_len | buffer2) => let
             val () = $A.barr_free(buffer2)
           in more_unavailable(input_external(have0, have0, limit0, external_limit(file_read, whole_len, source_len | ))) end
         | ~$F.content_read_eof(file_read | buffer2) => let
             val () = $A.barr_free(buffer2)
           in more_unavailable(input_external(have0, have0, limit0, external_eof(file_read, source_len | ))) end
         | ~$F.content_read_failed(failure, buffer2) => let
             val () = $A.barr_free(buffer2)
           in more_unavailable(input_external(have0, have0, limit0, external_failed(source_len | failure))) end
       end
     | ~external_limit(file_read, whole_len, have_len | ) => more_unavailable(input_external(have0, have0, limit0, external_limit(file_read, whole_len, have_len | )))
     | ~external_eof(file_read, have_len | ) => more_unavailable(input_external(have0, have0, limit0, external_eof(file_read, have_len | )))
     | ~external_failed(have_len | failure) => more_unavailable(input_external(have0, have0, limit0, external_failed(have_len | failure)))
     | ~external_overrun(have_len | ) => more_unavailable(input_external(have0, have0, limit0, external_overrun(have_len | ))))

end (* native *)

#target wasm begin

fn input_more {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,q:nat | front <= q; q == have}
  (inp: input(owner, source, front, have, first_byte, size_in), q: int q): more_result(owner, source, front, have, first_byte, size_in, q) =
  case+ inp of
  | @input_memory(len | cb, have) => (fold@(inp); more_unavailable(inp))

end (* wasm *)

(* ===== batch 6: reading bits ===== *)

prfn byte_bit_there {byte,half,low:nat | byte == 2 * half + low; low < 2}{index,bit:nat | bit < 2}
  (rest: BYTE_BIT(half, index, bit)): BYTE_BIT(byte, index + 1, bit) = BYTE_BIT_there{half,index}{bit,low}(rest)

fun byte_bit {byte,index:nat | byte < 256; index < 8} .<index>.
  (byte: int byte, index: int index): [bit:nat | bit < 2] (BYTE_BIT(byte, index, bit) | int bit) = let
  val half = byte / 2
  val low = byte - 2 * half
in
  if index = 0 then (BYTE_BIT_here{byte / 2}{byte - 2 * (byte / 2)}() | low)
  else let
    val (rest | bit) = byte_bit(half, index - 1)
  in (byte_bit_there{byte, byte / 2, byte - 2 * (byte / 2)}(rest) | bit) end
end

(* the position after one bit *)
fn next_position {byte_pos,bit_pos:nat | bit_pos < 8} (byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [next_byte,next_bit:nat | 8 * next_byte + next_bit == 8 * byte_pos + bit_pos + 1; next_bit < 8; byte_pos <= next_byte] @(int next_byte, int next_bit) =
  if bit_pos = 7 then @(byte_pos + 1, 0) else @(byte_pos, bit_pos + 1)

dataprop BIT_READ($A.cells, $A.cells, int, int, int, int, int, int) =
  | {source,source2:$A.cells}{front2,have2,size_in,byte_pos,bit_pos,bit:nat | front2 <= byte_pos; 8 * byte_pos + bit_pos + 1 <= 8 * have2; have2 <= size_in; bit_pos < 8; bit < 2}
    BIT_READ_mk(source, source2, byte_pos, bit_pos, bit, front2, have2, size_in) of (EXT(source, source2), BIT(source2, 8 * byte_pos + bit_pos, bit), $A.CLEN(source2, have2))

fn read_bit {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (inp: input(owner, source, front, have, first_byte, size_in), byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][bit:nat | bit < 2][ok:bool]
    (option_v(BIT_READ(source, source2, byte_pos, bit_pos, bit, front2, have2, size_in), ok) | bool ok, input(owner, source2, front2, have2, first_byte, size_in), int bit) = let
  val (have_len | have) = input_have(inp)
in
  if byte_pos < have then let
    val (found | byte) = input_peek(inp, byte_pos)
    val (byte_bit_pf | bit) = byte_bit(byte, bit_pos)
  in (Some_v(BIT_READ_mk(ext_refl(have_len), BIT_mk(found, byte_bit_pf), have_len)) | true, inp, bit) end
  else begin
    case+ input_more(inp, byte_pos) of
    | ~more_ready(ext, more_len | inp2) => let
        val (found | byte) = input_peek(inp2, byte_pos)
        val (byte_bit_pf | bit) = byte_bit(byte, bit_pos)
      in (Some_v(BIT_READ_mk(ext, BIT_mk(found, byte_bit_pf), more_len)) | true, inp2, bit) end
    | ~more_unavailable(inp2) => (None_v() | false, inp2, 0)
  end
end

dataprop BITS_READ($A.cells, $A.cells, int, int, int, int, int, int, int) =
  | {source,source2:$A.cells}{front2,have2,size_in,byte_pos,bit_pos,width,value:nat | 8 * front2 <= 8 * byte_pos + bit_pos + width; 8 * byte_pos + bit_pos + width <= 8 * have2; have2 <= size_in; bit_pos < 8}
    BITS_READ_mk(source, source2, byte_pos, bit_pos, width, value, front2, have2, size_in) of (EXT(source, source2), BITS(source2, 8 * byte_pos + bit_pos, width, value), $A.CLEN(source2, have2))

fun read_bits {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,byte_pos,bit_pos,width:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8; width <= 16} .<width>.
  (inp: input(owner, source, front, have, first_byte, size_in), byte_pos: int byte_pos, bit_pos: int bit_pos, width: int width)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][value:nat][ok:bool]
    (option_v(BITS_READ(source, source2, byte_pos, bit_pos, width, value, front2, have2, size_in), ok) | bool ok, input(owner, source2, front2, have2, first_byte, size_in), int value) =
  if width = 0 then let
    val (have_len | have) = input_have(inp)
  in (Some_v(BITS_READ_mk(ext_refl(have_len), BITS_nil(), have_len)) | true, inp, 0) end
  else let
    val (first_opt | first_ok, inp2, bit) = read_bit(inp, byte_pos, bit_pos)
  in
    if first_ok then let
      prval Some_v(BIT_READ_mk(first_ext, first_bit, first_len)) = first_opt
      val @(next_byte, next_bit) = next_position(byte_pos, bit_pos)
      val (rest_opt | rest_ok, inp3, rest_value) = read_bits(inp2, next_byte, next_bit, width - 1)
    in
      if rest_ok then let
        prval Some_v(BITS_READ_mk(rest_ext, rest_bits, rest_len)) = rest_opt
      in
        (Some_v(BITS_READ_mk(ext_trans(first_ext, rest_ext), BITS_cons(bit_in_ext(rest_ext, first_bit), rest_bits), rest_len)) | true, inp3, bit + 2 * rest_value)
      end
      else let prval None_v() = rest_opt in (None_v() | false, inp3, 0) end
    end
    else let prval None_v() = first_opt in (None_v() | false, inp2, 0) end
  end

prfn tailwin_covers {distance:nat}{output,window:$A.cells}{keep,n,w:nat | distance <= n; distance <= keep}
  (tail: _TAILWIN(output, window, keep), output_len: $A.CLEN(output, n), window_len: $A.CLEN(window, w)): [distance <= w] void =
  case+ tail of
  | _TAILWIN_whole(whole_len) => let prval () = _clen_functional(whole_len, window_len) prval () = _clen_functional(output_len, window_len) in () end
  | _TAILWIN_cut(pre_append, cut_len) => let prval () = _clen_functional(cut_len, window_len) in () end

prfn window_nth_back {distance:nat}{output,window:$A.cells}{keep,n,w:nat | distance <= n; distance <= keep; distance <= w}{value:int}
  (tail: _TAILWIN(output, window, keep), output_len: $A.CLEN(output, n), window_len: $A.CLEN(window, w), found: $A.NTH(window, w - distance, value))
  : $A.NTH(output, n - distance, value) =
  case+ tail of
  | _TAILWIN_whole(whole_len) => let prval () = _clen_functional(whole_len, window_len) prval () = _clen_functional(output_len, window_len) in found end
  | _TAILWIN_cut(pre_append, cut_len) =>
    (case+ pre_append of
     | $A.APPEND_made(pre_sized) =>
       (let
          prval () = _clen_functional(cut_len, window_len)
          prval () = _clen_functional(output_len, _append_sized_clen(pre_sized, window_len))
        in _nth_in_append_right(pre_sized, found) end))

#target native begin

(* the writer of a streaming output (native only): the file writer, or why it failed *)
datavtype external_writer($A.cells) =
  | {output:$A.cells} writer_live(output) of ($F.content_writer(output))
  | {output:$A.cells} writer_failed(output) of ($F.io_error)


(* The output so far, the cells output, written of them. A memory sink keeps all of it in one array of 1 MiB; a streaming sink writes
   each byte to the writer and keeps the last of it, in an array of 64 KiB, for the copies (a back-reference reaches 32768 bytes back). *)
datavtype sink(bool, $A.cells, int) =
  | {output,junk,buffer:$A.cells}{written:nat | written <= 1048576}{l:agz}
    sink_memory(true, output, written) of ($A.CLEN(output, written), $A.APPEND(output, junk, buffer) | $A.barr(l, 1048576, buffer), int written)
  | {output,held,junk,buffer:$A.cells}{written,fill:nat | fill <= 65536; written <= 2147483647}{l:agz}
    sink_streaming(false, output, written) of ($A.CLEN(output, written), $A.CLEN(held, fill), $A.APPEND(held, junk, buffer), _TAILWIN(output, held, 32768) |
                                        external_writer(output), $A.barr(l, 65536, buffer), int written, int fill)
  | {buffer:$A.cells}{l:agz} sink_memory_overflow(true, $A.cnil(), 0) of ($A.barr(l, 1048576, buffer))
  | {output,buffer:$A.cells}{l:agz} sink_streaming_stopped(false, $A.cnil(), 0) of (external_writer(output), $A.barr(l, 65536, buffer))

end (* native *)

#target wasm begin

(* The output so far, the cells output, written of them. A memory sink keeps all of it in one array of 1 MiB; a streaming sink writes
   each byte to the writer and keeps the last of it, in an array of 64 KiB, for the copies (a back-reference reaches 32768 bytes back). *)
datavtype sink(bool, $A.cells, int) =
  | {output,junk,buffer:$A.cells}{written:nat | written <= 1048576}{l:agz}
    sink_memory(true, output, written) of ($A.CLEN(output, written), $A.APPEND(output, junk, buffer) | $A.barr(l, 1048576, buffer), int written)
  | {buffer:$A.cells}{l:agz} sink_memory_overflow(true, $A.cnil(), 0) of ($A.barr(l, 1048576, buffer))

end (* wasm *)

prfun append_split {n,k:nat | k <= n}{both:$A.cells} .<k>.
  (both_len: $A.CLEN(both, n)): [first,second:$A.cells] ($A.CLEN(first, k), $A.CLEN(second, n - k), $A.APPEND(first, second, both)) =
  sif k == 0 then ($A.CLEN_nil(), both_len, $A.APPEND_nil())
  else (case+ both_len of
        | $A.CLEN_cons(rest_len) =>
          (let prval (first_len, second_len, appended) = append_split{n-1,k-1}(rest_len)
           in ($A.CLEN_cons(first_len), second_len, $A.APPEND_cons(appended)) end))

prfun append_peel {leading,rest,whole:$A.cells}{n:nat}{value:int} .<n>.
  (appended: $A.APPEND_SIZED(leading, rest, whole, n), found: $A.NTH(whole, n, value))
  : [leading2,rest2:$A.cells] ($A.APPEND(leading, $A.ccons(value, $A.cnil()), leading2), $A.APPEND(leading2, rest2, whole)) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => (case+ found of $A.NTH_here() => ($A.APPEND_nil(), $A.APPEND_cons($A.APPEND_nil())))
  | $A.APPEND_SIZED_cons(appended_rest) =>
    (case+ found of
     | $A.NTH_there(found_rest) =>
       (let prval (snoc, peeled) = append_peel(appended_rest, found_rest)
        in ($A.APPEND_cons(snoc), $A.APPEND_cons(peeled)) end))

prfun append_rest_len {first,second,both:$A.cells}{n,m:nat} .<n>.
  (appended: $A.APPEND_SIZED(first, second, both, n), both_len: $A.CLEN(both, m)): [rest_count:nat | m == n + rest_count] $A.CLEN(second, rest_count) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => both_len
  | $A.APPEND_SIZED_cons(appended_rest) => (case+ both_len of $A.CLEN_cons(rest_len) => append_rest_len(appended_rest, rest_len))

prfun clen_zero {cells:$A.cells} .<>. (cells_len: $A.CLEN(cells, 0)): $A.CELLS_EQ(cells, $A.cnil()) =
  (case+ cells_len of $A.CLEN_nil() => $A.CELLS_EQ_refl())

prfun append_assoc_back {a,b,c,bc,abc:$A.cells}{n:nat} .<n>.
  (appended: $A.APPEND_SIZED(a, bc, abc, n), inner: $A.APPEND(b, c, bc)): [ab:$A.cells] ($A.APPEND(a, b, ab), $A.APPEND(ab, c, abc)) =
  case+ appended of
  | $A.APPEND_SIZED_nil() => ($A.APPEND_nil(), inner)
  | $A.APPEND_SIZED_cons(appended_rest) =>
    (let prval (front, back) = append_assoc_back(appended_rest, inner)
     in ($A.APPEND_cons(front), $A.APPEND_cons(back)) end)

prfn tailwin_after_slide {output,held,first,second:$A.cells}
  (tail: _TAILWIN(output, held, 32768), halves: $A.APPEND(first, second, held), second_len: $A.CLEN(second, 32768)): _TAILWIN(output, second, 32768) =
  case+ tail of
  | _TAILWIN_whole(_) => _TAILWIN_cut(halves, second_len)
  | _TAILWIN_cut(pre_append, _) =>
    (case+ pre_append of
     | $A.APPEND_made(pre_sized) => (let prval (front, back) = append_assoc_back(pre_sized, halves) in _TAILWIN_cut(back, second_len) end))

(* count cells of an array, from offset on, copied to the front of a new array, one cell at a time *)
fun copy_range {first,second,junk,joined,old_cells,leading,rest_second,new_junk,new_cells:$A.cells}{offset,count,old_size,new_size,i:nat | i <= count; offset + count <= old_size; count <= new_size} {l1,l2:agz} .<count - i>.
  (first_len: $A.CLEN(first, offset), second_len: $A.CLEN(second, count), joined_app: $A.APPEND(first, joined, old_cells), second_app: $A.APPEND(second, junk, joined),
   leading_len: $A.CLEN(leading, i), split: $A.APPEND(leading, rest_second, second), filled: $A.APPEND(leading, new_junk, new_cells), new_len: $A.CLEN(new_cells, new_size) |
   old: !$A.barr(l1, old_size, old_cells), new: $A.barr(l2, new_size, new_cells), i: int i, offset: int offset, count: int count)
  : [new_cells2,new_junk2:$A.cells] ($A.APPEND(second, new_junk2, new_cells2), $A.CLEN(new_cells2, new_size) | $A.barr(l2, new_size, new_cells2)) =
  if i >= count then let
    prval $A.APPEND_made(split_sized) = split
    prval () = _clen_functional(leading_len, _append_sized_len(split_sized))
    prval rest_len = append_rest_len(split_sized, second_len)
    prval $A.CELLS_EQ_refl() = clen_zero(rest_len)
    prval $A.CELLS_EQ_refl() = append_nil_right(split_sized)
  in (filled, new_len | new) end
  else let
    val (found | v) = $A.barr_get(old, offset + i)
    prval $A.APPEND_made(joined_sized) = joined_app
    prval () = _clen_functional(first_len, _append_sized_len(joined_sized))
    prval in_joined = nth_of_append_right{first,joined,old_cells}{i,offset}(joined_sized, found)
    prval $A.APPEND_made(second_sized) = second_app
    prval () = _clen_functional(second_len, _append_sized_len(second_sized))
    prval in_second = nth_of_append_left(second_sized, in_joined)
    prval $A.APPEND_made(split_sized) = split
    prval () = _clen_functional(leading_len, _append_sized_len(split_sized))
    prval (snoc, peeled) = append_peel(split_sized, in_second)
    val (set | new2) = $A.barr_set(new, i, v)
    prval $A.APPEND_made(filled_sized) = filled
    prval (snoc_set, filled2) = append_setc(leading_len, filled_sized, set)
    prval $A.CELLS_EQ_refl() = $A.append_functional(snoc, snoc_set)
    prval next_len = _append_clen(snoc, leading_len, $A.CLEN_cons($A.CLEN_nil()))
    prval new_len2 = $A.setc_len(set, new_len)
  in copy_range(first_len, second_len, joined_app, second_app, next_len, peeled, filled2, new_len2 | old, new2, i + 1, offset, count) end

dataprop PUT_DONE($A.cells, int, $A.cells, int, int) =
  | {output,output2:$A.cells}{b,written,written2:nat | b < 256; written2 == written + 1}
    PUT_DONE_mk(output, b, output2, written, written2) of ($A.APPEND(output, $A.ccons(b, $A.cnil()), output2), $A.CLEN(output2, written2))

(* the memory sink's halves of sink_get and sink_put (keyword: output) *)
fn memory_sink_get {output,junk,buffer:$A.cells}{written,distance:nat | 1 <= distance; distance <= written; written <= 1048576}{l:agz}
  (output_len: $A.CLEN(output, written), appended: $A.APPEND(output, junk, buffer) | buffer: !$A.barr(l, 1048576, buffer), written: int written, distance: int distance)
  : [v:nat | v < 256] ($A.NTH(output, written - distance, v) | int v) = let
  val (found | v) = $A.barr_get(buffer, written - distance)
  prval $A.APPEND_made(sized) = appended
  prval () = _clen_functional(output_len, _append_sized_len(sized))
in (nth_of_append_left(sized, found) | v) end

fn memory_sink_put {output,junk,buffer:$A.cells}{written,b:nat | written <= 1048576; b < 256}{l:agz}
  (output_len: $A.CLEN(output, written), appended: $A.APPEND(output, junk, buffer) | buffer: $A.barr(l, 1048576, buffer), written: int written, b: int b)
  : [output2:$A.cells][written2:nat][ok:bool]
    (option_v(PUT_DONE(output, b, output2, written, written2), ok) | bool ok, sink(true, output2, written2)) =
  if written < 1048576 then let
    val (set | buffer2) = $A.barr_set(buffer, written, b)
    prval $A.APPEND_made(sized) = appended
    prval (snoc, appended2) = append_setc(output_len, sized, set)
    prval next_len = _append_clen(snoc, output_len, $A.CLEN_cons($A.CLEN_nil()))
  in (Some_v(PUT_DONE_mk(snoc, next_len)) | true, sink_memory(next_len, appended2 | buffer2, written + 1)) end
  else (None_v() | false, sink_memory_overflow(buffer))

#target native begin

fn sink_written {in_memory:bool}{output:$A.cells}{written:nat} (snk: !sink(in_memory, output, written)): ($A.CLEN(output, written) | int written) =
  case+ snk of
  | @sink_memory(output_len, appended | buffer, written) => let val r = (output_len | written) in fold@(snk); r end
  | @sink_streaming(output_len, held_len, appended, tail | writer, buffer, written, fill) => let val r = (output_len | written) in fold@(snk); r end
  | @sink_memory_overflow(buffer) => (fold@(snk); ($A.CLEN_nil() | 0))
  | @sink_streaming_stopped(writer, buffer) => (fold@(snk); ($A.CLEN_nil() | 0))

fn sink_get {in_memory:bool}{output:$A.cells}{written,distance:nat | 1 <= distance; distance <= written; distance <= 32768}
  (snk: !sink(in_memory, output, written), distance: int distance): [v:nat | v < 256] ($A.NTH(output, written - distance, v) | int v) =
  case+ snk of
  | @sink_memory(output_len, appended | buffer, written) => let val r = memory_sink_get(output_len, appended | buffer, written, distance) in fold@(snk); r end
  | @sink_streaming(output_len, held_len, appended, tail | writer, buffer, written, fill) => let
      prval () = tailwin_covers{distance}(tail, output_len, held_len)
      val (found | v) = $A.barr_get(buffer, fill - distance)
      prval $A.APPEND_made(sized) = appended
      prval () = _clen_functional(held_len, _append_sized_len(sized))
      prval in_held = nth_of_append_left(sized, found)
      prval in_output = window_nth_back{distance}(tail, output_len, held_len, in_held)
    in fold@(snk); (in_output | v) end

end (* native *)

#target wasm begin

fn sink_written {in_memory:bool}{output:$A.cells}{written:nat} (snk: !sink(in_memory, output, written)): ($A.CLEN(output, written) | int written) =
  case+ snk of
  | @sink_memory(output_len, appended | buffer, written) => let val r = (output_len | written) in fold@(snk); r end
  | @sink_memory_overflow(buffer) => (fold@(snk); ($A.CLEN_nil() | 0))

fn sink_get {in_memory:bool}{output:$A.cells}{written,distance:nat | 1 <= distance; distance <= written; distance <= 32768}
  (snk: !sink(in_memory, output, written), distance: int distance): [v:nat | v < 256] ($A.NTH(output, written - distance, v) | int v) =
  case+ snk of
  | @sink_memory(output_len, appended | buffer, written) => let val r = memory_sink_get(output_len, appended | buffer, written, distance) in fold@(snk); r end

end (* wasm *)

#target native begin

fn window_slide {output,held,junk,buffer:$A.cells}{l:agz}
  (held_len: $A.CLEN(held, 65536), appended: $A.APPEND(held, junk, buffer), tail: _TAILWIN(output, held, 32768) | buffer: $A.barr(l, 65536, buffer))
  : [held2,junk2,buffer2:$A.cells][l2:agz] ($A.CLEN(held2, 32768), $A.APPEND(held2, junk2, buffer2), _TAILWIN(output, held2, 32768) | $A.barr(l2, 65536, buffer2)) = let
  prval (first_len, second_len, halves) = append_split{65536,32768}(held_len)
  prval $A.APPEND_made(halves_sized) = halves
  prval (second_app, joined_app) = append_compose(halves_sized, appended)
  val (new_len | new) = $A.barr_alloc(65536)
  val (filled, new2_len | new2) = copy_range(first_len, second_len, joined_app, second_app, $A.CLEN_nil(), $A.APPEND_nil(), $A.APPEND_nil(), new_len | buffer, new, 0, 32768, 32768)
  val () = $A.barr_free(buffer)
  prval tail2 = tailwin_after_slide(tail, halves, second_len)
in (second_len, filled, tail2 | new2) end

end (* native *)

#target native begin

fn sink_put {in_memory:bool}{output:$A.cells}{written,b:nat | b < 256} (snk: sink(in_memory, output, written), b: int b)
  : [output2:$A.cells][written2:nat][ok:bool]
    (option_v(PUT_DONE(output, b, output2, written, written2), ok) | bool ok, sink(in_memory, output2, written2)) =
  case+ snk of
  | ~sink_memory(output_len, appended | buffer, written) => memory_sink_put(output_len, appended | buffer, written, b)
  | ~sink_streaming(output_len, held_len, appended, tail | writer, buffer, written, fill) =>
    if written >= 2147483647 then (None_v() | false, sink_streaming_stopped(writer, buffer))
    else begin
      case+ writer of
      | ~writer_live(file_writer) =>
        (case+ $F.content_write_byte(file_writer, b) of
         | ~$F.content_wrote(output_append | file_writer2) => let
             prval next_len = _append_clen(output_append, output_len, $A.CLEN_cons($A.CLEN_nil()))
           in
             if fill >= 65536 then let
               val (held2_len, appended2, tail2 | buffer2) = window_slide(held_len, appended, tail | buffer)
               val (set | buffer3) = $A.barr_set(buffer2, 32768, b)
               prval $A.APPEND_made(sized2) = appended2
               prval (snoc, appended3) = append_setc(held2_len, sized2, set)
               prval held3_len = _append_clen(snoc, held2_len, $A.CLEN_cons($A.CLEN_nil()))
               prval tail3 = _tailwin_append(tail2, output_append, snoc, $A.CLEN_cons($A.CLEN_nil()))
             in
               (Some_v(PUT_DONE_mk(output_append, next_len)) | true,
                sink_streaming(next_len, held3_len, appended3, tail3 | writer_live(file_writer2), buffer3, written + 1, 32769))
             end
             else let
               val (set | buffer2) = $A.barr_set(buffer, fill, b)
               prval $A.APPEND_made(sized) = appended
               prval (snoc, appended2) = append_setc(held_len, sized, set)
               prval held2_len = _append_clen(snoc, held_len, $A.CLEN_cons($A.CLEN_nil()))
               prval tail2 = _tailwin_append(tail, output_append, snoc, $A.CLEN_cons($A.CLEN_nil()))
             in
               (Some_v(PUT_DONE_mk(output_append, next_len)) | true,
                sink_streaming(next_len, held2_len, appended2, tail2 | writer_live(file_writer2), buffer2, written + 1, fill + 1))
             end
           end
         | ~$F.content_write_failed(failure) => (None_v() | false, sink_streaming_stopped(writer_failed(failure), buffer)))
      | ~writer_failed(failure) => (None_v() | false, sink_streaming_stopped(writer_failed(failure), buffer))
    end
  | ~sink_memory_overflow(buffer) => (None_v() | false, sink_memory_overflow(buffer))
  | ~sink_streaming_stopped(writer, buffer) => (None_v() | false, sink_streaming_stopped(writer, buffer))

end (* native *)

#target wasm begin

fn sink_put {in_memory:bool}{output:$A.cells}{written,b:nat | b < 256} (snk: sink(in_memory, output, written), b: int b)
  : [output2:$A.cells][written2:nat][ok:bool]
    (option_v(PUT_DONE(output, b, output2, written, written2), ok) | bool ok, sink(in_memory, output2, written2)) =
  case+ snk of
  | ~sink_memory(output_len, appended | buffer, written) => memory_sink_put(output_len, appended | buffer, written, b)
  | ~sink_memory_overflow(buffer) => (None_v() | false, sink_memory_overflow(buffer))

end (* wasm *)

(* ===== batch 9: decoding a symbol ===== *)

dataprop SYMBOL_AT($A.cells, int, int, int) =
  | {lengths:$A.cells}{symbol,len,rank:nat} SYMBOL_AT_mk(lengths, symbol, len, rank) of ($A.NTH(lengths, symbol, len), COUNT_BEFORE(lengths, symbol, len, rank))

(* the symbol of length len that comes rank-th among those of its length *)
fun find_symbol {lengths:$A.cells}{n,len,rank,i,c:nat | i <= n; c <= rank} .<n - i>.
  (counted: COUNT_BEFORE(lengths, i, len, c) | view: !lengths_view(lengths, n), n: int n, len: int len, rank: int rank, i: int i, c: int c)
  : [symbol:nat][ok:bool] (option_v(SYMBOL_AT(lengths, symbol, len, rank), ok) | bool ok, int symbol) =
  if i >= n then (None_v() | false, 0)
  else let
    val (found | v) = length_at(view, i)
  in
    if v = len then begin
      if c = rank then (Some_v(SYMBOL_AT_mk(found, counted)) | true, i)
      else find_symbol(count_before_snoc_hit(counted, found) | view, n, len, rank, i + 1, c + 1)
    end
    else find_symbol(count_before_snoc_miss(counted, found) | view, n, len, rank, i + 1, c)
  end

dataprop SYMBOL_READ($A.cells, $A.cells, $A.cells, int, int, int, int, int, int, int, int, int) =
  | {lengths,source,source2:$A.cells}{byte_pos,bit_pos,symbol,used,front2,have2,size_in,byte_out,bit_out:nat | 1 <= used; used <= 15; 8 * front2 <= 8 * byte_pos + bit_pos + used; 8 * byte_pos + bit_pos + used <= 8 * have2; have2 <= size_in; bit_pos < 8; bit_out < 8; 8 * byte_out + bit_out == 8 * byte_pos + bit_pos + used}
    SYMBOL_READ_mk(lengths, source, source2, byte_pos, bit_pos, symbol, used, front2, have2, size_in, byte_out, bit_out) of (EXT(source, source2), DECSYM(lengths, source2, 8 * byte_pos + bit_pos, symbol, used), $A.CLEN(source2, have2))

(* the bits from byte_pos, bit_pos on, read one at a time as far as the code needs: len of them are read, code is their value *)
fun decode_loop {owner:addr}{lengths,firsts,counts,source,start_source:$A.cells}{n,maxlen,len,code:nat | len < maxlen; maxlen <= 15}{l1,l2:agz}
  {front,have,first_byte,size_in,start_byte,start_bit,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8; start_bit < 8;
   8 * byte_pos + bit_pos == 8 * start_byte + start_bit + len; 8 * front <= 8 * start_byte + start_bit + len} .<maxlen - len>.
  (table: TABLE_UPTO(lengths, firsts, counts, maxlen), start_ext: EXT(start_source, source), hbits: HBITS(source, 8 * start_byte + start_bit, len, code) |
   view: !lengths_view(lengths, n), firsts: !$A.iarr(l1, 16, firsts), counts: !$A.iarr(l2, 16, counts), n: int n, maxlen: int maxlen,
   inp: input(owner, source, front, have, first_byte, size_in), byte_pos: int byte_pos, bit_pos: int bit_pos, len: int len, code: int code)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][symbol,used:nat][ok:bool][byte2,bit2:nat | bit2 < 8]
    (option_v(SYMBOL_READ(lengths, start_source, source2, start_byte, start_bit, symbol, used, front2, have2, size_in, byte2, bit2), ok) | bool ok, input(owner, source2, front2, have2, first_byte, size_in), int byte2, int bit2, int symbol, int used) = let
  val (bit_opt | bit_ok, inp2, bit) = read_bit(inp, byte_pos, bit_pos)
  val @(next_byte, next_bit) = next_position(byte_pos, bit_pos)
in
  if bit_ok then let
    prval Some_v(BIT_READ_mk(bit_ext, bit_pf, bit_len)) = bit_opt
    prval hbits2 = HBITS_snoc(hbits_in_ext(bit_ext, hbits), bit_pf)
    prval start_ext2 = ext_trans(start_ext, bit_ext)
    val code2 = 2 * code + bit
    val (first_nth | first) = $A.iarr_get(firsts, len + 1)
    val (count_nth | count) = $A.iarr_get(counts, len + 1)
    prval (next_pf, bl_pf) = table_lookup(table, first_nth, count_nth)
  in
    if code2 >= first then begin
      if code2 < first + count then let
        val (scan_opt | scan_ok, symbol) = find_symbol(COUNT_BEFORE_zero() | view, n, len + 1, code2 - first, 0, 0)
      in
        if scan_ok then let
          prval Some_v(SYMBOL_AT_mk(symbol_nth, symbol_count)) = scan_opt
          prval code_pf = CODE_mk(symbol_nth, next_pf, symbol_count)
        in (Some_v(SYMBOL_READ_mk(start_ext2, DECSYM_mk(hbits2, code_pf), bit_len)) | true, inp2, next_byte, next_bit, symbol, len + 1) end
        else let prval None_v() = scan_opt in (None_v() | false, inp2, next_byte, next_bit, 0, 0) end
      end
      else if len + 1 < maxlen then decode_loop(table, start_ext2, hbits2 | view, firsts, counts, n, maxlen, inp2, next_byte, next_bit, len + 1, code2)
      else (None_v() | false, inp2, next_byte, next_bit, 0, 0)
    end
    else if len + 1 < maxlen then decode_loop(table, start_ext2, hbits2 | view, firsts, counts, n, maxlen, inp2, next_byte, next_bit, len + 1, code2)
    else (None_v() | false, inp2, next_byte, next_bit, 0, 0)
  end
  else let prval None_v() = bit_opt in (None_v() | false, inp2, next_byte, next_bit, 0, 0) end
end

fn decode_symbol {owner:addr}{lengths:$A.cells}{n,maxlen:nat | 1 <= maxlen; maxlen <= 15}{source:$A.cells}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (view: !lengths_view(lengths, n), tab: !tables(lengths, maxlen), n: int n, maxlen: int maxlen,
   inp: input(owner, source, front, have, first_byte, size_in), byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][symbol,used:nat][ok:bool][byte2,bit2:nat | bit2 < 8]
    (option_v(SYMBOL_READ(lengths, source, source2, byte_pos, bit_pos, symbol, used, front2, have2, size_in, byte2, bit2), ok) | bool ok, input(owner, source2, front2, have2, first_byte, size_in), int byte2, int bit2, int symbol, int used) =
  case+ tab of
  | @tables_made(table, fit | firsts, counts) => let
      val (have_len | have) = input_have(inp)
      val r = decode_loop(table, ext_refl(have_len), HBITS_nil() | view, firsts, counts, n, maxlen, inp, byte_pos, bit_pos, 0, 0)
    in fold@(tab); r end

(* the table of 3.2.5 for the length symbols: the extra bits and the base of a symbol *)
fn length_symbol_info {sym:nat | 257 <= sym; sym <= 285} (sym: int sym)
  : [extra_bits,base:nat | extra_bits <= 5] (LENGTH_SYMBOL(sym, extra_bits, base) | int extra_bits, int base) =
  if sym <= 264 then (LENGTH_SYMBOL_short() | 0, sym - 254)
  else if sym = 285 then (LENGTH_SYMBOL_last() | 0, 258)
  else let
    val extra_bits = (sym - 261) / 4
    val group = sym - 261 - 4 * extra_bits
    val (power_pf | power) = pow2_of(extra_bits)
  in
    if group = 0 then (LENGTH_SYMBOL_base_4_times(power_pf) | extra_bits, 4 * power + 3)
    else if group = 1 then (LENGTH_SYMBOL_base_5_times(power_pf) | extra_bits, 5 * power + 3)
    else if group = 2 then (LENGTH_SYMBOL_base_6_times(power_pf) | extra_bits, 6 * power + 3)
    else (LENGTH_SYMBOL_base_7_times(power_pf) | extra_bits, 7 * power + 3)
  end

fn distance_symbol_info {sym:nat | sym <= 29} (sym: int sym)
  : [extra_bits,base:nat | extra_bits <= 13] (DISTANCE_SYMBOL(sym, extra_bits, base) | int extra_bits, int base) =
  if sym < 4 then (DISTANCE_SYMBOL_short() | 0, sym + 1)
  else let
    val extra_bits = (sym - 2) / 2
    val group = sym - 2 - 2 * extra_bits
    val (power_pf | power) = pow2_of(extra_bits)
  in
    if group = 0 then (DISTANCE_SYMBOL_base_2_times(power_pf) | extra_bits, 2 * power + 1)
    else (DISTANCE_SYMBOL_base_3_times(power_pf) | extra_bits, 3 * power + 1)
  end

(* ===== batch 10: copies and symbols ===== *)

dataprop COPY_DONE($A.cells, int, int, $A.cells, int) =
  | {output,output2:$A.cells}{distance,length,written2:nat} COPY_DONE_mk(output, distance, length, output2, written2) of (COPY(output, distance, length, output2), $A.CLEN(output2, written2))

fun copy_bytes {in_memory:bool}{output:$A.cells}{written,distance,length:nat | 1 <= distance; distance <= written; distance <= 32768} .<length>.
  (snk: sink(in_memory, output, written), distance: int distance, length: int length)
  : [output2:$A.cells][written2:nat][ok:bool]
    (option_v(COPY_DONE(output, distance, length, output2, written2), ok) | bool ok, sink(in_memory, output2, written2)) =
  if length = 0 then let
    val (output_len | _) = sink_written(snk)
  in (Some_v(COPY_DONE_mk(COPY_done(), output_len)) | true, snk) end
  else let
    val (output_len | _) = sink_written(snk)
    val (found | byte) = sink_get(snk, distance)
    val (put_opt | put_ok, snk2) = sink_put(snk, byte)
  in
    if put_ok then let
      prval Some_v(PUT_DONE_mk(appended, next_len)) = put_opt
      val (rest_opt | rest_ok, snk3) = copy_bytes(snk2, distance, length - 1)
    in
      if rest_ok then let
        prval Some_v(COPY_DONE_mk(rest_copy, rest_len)) = rest_opt
      in (Some_v(COPY_DONE_mk(COPY_step(output_len, found, appended, rest_copy), rest_len)) | true, snk3) end
      else let prval None_v() = rest_opt in (None_v() | false, snk3) end
    end
    else let prval None_v() = put_opt in (None_v() | false, snk2) end
  end

(* ===== batch 11: the symbols of a block, one at a time ===== *)

(* SYMBOL_STEP(litlen, dist, source, p, output, p2, output2): the next symbol, from bit p, takes the output to output2 and ends at bit p2 *)
dataprop SYMBOL_STEP($A.cells, $A.cells, $A.cells, int, $A.cells, int, $A.cells) =
  | {litlen,dist,source:$A.cells}{p,sym,used:nat}{output,next:$A.cells}
    SYMBOL_STEP_literal(litlen, dist, source, p, output, p + used, next)
    of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_literal(), sym), $A.APPEND(output, $A.ccons(sym, $A.cnil()), next))
  | {litlen,dist,source:$A.cells}{p,sym,used,length_extra_bits,length_base,length_extra_value,dist_sym,dist_used,dist_extra_bits,dist_base,dist_extra_value:nat | sym == 285 || length_base + length_extra_value <= 257}{output,next:$A.cells}
    SYMBOL_STEP_copy(litlen, dist, source, p, output, p + used + length_extra_bits + dist_used + dist_extra_bits, next)
    of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_length(), sym),
        LENGTH_SYMBOL(sym, length_extra_bits, length_base), BITS(source, p + used, length_extra_bits, length_extra_value),
        DECSYM(dist, source, p + used + length_extra_bits, dist_sym, dist_used), DISTANCE_SYMBOL(dist_sym, dist_extra_bits, dist_base),
        BITS(source, p + used + length_extra_bits + dist_used, dist_extra_bits, dist_extra_value),
        COPY(output, dist_base + dist_extra_value, length_base + length_extra_value, next))

prfun symbol_step_in_ext {litlen,dist,source,source2:$A.cells}{p,p2:nat}{output,output2:$A.cells} .<>.
  (ext: EXT(source, source2), step: SYMBOL_STEP(litlen, dist, source, p, output, p2, output2)): SYMBOL_STEP(litlen, dist, source2, p, output, p2, output2) =
  case+ step of
  | SYMBOL_STEP_literal(decoded, class, appended) =>
    (case+ decoded of DECSYM_mk(hbits, code) => SYMBOL_STEP_literal(DECSYM_mk(hbits_in_ext(ext, hbits), code), class, appended))
  | SYMBOL_STEP_copy(decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied) =>
    (case+ decoded of
     | DECSYM_mk(hbits, code) =>
       (case+ dist_decoded of
        | DECSYM_mk(dist_hbits, dist_code) =>
          SYMBOL_STEP_copy(DECSYM_mk(hbits_in_ext(ext, hbits), code), class, length_symbol, bits_in_ext(ext, length_bits),
                           DECSYM_mk(hbits_in_ext(ext, dist_hbits), dist_code), dist_symbol, bits_in_ext(ext, dist_bits), copied)))

prfun symbol_step_extend {litlen,dist,source:$A.cells}{p,p2,end_bit:nat}{output,output2,after:$A.cells} .<>.
  (step: SYMBOL_STEP(litlen, dist, source, p, output, p2, output2), rest: SYMS(litlen, dist, source, p2, output2, after, end_bit))
  : SYMS(litlen, dist, source, p, output, after, end_bit) =
  case+ step of
  | SYMBOL_STEP_literal(decoded, class, appended) => SYMS_literal(decoded, class, appended, rest)
  | SYMBOL_STEP_copy(decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied) =>
    SYMS_copy(decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied, rest)

(* SYMS_PREFIX(litlen, dist, source, p0, output0, p, output, count): count symbols from bit p0 take the output0 to output and end at bit p; each
   symbol is a step over the source as it was when the symbol was read, and the source grew to the next symbol's (an EXT) *)
dataprop SYMS_PREFIX($A.cells, $A.cells, $A.cells, int, $A.cells, int, $A.cells, int) =
  | {litlen,dist,source:$A.cells}{p:nat}{output:$A.cells} SYMS_PREFIX_empty(litlen, dist, source, p, output, p, output, 0)
  | {litlen,dist,source_before,source:$A.cells}{p0,p,p2,count:nat}{output0,output,output2:$A.cells}
    SYMS_PREFIX_step(litlen, dist, source, p0, output0, p2, output2, count + 1)
    of (SYMS_PREFIX(litlen, dist, source_before, p0, output0, p, output, count), EXT(source_before, source), SYMBOL_STEP(litlen, dist, source, p, output, p2, output2))

prfun syms_close {litlen,dist,source,source_end:$A.cells}{p0,p,end_bit,count:nat}{output0,output,after:$A.cells} .<count>.
  (leading: SYMS_PREFIX(litlen, dist, source, p0, output0, p, output, count), ext: EXT(source, source_end), rest: SYMS(litlen, dist, source_end, p, output, after, end_bit))
  : SYMS(litlen, dist, source_end, p0, output0, after, end_bit) =
  case+ leading of
  | SYMS_PREFIX_empty() => rest
  | SYMS_PREFIX_step(leading_before, step_ext, step) =>
    syms_close(leading_before, ext_trans(step_ext, ext), symbol_step_extend(symbol_step_in_ext(ext, step), rest))

fn advance_position {byte_pos,bit_pos,width:nat | bit_pos < 8; width <= 16} (byte_pos: int byte_pos, bit_pos: int bit_pos, width: int width)
  : [next_byte,next_bit:nat | 8 * next_byte + next_bit == 8 * byte_pos + bit_pos + width; next_bit < 8; byte_pos <= next_byte] @(int next_byte, int next_bit) = let
  val total = bit_pos + width
  val carried = total / 8
in @(byte_pos + carried, total - 8 * carried) end

prfun decsym_in_ext {lengths,source,source2:$A.cells}{p,sym,used:nat} .<>.
  (ext: EXT(source, source2), decoded: DECSYM(lengths, source, p, sym, used)): DECSYM(lengths, source2, p, sym, used) =
  (case+ decoded of DECSYM_mk(hbits, code) => DECSYM_mk(hbits_in_ext(ext, hbits), code))

dataprop LENGTH_ALLOWED(int, int, int) =
  | {sym,base,extra_value:nat | sym == 285 || base + extra_value <= 257} LENGTH_ALLOWED_mk(sym, base, extra_value)

fn length_allowed {sym,base,extra_value:nat} (sym: int sym, base: int base, extra_value: int extra_value)
  : [ok:bool] (option_v(LENGTH_ALLOWED(sym, base, extra_value), ok) | bool ok) =
  if sym = 285 then (Some_v(LENGTH_ALLOWED_mk()) | true)
  else if base + extra_value <= 257 then (Some_v(LENGTH_ALLOWED_mk()) | true)
  else (None_v() | false)

dataprop SYMBOL_OUTCOME(bool, $A.cells, $A.cells, $A.cells, $A.cells, int, $A.cells, int, $A.cells, int, int, int) =
  | {litlen,dist,source,source2:$A.cells}{p,p2,front2,have2,size_in:nat | 8 * front2 <= p2; p2 <= 8 * have2; have2 <= size_in; p < p2}{output,output2:$A.cells}
    OUTCOME_step(false, litlen, dist, source, source2, p, output, p2, output2, front2, have2, size_in)
    of (EXT(source, source2), SYMBOL_STEP(litlen, dist, source2, p, output, p2, output2), $A.CLEN(source2, have2))
  | {litlen,dist,source,source2:$A.cells}{p,p2,front2,have2,size_in:nat | 8 * front2 <= p2; p2 <= 8 * have2; have2 <= size_in; p < p2}{output:$A.cells}
    OUTCOME_end(true, litlen, dist, source, source2, p, output, p2, output, front2, have2, size_in)
    of (EXT(source, source2), SYMS(litlen, dist, source2, p, output, output, p2), $A.CLEN(source2, have2))

(* a length symbol has been read (it ended at the position byte_pos, bit_pos): the rest of the copy *)
fn read_copy {in_memory:bool}{owner:addr}{litlen,dist,source,source2:$A.cells}{dist_n:nat}{output:$A.cells}{written,sym,used,p:nat | 257 <= sym; sym <= 285; 1 <= used; used <= 15}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos == p + used; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (decoded: DECSYM(litlen, source2, p, sym, used), first_ext: EXT(source, source2) |
   dist_view: !lengths_view(dist, dist_n), dist_tab: !tables(dist, 15), dist_n: int dist_n,
   inp: input(owner, source2, front, have, first_byte, size_in), snk: sink(in_memory, output, written), byte_pos: int byte_pos, bit_pos: int bit_pos, sym: int sym)
  : [source3:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][output2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(SYMBOL_OUTCOME(false, litlen, dist, source, source3, p, output, 8 * byte2 + bit2, output2, front2, have2, size_in), ok) |
     bool ok, input(owner, source3, front2, have2, first_byte, size_in), sink(in_memory, output2, written2), int byte2, int bit2) = let
  val (length_pf | length_bits, length_base) = length_symbol_info(sym)
  val (extra_opt | extra_ok, inp2, extra_value) = read_bits(inp, byte_pos, bit_pos, length_bits)
  val @(byte2, bit2) = advance_position(byte_pos, bit_pos, length_bits)
in
  if extra_ok then let
    prval Some_v(BITS_READ_mk(extra_ext, extra_bits, extra_len)) = extra_opt
    prval ext2 = ext_trans(first_ext, extra_ext)
    val (allowed_opt | allowed) = length_allowed(sym, length_base, extra_value)
  in
    if allowed then let
      prval Some_v(LENGTH_ALLOWED_mk()) = allowed_opt
      val (dist_opt | dist_ok, inp3, byte3, bit3, dist_sym, dist_used) = decode_symbol(dist_view, dist_tab, dist_n, 15, inp2, byte2, bit2)
    in
      if dist_ok then let
        prval Some_v(SYMBOL_READ_mk(dist_ext, dist_decoded, dist_len)) = dist_opt
        prval ext3 = ext_trans(ext2, dist_ext)
      in
        if dist_sym <= 29 then let
          val (dist_symbol_pf | dist_bits, dist_base) = distance_symbol_info(dist_sym)
          val (dist_extra_opt | dist_extra_ok, inp4, dist_extra_value) = read_bits(inp3, byte3, bit3, dist_bits)
          val @(byte4, bit4) = advance_position(byte3, bit3, dist_bits)
        in
          if dist_extra_ok then let
            prval Some_v(BITS_READ_mk(dist_extra_ext, dist_extra_bits, dist_extra_len)) = dist_extra_opt
            prval ext4 = ext_trans(ext3, dist_extra_ext)
            prval () = distance_range(dist_symbol_pf, dist_extra_bits)
            val (output_len | count) = sink_written(snk)
            val distance = dist_base + dist_extra_value
            val length = length_base + extra_value
          in
            if distance <= count then let
              val (copy_opt | copy_ok, snk2) = copy_bytes(snk, distance, length)
            in
              if copy_ok then let
                prval Some_v(COPY_DONE_mk(copied, copy_len)) = copy_opt
                prval step = SYMBOL_STEP_copy(decsym_in_ext(ext_trans(extra_ext, ext_trans(dist_ext, dist_extra_ext)), decoded), SYMBOL_CLASS_length(),
                                              length_pf, bits_in_ext(ext_trans(dist_ext, dist_extra_ext), extra_bits),
                                              decsym_in_ext(dist_extra_ext, dist_decoded), dist_symbol_pf, dist_extra_bits, copied)
              in
                (Some_v(OUTCOME_step(ext4, step, dist_extra_len)) | true, inp4, snk2, byte4, bit4)
              end
              else let prval None_v() = copy_opt in (None_v() | false, inp4, snk2, byte4, bit4) end
            end
            else (None_v() | false, inp4, snk, byte4, bit4)
          end
          else let prval None_v() = dist_extra_opt in (None_v() | false, inp4, snk, byte4, bit4) end
        end
        else (None_v() | false, inp3, snk, byte3, bit3)
      end
      else let prval None_v() = dist_opt in (None_v() | false, inp3, snk, byte3, bit3) end
    end
    else let prval None_v() = allowed_opt in (None_v() | false, inp2, snk, byte2, bit2) end
  end
  else let prval None_v() = extra_opt in (None_v() | false, inp2, snk, byte2, bit2) end
end

(* the next symbol of a block: a literal and a copy are steps, the end-of-block symbol ends the block *)
fn read_symbol {in_memory:bool}{owner:addr}{litlen,dist,source:$A.cells}{litlen_n,dist_n:nat}{output:$A.cells}{written,p:nat}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos == p; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (litlen_view: !lengths_view(litlen, litlen_n), litlen_tab: !tables(litlen, 15), litlen_n: int litlen_n,
   dist_view: !lengths_view(dist, dist_n), dist_tab: !tables(dist, 15), dist_n: int dist_n,
   inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, output, written), byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][output2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][is_end,ok:bool]
    (option_v(SYMBOL_OUTCOME(is_end, litlen, dist, source, source2, p, output, 8 * byte2 + bit2, output2, front2, have2, size_in), ok) |
     bool ok, bool is_end, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, output2, written2), int byte2, int bit2) = let
  val (sym_opt | sym_ok, inp2, byte2, bit2, sym, used) = decode_symbol(litlen_view, litlen_tab, litlen_n, 15, inp, byte_pos, bit_pos)
in
  if sym_ok then let
    prval Some_v(SYMBOL_READ_mk(sym_ext, decoded, sym_len)) = sym_opt
  in
    if sym < 256 then let
      val (put_opt | put_ok, snk2) = sink_put(snk, sym)
    in
      if put_ok then let
        prval Some_v(PUT_DONE_mk(appended, next_len)) = put_opt
      in (Some_v(OUTCOME_step(sym_ext, SYMBOL_STEP_literal(decoded, SYMBOL_CLASS_literal(), appended), sym_len)) | true, false, inp2, snk2, byte2, bit2) end
      else let prval None_v() = put_opt in (None_v() | false, false, inp2, snk2, byte2, bit2) end
    end
    else if sym = 256 then
      (Some_v(OUTCOME_end(sym_ext, SYMS_end(decoded, SYMBOL_CLASS_end_of_block()), sym_len)) | true, true, inp2, snk, byte2, bit2)
    else if sym <= 285 then let
      val (copy_opt | copy_ok, inp3, snk2, byte3, bit3) = read_copy(decoded, sym_ext | dist_view, dist_tab, dist_n, inp2, snk, byte2, bit2, sym)
    in (copy_opt | copy_ok, false, inp3, snk2, byte3, bit3) end
    else (None_v() | false, false, inp2, snk, byte2, bit2)
  end
  else let prval None_v() = sym_opt in (None_v() | false, false, inp2, snk, byte2, bit2) end
end

dataprop SYMS_DONE($A.cells, $A.cells, $A.cells, $A.cells, int, $A.cells, $A.cells, int, int, int, int) =
  | {litlen,dist,entry,source2:$A.cells}{p0,end_bit,front2,have2,size_in:nat | p0 < end_bit; 8 * front2 <= end_bit; end_bit <= 8 * have2; have2 <= size_in}{out0,out2:$A.cells}
    SYMS_DONE_mk(litlen, dist, entry, source2, p0, out0, out2, end_bit, front2, have2, size_in)
    of (EXT(entry, source2), SYMS(litlen, dist, source2, p0, out0, out2, end_bit), $A.CLEN(source2, have2))

(* the symbols of a block, to its end-of-block symbol *)
fun symbols_loop {in_memory:bool}{owner:addr}{litlen,dist,entry,source:$A.cells}{litlen_n,dist_n:nat}{p0,count:nat}{out0,output:$A.cells}{written:nat}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | p0 <= 8 * byte_pos + bit_pos; front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8} .<8 * size_in - (8 * byte_pos + bit_pos)>.
  (leading: SYMS_PREFIX(litlen, dist, source, p0, out0, 8 * byte_pos + bit_pos, output, count), entry_ext: EXT(entry, source) |
   litlen_view: !lengths_view(litlen, litlen_n), litlen_tab: !tables(litlen, 15), litlen_n: int litlen_n,
   dist_view: !lengths_view(dist, dist_n), dist_tab: !tables(dist, 15), dist_n: int dist_n,
   inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, output, written), byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][output2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(SYMS_DONE(litlen, dist, entry, source2, p0, out0, output2, 8 * byte2 + bit2, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, output2, written2), int byte2, int bit2) = let
  val (symbol_opt | symbol_ok, is_end, inp2, snk2, byte2, bit2) = read_symbol(litlen_view, litlen_tab, litlen_n, dist_view, dist_tab, dist_n, inp, snk, byte_pos, bit_pos)
in
  if symbol_ok then begin
    if is_end then let
      prval Some_v(OUTCOME_end(symbol_ext, ended, symbol_len)) = symbol_opt
    in
      (Some_v(SYMS_DONE_mk(ext_trans(entry_ext, symbol_ext), syms_close(leading, symbol_ext, ended), symbol_len)) | true, inp2, snk2, byte2, bit2)
    end
    else let
      prval Some_v(OUTCOME_step(symbol_ext, step, symbol_len)) = symbol_opt
    in
      symbols_loop(SYMS_PREFIX_step(leading, symbol_ext, step), ext_trans(entry_ext, symbol_ext) |
                   litlen_view, litlen_tab, litlen_n, dist_view, dist_tab, dist_n, inp2, snk2, byte2, bit2)
    end
  end
  else let prval None_v() = symbol_opt in (None_v() | false, inp2, snk2, byte2, bit2) end
end

(* ===== batch 12: blocks ===== *)

dataprop BYTE_READ($A.cells, $A.cells, int, int, int, int, int) =
  | {source,source2:$A.cells}{byte_pos,value,front2,have2,size_in:nat | front2 <= byte_pos; byte_pos < have2; have2 <= size_in; value < 256}
    BYTE_READ_mk(source, source2, byte_pos, value, front2, have2, size_in) of (EXT(source, source2), $A.NTH(source2, byte_pos, value), $A.CLEN(source2, have2))

fn read_byte {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,byte_pos:nat | front <= byte_pos; front <= have; have <= size_in; byte_pos <= have}
  (inp: input(owner, source, front, have, first_byte, size_in), byte_pos: int byte_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][value:nat][ok:bool]
    (option_v(BYTE_READ(source, source2, byte_pos, value, front2, have2, size_in), ok) | bool ok, input(owner, source2, front2, have2, first_byte, size_in), int value) = let
  val (have_len | have) = input_have(inp)
in
  if byte_pos < have then let
    val (found | byte) = input_peek(inp, byte_pos)
  in (Some_v(BYTE_READ_mk(ext_refl(have_len), found, have_len)) | true, inp, byte) end
  else begin
    case+ input_more(inp, byte_pos) of
    | ~more_ready(ext, more_len | inp2) => let
        val (found | byte) = input_peek(inp2, byte_pos)
      in (Some_v(BYTE_READ_mk(ext, found, more_len)) | true, inp2, byte) end
    | ~more_unavailable(inp2) => (None_v() | false, inp2, 0)
  end
end

(* SLICE built one cell at a time, and moved to a longer source *)
prfun slice_snoc {source:$A.cells}{start,width:nat}{part,part2:$A.cells}{value:int} .<width>.
  (sliced: SLICE(source, start, width, part), found: $A.NTH(source, start + width, value), snoc: $A.APPEND(part, $A.ccons(value, $A.cnil()), part2))
  : SLICE(source, start, width + 1, part2) =
  case+ sliced of
  | SLICE_nil() =>
    (case+ snoc of
     | $A.APPEND_made(snoc_sized) =>
       (case+ snoc_sized of
        | $A.APPEND_SIZED_nil() => SLICE_cons(found, SLICE_nil())))
  | SLICE_cons(head_nth, sliced_rest) =>
    (case+ snoc of
     | $A.APPEND_made(snoc_sized) =>
       (case+ snoc_sized of
        | $A.APPEND_SIZED_cons(snoc_rest) => SLICE_cons(head_nth, slice_snoc{source}{start+1,width-1}(sliced_rest, found, $A.APPEND_made(snoc_rest)))))

prfun slice_in_ext {source,source2:$A.cells}{start,width:nat}{part:$A.cells} .<width>.
  (ext: EXT(source, source2), sliced: SLICE(source, start, width, part)): SLICE(source2, start, width, part) =
  case+ sliced of
  | SLICE_nil() => SLICE_nil()
  | SLICE_cons(head_nth, sliced_rest) => SLICE_cons(nth_in_ext(ext, head_nth), slice_in_ext(ext, sliced_rest))

dataprop BLOCK_DONE(block_kind, $A.cells, $A.cells, int, $A.cells, $A.cells, int, int, int, int) =
  | {source,source2:$A.cells}{kind:block_kind}{p,end_bit,front2,have2,size_in:nat | p <= end_bit; 8 * front2 <= end_bit; end_bit <= 8 * have2; have2 <= size_in}{out,out2:$A.cells}
    BLOCK_DONE_mk(kind, source, source2, p, out, out2, end_bit, front2, have2, size_in)
    of (EXT(source, source2), BLOCK(kind, source2, p, out, out2, end_bit), $A.CLEN(source2, have2))

fn align_byte {byte_pos,bit_pos:nat | bit_pos < 8} (byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [data_byte:nat | 8 * data_byte >= 8 * byte_pos + bit_pos; 8 * data_byte < 8 * byte_pos + bit_pos + 8; byte_pos <= data_byte] int data_byte =
  if bit_pos = 0 then byte_pos else byte_pos + 1

(* the data of a stored block, a byte at a time *)
dataprop STORED_COPIED($A.cells, $A.cells, int, int, $A.cells, $A.cells, $A.cells, int, int, int) =
  | {entry,source2,out_before,data,output:$A.cells}{data_byte,len,front2,have2,size_in:nat | front2 <= data_byte + 4 + len; data_byte + 4 + len <= have2; have2 <= size_in}
    STORED_COPIED_mk(entry, source2, data_byte, len, out_before, data, output, front2, have2, size_in)
    of (EXT(entry, source2), SLICE(source2, data_byte + 4, len, data), $A.APPEND(out_before, data, output), $A.CLEN(source2, have2))

fun stored_copy {in_memory:bool}{owner:addr}{source,entry,data,out_before,output:$A.cells}{data_byte,len,i:nat | i <= len}{written:nat}
  {front,have,first_byte,size_in:nat | front <= data_byte + 4 + i; front <= have; have <= size_in; data_byte + 4 + i <= have} .<len - i>.
  (entry_ext: EXT(entry, source), sliced: SLICE(source, data_byte + 4, i, data), appended: $A.APPEND(out_before, data, output) |
   inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, output, written), data_byte: int data_byte, len: int len, i: int i)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][data2,output2:$A.cells][written2:nat][ok:bool]
    (option_v(STORED_COPIED(entry, source2, data_byte, len, out_before, data2, output2, front2, have2, size_in), ok) | bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, output2, written2)) =
  if i >= len then let
    val (have_len | _) = input_have(inp)
  in (Some_v(STORED_COPIED_mk(entry_ext, sliced, appended, have_len)) | true, inp, snk) end
  else let
    val (byte_opt | byte_ok, inp2, value) = read_byte(inp, data_byte + 4 + i)
  in
    if byte_ok then let
      prval Some_v(BYTE_READ_mk(byte_ext, byte_nth, byte_len)) = byte_opt
      val (put_opt | put_ok, snk2) = sink_put(snk, value)
    in
      if put_ok then let
        prval Some_v(PUT_DONE_mk(put_append, put_len)) = put_opt
        prval $A.APPEND_made(appended_sized) = appended
        prval (data_snoc, appended2) = append_compose(appended_sized, put_append)
      in
        stored_copy(ext_trans(entry_ext, byte_ext), slice_snoc(slice_in_ext(byte_ext, sliced), byte_nth, data_snoc), appended2 | inp2, snk2, data_byte, len, i + 1)
      end
      else let prval None_v() = put_opt in (None_v() | false, inp2, snk2) end
    end
    else let prval None_v() = byte_opt in (None_v() | false, inp2, snk) end
  end

prfn block_stored_at {data_byte:nat}{source:$A.cells}{p,len,nlen:nat | 8 * data_byte >= p; 8 * data_byte < p + 8; len + nlen == 65535}{before,data,after:$A.cells}
  (len_bits: BITS(source, 8 * data_byte, 16, len), nlen_bits: BITS(source, 8 * data_byte + 16, 16, nlen), sliced: SLICE(source, data_byte + 4, len, data), appended: $A.APPEND(before, data, after))
  : BLOCK(block_stored(), source, p, before, after, 8 * (data_byte + 4 + len)) =
  BLOCK_stored{source}{p,data_byte,len,nlen}(len_bits, nlen_bits, sliced, appended)

(* a stored block (3.2.4), its three header bits read: the body starts at the position byte_pos, bit_pos *)
fn decode_stored {in_memory:bool}{owner:addr}{source:$A.cells}{out:$A.cells}{written:nat}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, out, written), byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][out2:$A.cells][written2:nat][end_byte:nat][ok:bool]
    (option_v(BLOCK_DONE(block_stored(), source, source2, 8 * byte_pos + bit_pos, out, out2, 8 * end_byte, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, out2, written2), int end_byte) = let
  val [data_byte_static:int] data_byte = align_byte(byte_pos, bit_pos)
  val (len_opt | len_ok, inp2, len) = read_bits(inp, data_byte, 0, 16)
in
  if len_ok then let
    prval Some_v(BITS_READ_mk(len_ext, len_bits, len_len)) = len_opt
    val (nlen_opt | nlen_ok, inp3, nlen) = read_bits(inp2, data_byte + 2, 0, 16)
  in
    if nlen_ok then let
      prval Some_v(BITS_READ_mk(nlen_ext, nlen_bits, nlen_len)) = nlen_opt
      val (header_len | _) = input_have(inp3)
    in
      if len + nlen = 65535 then let
        val (out_len | _) = sink_written(snk)
        val (copy_opt | copy_ok, inp4, snk2) = stored_copy(ext_refl(header_len), SLICE_nil(), append_nil_refl(out_len) | inp3, snk, data_byte, len, 0)
      in
        if copy_ok then let
          prval Some_v(STORED_COPIED_mk(copy_ext, sliced, appended, copy_len)) = copy_opt
          prval block = block_stored_at{data_byte_static}(bits_in_ext(ext_trans(nlen_ext, copy_ext), len_bits), bits_in_ext(copy_ext, nlen_bits), sliced, appended)
        in (Some_v(BLOCK_DONE_mk(ext_trans(len_ext, ext_trans(nlen_ext, copy_ext)), block, copy_len)) | true, inp4, snk2, data_byte + 4 + len) end
        else let prval None_v() = copy_opt in (None_v() | false, inp4, snk2, 0) end
      end
      else (None_v() | false, inp3, snk, 0)
    end
    else let prval None_v() = nlen_opt in (None_v() | false, inp3, snk, 0) end
  end
  else let prval None_v() = len_opt in (None_v() | false, inp2, snk, 0) end
end

prfun run_make {count:nat}{value:int}{rest:$A.cells} .<count>. (): [all:$A.cells] RUN(count, value, rest, all) =
  sif count == 0 then RUN_zero() else RUN_cons(run_make{count-1}{value}{rest}())

prfn fixed_litlen_make (): [lengths:$A.cells] FIXED_LITLEN(lengths) = let
  prval [after_24:$A.cells] run_fourth = run_make{8}{8}{$A.cnil()}()
  prval [after_112:$A.cells] run_third = run_make{24}{7}{after_24}()
  prval [after_144:$A.cells] run_second = run_make{112}{9}{after_112}()
  prval [all:$A.cells] run_first = run_make{144}{8}{after_144}()
in FIXED_LITLEN_mk(run_first, run_second, run_third, run_fourth) end

prfn fixed_dist_make (): [lengths:$A.cells] FIXED_DIST(lengths) = let
  prval [all:$A.cells] run = run_make{32}{5}{$A.cnil()}()
in FIXED_DIST_mk(run) end

datavtype code_result($A.cells, int) =
  | {lengths:$A.cells}{maxlen:nat} code_ok(lengths, maxlen) of (LENGTHS_FIT(lengths, maxlen) | tables(lengths, maxlen))
  | {lengths:$A.cells}{maxlen:nat} code_refused(lengths, maxlen) of ()

(* the tables of the code whose lengths are read through view, and the proof that no length is over maxlen and the code is not over-subscribed *)
fn make_code {lengths:$A.cells}{n,maxlen:nat | 1 <= maxlen; maxlen <= 15} (view: !lengths_view(lengths, n), n: int n, maxlen: int maxlen): code_result(lengths, maxlen) = let
  val (lengths_len | ()) = lengths_len(view)
  val (at_opt | at_ok) = at_most_scan(AT_MOST_UPTO_zero() | view, n, maxlen, 0)
in
  if at_ok then let
    prval Some_v(upto) = at_opt
    prval at_most = at_most_of_upto(lengths_len, upto)
    val (firsts_len, firsts_zeros | firsts) = $A.iarr_alloc(16)
    val (counts_len, counts_zeros | counts) = $A.iarr_alloc(16)
  in
    case+ build_loop(TABLE_UPTO_zero(), LEN_FIT_zero(), NEXT_CODE_first() | view, firsts, counts, n, maxlen, 0, 0) of
    | ~build_made(tab) =>
      (case+ tab of
       | @tables_made(table, fit | made_firsts, made_counts) => let
           prval fitted = LENGTHS_FIT_mk(at_most, fit)
         in fold@(tab); code_ok(fitted | tab) end)
    | ~build_over_subscribed() => code_refused()
  end
  else let prval None_v() = at_opt in code_refused() end
end

fn free_tables {lengths:$A.cells}{maxlen:nat} (tab: tables(lengths, maxlen)): void =
  case+ tab of ~tables_made(_, _ | firsts, counts) => ($A.iarr_free(firsts); $A.iarr_free(counts))

fn free_view {lengths:$A.cells}{n:nat} (view: lengths_view(lengths, n)): void =
  case+ view of
  | ~lengths_of_fixed_litlen(_, _ | ) => ()
  | ~lengths_of_fixed_dist(_, _ | ) => ()
  | ~lengths_of_array(_, _ | array) => $A.barr_free(array)

prfn fixed_litlen_len {lengths:$A.cells} (fixed: FIXED_LITLEN(lengths)): $A.CLEN(lengths, 288) =
  case+ fixed of
  | FIXED_LITLEN_mk(run_first, run_second, run_third, run_fourth) =>
    run_len(run_first, run_len(run_second, run_len(run_third, run_len(run_fourth, $A.CLEN_nil()))))

prfn fixed_dist_len {lengths:$A.cells} (fixed: FIXED_DIST(lengths)): $A.CLEN(lengths, 32) =
  case+ fixed of FIXED_DIST_mk(run) => run_len(run, $A.CLEN_nil())

(* a block with the fixed codes (3.2.6), its three header bits read *)
fn decode_fixed {in_memory:bool}{owner:addr}{source:$A.cells}{out:$A.cells}{written:nat}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, out, written), byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][out2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(BLOCK_DONE(block_fixed(), source, source2, 8 * byte_pos + bit_pos, out, out2, 8 * byte2 + bit2, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, out2, written2), int byte2, int bit2) = let
  prval [litlen:$A.cells] fixed_litlen = fixed_litlen_make()
  prval [dist:$A.cells] fixed_dist = fixed_dist_make()
  val litlen_view = lengths_of_fixed_litlen(fixed_litlen, fixed_litlen_len(fixed_litlen) | )
  val dist_view = lengths_of_fixed_dist(fixed_dist, fixed_dist_len(fixed_dist) | )
  val litlen_code = make_code(litlen_view, 288, 15)
  val dist_code = make_code(dist_view, 32, 15)
in
  case+ litlen_code of
  | ~code_ok(litlen_fit | litlen_tab) =>
    (case+ dist_code of
     | ~code_ok(dist_fit | dist_tab) => let
         val (have_len | _) = input_have(inp)
         val (syms_opt | syms_ok, inp2, snk2, byte2, bit2) =
           symbols_loop(SYMS_PREFIX_empty(), ext_refl(have_len) | litlen_view, litlen_tab, 288, dist_view, dist_tab, 32, inp, snk, byte_pos, bit_pos)
         val () = free_tables(litlen_tab)
         val () = free_tables(dist_tab)
         val () = free_view(litlen_view)
         val () = free_view(dist_view)
       in
         if syms_ok then let
           prval Some_v(SYMS_DONE_mk(syms_ext, syms, syms_len)) = syms_opt
         in (Some_v(BLOCK_DONE_mk(syms_ext, BLOCK_fixed(fixed_litlen, fixed_dist, litlen_fit, dist_fit, syms), syms_len)) | true, inp2, snk2, byte2, bit2) end
         else let prval None_v() = syms_opt in (None_v() | false, inp2, snk2, byte2, bit2) end
       end
     | ~code_refused() => let
         val () = free_tables(litlen_tab)
         val () = free_view(litlen_view)
         val () = free_view(dist_view)
       in (None_v() | false, inp, snk, 0, 0) end)
  | ~code_refused() => let
      val () = free_view(litlen_view)
      val () = free_view(dist_view)
      val () = (case+ dist_code of ~code_ok(_ | tab) => free_tables(tab) | ~code_refused() => ())
    in (None_v() | false, inp, snk, 0, 0) end
end

(* ===== batch 13: a block, moved to a longer source ===== *)

prfun syms_sized_in_ext {litlen,dist,source,source2:$A.cells}{p,end_bit,symbols:nat}{before,after:$A.cells} .<symbols>.
  (ext: EXT(source, source2), syms: SYMS_SIZED(litlen, dist, source, p, before, after, end_bit, symbols)): SYMS_SIZED(litlen, dist, source2, p, before, after, end_bit, symbols) =
  case+ syms of
  | SYMS_SIZED_end(decoded, class) => SYMS_SIZED_end(decsym_in_ext(ext, decoded), class)
  | SYMS_SIZED_literal(decoded, class, appended, rest) =>
    SYMS_SIZED_literal(decsym_in_ext(ext, decoded), class, appended, syms_sized_in_ext(ext, rest))
  | SYMS_SIZED_copy(decoded, class, length_symbol, length_bits, dist_decoded, dist_symbol, dist_bits, copied, rest) =>
    SYMS_SIZED_copy(decsym_in_ext(ext, decoded), class, length_symbol, bits_in_ext(ext, length_bits),
                    decsym_in_ext(ext, dist_decoded), dist_symbol, bits_in_ext(ext, dist_bits), copied, syms_sized_in_ext(ext, rest))

prfun syms_in_ext {litlen,dist,source,source2:$A.cells}{p,end_bit:nat}{before,after:$A.cells} .<>.
  (ext: EXT(source, source2), syms: SYMS(litlen, dist, source, p, before, after, end_bit)): SYMS(litlen, dist, source2, p, before, after, end_bit) =
  (case+ syms of SYMS_made(sized) => SYMS_made(syms_sized_in_ext(ext, sized)))

prfun read_lengths3_in_ext {source,source2:$A.cells}{p,count:nat}{values:$A.cells} .<count>.
  (ext: EXT(source, source2), read: READ_LENGTHS3(source, p, count, values)): READ_LENGTHS3(source2, p, count, values) =
  case+ read of
  | READ_LENGTHS3_nil() => READ_LENGTHS3_nil()
  | READ_LENGTHS3_cons(bits, read_rest) => READ_LENGTHS3_cons(bits_in_ext(ext, bits), read_lengths3_in_ext(ext, read_rest))

prfun code_lengths_sized_in_ext {code_length_code,source,source2:$A.cells}{p,total,end_bit,steps:nat}{so_far,lengths:$A.cells} .<steps>.
  (ext: EXT(source, source2), lengths: CODE_LENGTHS_SIZED(code_length_code, source, p, so_far, total, lengths, end_bit, steps))
  : CODE_LENGTHS_SIZED(code_length_code, source2, p, so_far, total, lengths, end_bit, steps) =
  case+ lengths of
  | CODE_LENGTHS_SIZED_done(so_far_len) => CODE_LENGTHS_SIZED_done(so_far_len)
  | CODE_LENGTHS_SIZED_literal(so_far_len, decoded, class, appended, rest) =>
    CODE_LENGTHS_SIZED_literal(so_far_len, decsym_in_ext(ext, decoded), class, appended, code_lengths_sized_in_ext(ext, rest))
  | CODE_LENGTHS_SIZED_repeat_previous(so_far_len, decoded, class, extra, previous, run, appended, rest) =>
    CODE_LENGTHS_SIZED_repeat_previous(so_far_len, decsym_in_ext(ext, decoded), class, bits_in_ext(ext, extra), previous, run, appended, code_lengths_sized_in_ext(ext, rest))
  | CODE_LENGTHS_SIZED_zeros_short(so_far_len, decoded, class, extra, run, appended, rest) =>
    CODE_LENGTHS_SIZED_zeros_short(so_far_len, decsym_in_ext(ext, decoded), class, bits_in_ext(ext, extra), run, appended, code_lengths_sized_in_ext(ext, rest))
  | CODE_LENGTHS_SIZED_zeros_long(so_far_len, decoded, class, extra, run, appended, rest) =>
    CODE_LENGTHS_SIZED_zeros_long(so_far_len, decsym_in_ext(ext, decoded), class, bits_in_ext(ext, extra), run, appended, code_lengths_sized_in_ext(ext, rest))

prfun code_lengths_in_ext {code_length_code,source,source2:$A.cells}{p,total,end_bit:nat}{so_far,lengths:$A.cells} .<>.
  (ext: EXT(source, source2), lengths: CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit))
  : CODE_LENGTHS(code_length_code, source2, p, so_far, total, lengths, end_bit) =
  (case+ lengths of CODE_LENGTHS_made(sized) => CODE_LENGTHS_made(code_lengths_sized_in_ext(ext, sized)))

prfun block_in_ext {kind:block_kind}{source,source2:$A.cells}{p,end_bit:nat}{before,after:$A.cells} .<>.
  (ext: EXT(source, source2), block: BLOCK(kind, source, p, before, after, end_bit)): BLOCK(kind, source2, p, before, after, end_bit) =
  case+ block of
  | BLOCK_stored{source}{p1,data_byte,len,nlen}{before1,data,after1}(len_bits, nlen_bits, sliced, appended) =>
    block_stored_at{data_byte}(bits_in_ext(ext, len_bits), bits_in_ext(ext, nlen_bits), slice_in_ext(ext, sliced), appended)
  | BLOCK_fixed(fixed_litlen, fixed_dist, litlen_fit, dist_fit, syms) =>
    BLOCK_fixed(fixed_litlen, fixed_dist, litlen_fit, dist_fit, syms_in_ext(ext, syms))
  | BLOCK_dynamic(hlit_bits, hdist_bits, hclen_bits, values_read, order, from, clc_fit, clc_full, lengths, litlen_len, split, litlen_usable, dist_usable, syms) =>
    BLOCK_dynamic(bits_in_ext(ext, hlit_bits), bits_in_ext(ext, hdist_bits), bits_in_ext(ext, hclen_bits), read_lengths3_in_ext(ext, values_read), order, from, clc_fit, clc_full,
                  code_lengths_in_ext(ext, lengths), litlen_len, split, litlen_usable, dist_usable, syms_in_ext(ext, syms))

(* ===== batch 14: the blocks ===== *)

(* ===== batch 13b: the dynamic block's header ===== *)

prfn append_head_move {a,av,r,avr:$A.cells}{value:int}
  (snoc: $A.APPEND(a, $A.ccons(value, $A.cnil()), av), rest: $A.APPEND(av, r, avr)): $A.APPEND(a, $A.ccons(value, r), avr) =
  (case+ snoc of
   | $A.APPEND_made(snoc_sized) => _append_assoc(snoc_sized, rest, $A.APPEND_cons($A.APPEND_nil())))

prfn neq_of_not_in {head,sym:int}{rest:$A.cells}{k:nat} (not_in: _NOT_IN(head, rest), found: $A.NTH(rest, k, sym)): [head != sym] void =
  sif head == sym then (let prval () = _not_in_nth(not_in, found) in () end) else ()

prfun not_in_prefix_of_nth {order:$A.cells}{count,position:nat | count <= position}{sym:int} .<count>.
  (distinct: _DISTINCT(order), found: $A.NTH(order, position, sym)): NOT_IN_PREFIX(order, count, sym) =
  sif count == 0 then NOT_IN_PREFIX_zero()
  else (case+ found of
        | $A.NTH_there(found_rest) =>
          (case+ distinct of
           | _DISTINCT_cons(not_in_rest, distinct_rest) => let
               prval () = neq_of_not_in(not_in_rest, found_rest)
             in NOT_IN_PREFIX_cons(not_in_prefix_of_nth{..}{count-1,position-1}(distinct_rest, found_rest)) end))

dataprop VALUES_READ($A.cells, $A.cells, int, int, $A.cells, $A.cells, $A.cells, $A.cells, int, int, int, int, int) =
  | {source,source2,so_far,suffix,total,junk,cells:$A.cells}{p,remaining,front2,have2,size_in,byte2,bit2:nat | bit2 < 8; 8 * byte2 + bit2 == p + 3 * remaining; 8 * front2 <= p + 3 * remaining; p + 3 * remaining <= 8 * have2; have2 <= size_in}
    VALUES_READ_mk(source, source2, p, remaining, so_far, suffix, total, cells, front2, have2, size_in, byte2, bit2)
    of (EXT(source, source2), READ_LENGTHS3(source2, p, remaining, suffix), $A.APPEND(so_far, suffix, total), $A.APPEND(total, junk, cells), $A.CLEN(source2, have2))

(* the 3-bit values of the code length code, written into an array as they are read *)
fun read_values {owner:addr}{source,so_far,junk,cells:$A.cells}{filled,remaining:nat | filled + remaining <= 32}{l:agz}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8} .<remaining>.
  (so_far_len: $A.CLEN(so_far, filled), appended: $A.APPEND(so_far, junk, cells) |
   inp: input(owner, source, front, have, first_byte, size_in), values: $A.barr(l, 32, cells), byte_pos: int byte_pos, bit_pos: int bit_pos, filled: int filled, remaining: int remaining)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][suffix,total,cells2:$A.cells][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(VALUES_READ(source, source2, 8 * byte_pos + bit_pos, remaining, so_far, suffix, total, cells2, front2, have2, size_in, byte2, bit2), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), $A.barr(l, 32, cells2), int byte2, int bit2) =
  if remaining = 0 then let
    val (have_len | _) = input_have(inp)
  in (Some_v(VALUES_READ_mk(ext_refl(have_len), READ_LENGTHS3_nil(), append_nil_refl(so_far_len), appended, have_len)) | true, inp, values, byte_pos, bit_pos) end
  else let
    val (bits_opt | bits_ok, inp2, value) = read_bits(inp, byte_pos, bit_pos, 3)
    val @(byte2, bit2) = advance_position(byte_pos, bit_pos, 3)
  in
    if bits_ok then let
      prval Some_v(BITS_READ_mk(bits_ext, value_bits, bits_len)) = bits_opt
      prval () = _bits_below_power(value_bits, $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))
      val (set | values2) = $A.barr_set(values, filled, value)
      prval $A.APPEND_made(appended_sized) = appended
      prval (snoc, appended2) = append_setc(so_far_len, appended_sized, set)
      prval next_len = _append_clen(snoc, so_far_len, $A.CLEN_cons($A.CLEN_nil()))
      val (rest_opt | rest_ok, inp3, values3, byte3, bit3) = read_values(next_len, appended2 | inp2, values2, byte2, bit2, filled + 1, remaining - 1)
    in
      if rest_ok then let
        prval Some_v(VALUES_READ_mk(rest_ext, rest_read, rest_total, rest_cells, rest_len)) = rest_opt
      in
        (Some_v(VALUES_READ_mk(ext_trans(bits_ext, rest_ext), READ_LENGTHS3_cons(bits_in_ext(rest_ext, value_bits), rest_read),
                               append_head_move(snoc, rest_total), rest_cells, rest_len)) | true, inp3, values3, byte3, bit3)
      end
      else let prval None_v() = rest_opt in (None_v() | false, inp3, values3, byte3, bit3) end
    end
    else let prval None_v() = bits_opt in (None_v() | false, inp2, values, byte2, bit2) end
  end


dataprop ORDER_FACTS($A.cells) =
  | {order:$A.cells} ORDER_FACTS_mk(order) of ($A.NTH(order, 0, 16), $A.NTH(order, 1, 17), $A.NTH(order, 2, 18), $A.NTH(order, 3, 0), $A.NTH(order, 4, 8), $A.NTH(order, 5, 7), $A.NTH(order, 6, 9), $A.NTH(order, 7, 6), $A.NTH(order, 8, 10), $A.NTH(order, 9, 5), $A.NTH(order, 10, 11), $A.NTH(order, 11, 4), $A.NTH(order, 12, 12), $A.NTH(order, 13, 3), $A.NTH(order, 14, 13), $A.NTH(order, 15, 2), $A.NTH(order, 16, 14), $A.NTH(order, 17, 1), $A.NTH(order, 18, 15))

prfn order_facts {order:$A.cells} (order_pf: CL_ORDER(order)): ORDER_FACTS(order) =
  case+ order_pf of CL_ORDER_mk() => ORDER_FACTS_mk($A.NTH_here(), $A.NTH_there($A.NTH_here()), $A.NTH_there($A.NTH_there($A.NTH_here())), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))))))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))))))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))))))))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))))))))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here()))))))))))))))))), $A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_there($A.NTH_here())))))))))))))))))))

fn order_position {order:$A.cells}{sym:nat | sym <= 18} (order_pf: CL_ORDER(order) | sym: int sym)
  : [position:nat | position < 19] ($A.NTH(order, position, sym) | int position) = let
  prval ORDER_FACTS_mk(order_nth_0, order_nth_1, order_nth_2, order_nth_3, order_nth_4, order_nth_5, order_nth_6, order_nth_7, order_nth_8, order_nth_9, order_nth_10, order_nth_11, order_nth_12, order_nth_13, order_nth_14, order_nth_15, order_nth_16, order_nth_17, order_nth_18) = order_facts(order_pf)
in
  if sym = 16 then (order_nth_0 | 0)
  else if sym = 17 then (order_nth_1 | 1)
  else if sym = 18 then (order_nth_2 | 2)
  else if sym = 0 then (order_nth_3 | 3)
  else if sym = 8 then (order_nth_4 | 4)
  else if sym = 7 then (order_nth_5 | 5)
  else if sym = 9 then (order_nth_6 | 6)
  else if sym = 6 then (order_nth_7 | 7)
  else if sym = 10 then (order_nth_8 | 8)
  else if sym = 5 then (order_nth_9 | 9)
  else if sym = 11 then (order_nth_10 | 10)
  else if sym = 4 then (order_nth_11 | 11)
  else if sym = 12 then (order_nth_12 | 12)
  else if sym = 3 then (order_nth_13 | 13)
  else if sym = 13 then (order_nth_14 | 14)
  else if sym = 2 then (order_nth_15 | 15)
  else if sym = 14 then (order_nth_16 | 16)
  else if sym = 1 then (order_nth_17 | 17)
  else (order_nth_18 | 18)
end

dataprop CLC_FILLED($A.cells, $A.cells, $A.cells, int, int, $A.cells, $A.cells, $A.cells) =
  (* order, values, rest, count, sym, so_far, total, cells *)
  | {order,values,rest,so_far,total,junk,cells:$A.cells}{count,sym:nat}
    CLC_FILLED_mk(order, values, rest, count, sym, so_far, total, cells)
    of (CODE_LENGTHS_FROM(order, count, values, sym, rest), $A.APPEND(so_far, rest, total), $A.APPEND(total, junk, cells))

fn clc_length_of {order,values,vjunk,vcells:$A.cells}{count,sym:nat | sym <= 18; count <= 19}{lv:agz}
  (order_pf: CL_ORDER(order), values_len: $A.CLEN(values, count), values_app: $A.APPEND(values, vjunk, vcells) |
   source_values: !$A.barr(lv, 32, vcells), count: int count, sym: int sym)
  : [length:nat | length < 256] (CODE_LENGTH_OF(order, sym, count, values, length) | int length) = let
  val (order_nth | position) = order_position(order_pf | sym)
in
  if position < count then let
    val (values_nth | length) = $A.barr_get(source_values, position)
    prval $A.APPEND_made(values_sized) = values_app
    prval () = _clen_functional(values_len, _append_sized_len(values_sized))
  in (CODE_LENGTH_OF_stored(order_nth, nth_of_append_left(values_sized, values_nth)) | length) end
  else (CODE_LENGTH_OF_absent(not_in_prefix_of_nth(_cl_order_distinct(order_pf), order_nth)) | 0)
end

fun fill_clc {order,values,vjunk,vcells,so_far,junk,cells:$A.cells}{count,sym:nat | sym <= 19; count <= 19}{lv,lc:agz} .<19 - sym>.
  (order_pf: CL_ORDER(order), values_len: $A.CLEN(values, count), values_app: $A.APPEND(values, vjunk, vcells), so_far_len: $A.CLEN(so_far, sym), cl_app: $A.APPEND(so_far, junk, cells) |
   source_values: !$A.barr(lv, 32, vcells), lengths: $A.barr(lc, 320, cells), count: int count, sym: int sym)
  : [rest,total,cells2:$A.cells] (CLC_FILLED(order, values, rest, count, sym, so_far, total, cells2) | $A.barr(lc, 320, cells2)) =
  if sym >= 19 then
    (CLC_FILLED_mk(CODE_LENGTHS_FROM_end(), append_nil_refl(so_far_len), cl_app) | lengths)
  else let
    val (of_pf | length) = clc_length_of(order_pf, values_len, values_app | source_values, count, sym)
    val (set | lengths2) = $A.barr_set(lengths, sym, length)
    prval $A.APPEND_made(cl_sized) = cl_app
    prval (snoc, cl_app2) = append_setc(so_far_len, cl_sized, set)
    prval next_len = _append_clen(snoc, so_far_len, $A.CLEN_cons($A.CLEN_nil()))
    val (rest_pf | lengths3) = fill_clc(order_pf, values_len, values_app, next_len, cl_app2 | source_values, lengths2, count, sym + 1)
    prval CLC_FILLED_mk(rest_from, rest_total, rest_cells) = rest_pf
  in (CLC_FILLED_mk(CODE_LENGTHS_FROM_cons(of_pf, rest_from), append_head_move(snoc, rest_total), rest_cells) | lengths3) end

(* count cells, all value, written to an array after the cells so_far *)
fun write_run {so_far,junk,cells:$A.cells}{count,k:nat | count + k <= 320}{value:nat | value < 256}{l:agz} .<k>.
  (so_far_len: $A.CLEN(so_far, count), appended: $A.APPEND(so_far, junk, cells) |
   lengths: $A.barr(l, 320, cells), count: int count, k: int k, value: int value)
  : [run,next,junk2,cells2:$A.cells] (RUN(k, value, $A.cnil(), run), $A.APPEND(so_far, run, next), $A.APPEND(next, junk2, cells2) | $A.barr(l, 320, cells2)) =
  if k = 0 then (RUN_zero(), append_nil_refl(so_far_len), appended | lengths)
  else let
    val (set | lengths2) = $A.barr_set(lengths, count, value)
    prval $A.APPEND_made(sized) = appended
    prval (snoc, appended2) = append_setc(so_far_len, sized, set)
    prval next_len = _append_clen(snoc, so_far_len, $A.CLEN_cons($A.CLEN_nil()))
    val (rest_run, rest_app, rest_appended | lengths3) = write_run(next_len, appended2 | lengths2, count + 1, k - 1, value)
  in (RUN_cons(rest_run), append_head_move(snoc, rest_app), rest_appended | lengths3) end

dataprop CL_READ($A.cells, $A.cells, $A.cells, int, $A.cells, int, $A.cells, $A.cells, int, int, int, int) =
  | {clc,source,source2,so_far,lengths,junk,cells2:$A.cells}{p,total,end_bit,front2,have2,size_in:nat | p <= end_bit; 8 * front2 <= end_bit; end_bit <= 8 * have2; have2 <= size_in}
    CL_READ_mk(clc, source, source2, p, so_far, total, lengths, cells2, end_bit, front2, have2, size_in)
    of (EXT(source, source2), CODE_LENGTHS(clc, source2, p, so_far, total, lengths, end_bit), $A.APPEND(lengths, junk, cells2), $A.CLEN(source2, have2))

(* the code lengths of a dynamic block (3.2.7): the symbols of the code length code, to the total number of lengths *)
fun read_code_lengths {owner:addr}{clc,source,so_far,junk,cells:$A.cells}{total,count:nat | count <= total; total <= 320}{l:agz}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8} .<total - count>.
  (so_far_len: $A.CLEN(so_far, count), appended: $A.APPEND(so_far, junk, cells) |
   view: !lengths_view(clc, 19), tab: !tables(clc, 7), inp: input(owner, source, front, have, first_byte, size_in), lengths: $A.barr(l, 320, cells),
   byte_pos: int byte_pos, bit_pos: int bit_pos, count: int count, total: int total)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][all_lengths,cells2:$A.cells][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(CL_READ(clc, source, source2, 8 * byte_pos + bit_pos, so_far, total, all_lengths, cells2, 8 * byte2 + bit2, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), $A.barr(l, 320, cells2), int byte2, int bit2) =
  if count >= total then let
    val (have_len | _) = input_have(inp)
  in (Some_v(CL_READ_mk(ext_refl(have_len), CODE_LENGTHS_done(so_far_len), appended, have_len)) | true, inp, lengths, byte_pos, bit_pos) end
  else let
    val (sym_opt | sym_ok, inp2, byte2, bit2, sym, used) = decode_symbol(view, tab, 19, 7, inp, byte_pos, bit_pos)
  in
    if sym_ok then let
      prval Some_v(SYMBOL_READ_mk(sym_ext, decoded, sym_len)) = sym_opt
    in
      if sym <= 15 then let
        val (set | lengths2) = $A.barr_set(lengths, count, sym)
        prval $A.APPEND_made(sized) = appended
        prval (snoc, appended2) = append_setc(so_far_len, sized, set)
        prval next_len = _append_clen(snoc, so_far_len, $A.CLEN_cons($A.CLEN_nil()))
        val (rest_opt | rest_ok, inp3, lengths3, byte3, bit3) = read_code_lengths(next_len, appended2 | view, tab, inp2, lengths2, byte2, bit2, count + 1, total)
      in
        if rest_ok then let
          prval Some_v(CL_READ_mk(rest_ext, rest_lengths, rest_appended, rest_len)) = rest_opt
        in
          (Some_v(CL_READ_mk(ext_trans(sym_ext, rest_ext),
                             CODE_LENGTHS_literal(so_far_len, decsym_in_ext(rest_ext, decoded), LENGTH_CLASS_literal(), snoc, rest_lengths), rest_appended, rest_len)) |
           true, inp3, lengths3, byte3, bit3)
        end
        else let prval None_v() = rest_opt in (None_v() | false, inp3, lengths3, byte3, bit3) end
      end
      else if sym = 16 then begin
        if count >= 1 then let
          val (previous_nth | previous) = $A.barr_get(lengths, count - 1)
          prval $A.APPEND_made(previous_sized) = appended
          prval () = _clen_functional(so_far_len, _append_sized_len(previous_sized))
          prval previous_in = nth_of_append_left(previous_sized, previous_nth)
          val (extra_opt | extra_ok, inp3, extra) = read_bits(inp2, byte2, bit2, 2)
          val @(byte3, bit3) = advance_position(byte2, bit2, 2)
        in
          if extra_ok then let
            prval Some_v(BITS_READ_mk(extra_ext, extra_bits, extra_len)) = extra_opt
            prval () = _bits_below_power(extra_bits, $AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))
          in
            if count + 3 + extra <= total then let
              val (run_pf, run_app, run_appended | lengths2) = write_run(so_far_len, appended | lengths, count, 3 + extra, previous)
              prval next_len = _append_clen(run_app, so_far_len, run_len(run_pf, $A.CLEN_nil()))
              val (rest_opt | rest_ok, inp4, lengths3, byte4, bit4) = read_code_lengths(next_len, run_appended | view, tab, inp3, lengths2, byte3, bit3, count + 3 + extra, total)
            in
              if rest_ok then let
                prval Some_v(CL_READ_mk(rest_ext, rest_lengths, rest_appended, rest_len)) = rest_opt
                prval sym_to_end = ext_trans(extra_ext, rest_ext)
              in
                (Some_v(CL_READ_mk(ext_trans(sym_ext, sym_to_end),
                                   CODE_LENGTHS_repeat_previous(so_far_len, decsym_in_ext(sym_to_end, decoded), LENGTH_CLASS_repeat_previous(), bits_in_ext(rest_ext, extra_bits), previous_in,
                                          run_pf, run_app, rest_lengths), rest_appended, rest_len)) | true, inp4, lengths3, byte4, bit4)
              end
              else let prval None_v() = rest_opt in (None_v() | false, inp4, lengths3, byte4, bit4) end
            end
            else (None_v() | false, inp3, lengths, byte3, bit3)
          end
          else let prval None_v() = extra_opt in (None_v() | false, inp3, lengths, byte3, bit3) end
        end
        else (None_v() | false, inp2, lengths, byte2, bit2)
      end
      else if sym = 17 then begin
        if true then let
          val (extra_opt | extra_ok, inp3, extra) = read_bits(inp2, byte2, bit2, 3)
          val @(byte3, bit3) = advance_position(byte2, bit2, 3)
        in
          if extra_ok then let
            prval Some_v(BITS_READ_mk(extra_ext, extra_bits, extra_len)) = extra_opt
            prval () = _bits_below_power(extra_bits, $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))
          in
            if count + 3 + extra <= total then let
              val (run_pf, run_app, run_appended | lengths2) = write_run(so_far_len, appended | lengths, count, 3 + extra, 0)
              prval next_len = _append_clen(run_app, so_far_len, run_len(run_pf, $A.CLEN_nil()))
              val (rest_opt | rest_ok, inp4, lengths3, byte4, bit4) = read_code_lengths(next_len, run_appended | view, tab, inp3, lengths2, byte3, bit3, count + 3 + extra, total)
            in
              if rest_ok then let
                prval Some_v(CL_READ_mk(rest_ext, rest_lengths, rest_appended, rest_len)) = rest_opt
                prval sym_to_end = ext_trans(extra_ext, rest_ext)
              in
                (Some_v(CL_READ_mk(ext_trans(sym_ext, sym_to_end),
                                   CODE_LENGTHS_zeros_short(so_far_len, decsym_in_ext(sym_to_end, decoded), LENGTH_CLASS_zeros_short(), bits_in_ext(rest_ext, extra_bits),
                                          run_pf, run_app, rest_lengths), rest_appended, rest_len)) | true, inp4, lengths3, byte4, bit4)
              end
              else let prval None_v() = rest_opt in (None_v() | false, inp4, lengths3, byte4, bit4) end
            end
            else (None_v() | false, inp3, lengths, byte3, bit3)
          end
          else let prval None_v() = extra_opt in (None_v() | false, inp3, lengths, byte3, bit3) end
        end
        else (None_v() | false, inp2, lengths, byte2, bit2)
      end
      else if sym = 18 then begin
        if true then let
          val (extra_opt | extra_ok, inp3, extra) = read_bits(inp2, byte2, bit2, 7)
          val @(byte3, bit3) = advance_position(byte2, bit2, 7)
        in
          if extra_ok then let
            prval Some_v(BITS_READ_mk(extra_ext, extra_bits, extra_len)) = extra_opt
            prval () = _bits_below_power(extra_bits, $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero()))))))))
          in
            if count + 11 + extra <= total then let
              val (run_pf, run_app, run_appended | lengths2) = write_run(so_far_len, appended | lengths, count, 11 + extra, 0)
              prval next_len = _append_clen(run_app, so_far_len, run_len(run_pf, $A.CLEN_nil()))
              val (rest_opt | rest_ok, inp4, lengths3, byte4, bit4) = read_code_lengths(next_len, run_appended | view, tab, inp3, lengths2, byte3, bit3, count + 11 + extra, total)
            in
              if rest_ok then let
                prval Some_v(CL_READ_mk(rest_ext, rest_lengths, rest_appended, rest_len)) = rest_opt
                prval sym_to_end = ext_trans(extra_ext, rest_ext)
              in
                (Some_v(CL_READ_mk(ext_trans(sym_ext, sym_to_end),
                                   CODE_LENGTHS_zeros_long(so_far_len, decsym_in_ext(sym_to_end, decoded), LENGTH_CLASS_zeros_long(), bits_in_ext(rest_ext, extra_bits),
                                          run_pf, run_app, rest_lengths), rest_appended, rest_len)) | true, inp4, lengths3, byte4, bit4)
              end
              else let prval None_v() = rest_opt in (None_v() | false, inp4, lengths3, byte4, bit4) end
            end
            else (None_v() | false, inp3, lengths, byte3, bit3)
          end
          else let prval None_v() = extra_opt in (None_v() | false, inp3, lengths, byte3, bit3) end
        end
        else (None_v() | false, inp2, lengths, byte2, bit2)
      end
      else (None_v() | false, inp2, lengths, byte2, bit2)
    end
    else let prval None_v() = sym_opt in (None_v() | false, inp2, lengths, byte2, bit2) end
  end

prfun code_lengths_from_len {order,values,lengths:$A.cells}{count,first_sym:nat | first_sym <= 19} .<19 - first_sym>.
  (from: CODE_LENGTHS_FROM(order, count, values, first_sym, lengths)): $A.CLEN(lengths, 19 - first_sym) =
  case+ from of
  | CODE_LENGTHS_FROM_end() => $A.CLEN_nil()
  | CODE_LENGTHS_FROM_cons(_, from_rest) => $A.CLEN_cons(code_lengths_from_len(from_rest))

prfun code_lengths_sized_len {code_length_code,source:$A.cells}{p,total,end_bit,steps:nat}{so_far,lengths:$A.cells} .<steps>.
  (sized: CODE_LENGTHS_SIZED(code_length_code, source, p, so_far, total, lengths, end_bit, steps)): $A.CLEN(lengths, total) =
  case+ sized of
  | CODE_LENGTHS_SIZED_done(so_far_len) => so_far_len
  | CODE_LENGTHS_SIZED_literal(_, _, _, _, rest) => code_lengths_sized_len(rest)
  | CODE_LENGTHS_SIZED_repeat_previous(_, _, _, _, _, _, _, rest) => code_lengths_sized_len(rest)
  | CODE_LENGTHS_SIZED_zeros_short(_, _, _, _, _, _, rest) => code_lengths_sized_len(rest)
  | CODE_LENGTHS_SIZED_zeros_long(_, _, _, _, _, _, rest) => code_lengths_sized_len(rest)

prfn code_lengths_len {code_length_code,source:$A.cells}{p,total,end_bit:nat}{so_far,lengths:$A.cells}
  (done: CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit)): $A.CLEN(lengths, total) =
  (case+ done of CODE_LENGTHS_made(sized) => code_lengths_sized_len(sized))

(* the shapes of a code that 3.2.7 takes *)
fn tables_full {lengths:$A.cells}{maxlen:nat | 1 <= maxlen; maxlen <= 15} (tab: !tables(lengths, maxlen), maxlen: int maxlen)
  : [ok:bool] (option_v(LENGTHS_FULL(lengths, maxlen), ok) | bool ok) =
  case+ tab of
  | @tables_made(table, fit | firsts, counts) => let
      val (first_nth | first) = $A.iarr_get(firsts, maxlen)
      val (count_nth | count) = $A.iarr_get(counts, maxlen)
      prval (next_pf, bl_pf) = table_lookup(table, first_nth, count_nth)
      val (pow_pf | power) = pow2_of(maxlen)
    in
      fold@(tab);
      if first + count = power then (Some_v(LENGTHS_FULL_mk(next_pf, bl_pf, pow_pf)) | true) else (None_v() | false)
    end

fn tables_single {lengths:$A.cells}{n,maxlen:nat | 1 <= n; 1 <= maxlen; maxlen <= 15}
  (view: !lengths_view(lengths, n), tab: !tables(lengths, maxlen), n: int n)
  : [ok:bool] (option_v(LENGTHS_SINGLE(lengths), ok) | bool ok) =
  case+ tab of
  | @tables_made(table, fit | firsts, counts) => let
      val (count_nth | ones) = $A.iarr_get(counts, 1)
      val (first_nth | _) = $A.iarr_get(firsts, 1)
      prval (next_pf, bl_pf) = table_lookup(table, first_nth, count_nth)
      prval BL_COUNT_mk(bl_len, ones_counted) = bl_pf
      val (view_len | ()) = lengths_len(view)
      prval () = _clen_functional(view_len, bl_len)
      val (zeros_counted | zeros) = count_scan(COUNT_BEFORE_zero() | view, n, 0, 0, 0)
    in
      fold@(tab);
      if ones = 1 then (if zeros = n - 1 then (Some_v(LENGTHS_SINGLE_mk(view_len, zeros_counted, ones_counted)) | true) else (None_v() | false)) else (None_v() | false)
    end

fn lengths_empty {lengths:$A.cells}{n:nat} (view: !lengths_view(lengths, n), n: int n)
  : [ok:bool] (option_v(LENGTHS_EMPTY(lengths), ok) | bool ok) = let
  val (lengths_len | ()) = lengths_len(view)
  val (zeros_counted | zeros) = count_scan(COUNT_BEFORE_zero() | view, n, 0, 0, 0)
in
  if zeros = n then (Some_v(LENGTHS_EMPTY_mk(lengths_len, zeros_counted)) | true) else (None_v() | false)
end

fn litlen_usable {lengths:$A.cells}{n:nat | 1 <= n} (view: !lengths_view(lengths, n), tab: !tables(lengths, 15), fit: LENGTHS_FIT(lengths, 15), n: int n)
  : [ok:bool] (option_v(LITLEN_USABLE(lengths), ok) | bool ok) = let
  val (full_opt | full_ok) = tables_full(tab, 15)
in
  if full_ok then let prval Some_v(full) = full_opt in (Some_v(LITLEN_USABLE_full(fit, full)) | true) end
  else let
    prval None_v() = full_opt
    val (single_opt | single_ok) = tables_single(view, tab, n)
  in
    if single_ok then let prval Some_v(single) = single_opt in (Some_v(LITLEN_USABLE_single(fit, single)) | true) end
    else let prval None_v() = single_opt in (None_v() | false) end
  end
end

fn dist_usable {lengths:$A.cells}{n:nat | 1 <= n} (view: !lengths_view(lengths, n), tab: !tables(lengths, 15), fit: LENGTHS_FIT(lengths, 15), n: int n)
  : [ok:bool] (option_v(DIST_USABLE(lengths), ok) | bool ok) = let
  val (full_opt | full_ok) = tables_full(tab, 15)
in
  if full_ok then let prval Some_v(full) = full_opt in (Some_v(DIST_USABLE_full(fit, full)) | true) end
  else let
    prval None_v() = full_opt
    val (single_opt | single_ok) = tables_single(view, tab, n)
  in
    if single_ok then let prval Some_v(single) = single_opt in (Some_v(DIST_USABLE_single(fit, single)) | true) end
    else let
      prval None_v() = single_opt
      val (empty_opt | empty_ok) = lengths_empty(view, n)
    in
      if empty_ok then let prval Some_v(empty) = empty_opt in (Some_v(DIST_USABLE_empty(fit, empty)) | true) end
      else let prval None_v() = empty_opt in (None_v() | false) end
    end
  end
end

dataprop CLC_READY($A.cells, $A.cells, int, int, $A.cells, $A.cells, int, int, int, int, int) =
  | {source,source2,values,order,clc:$A.cells}{p,count,front2,have2,size_in,byte2,bit2:nat | bit2 < 8; 8 * byte2 + bit2 == p + 3 * count; 8 * front2 <= p + 3 * count; p + 3 * count <= 8 * have2; have2 <= size_in}
    CLC_READY_mk(source, source2, p, count, values, clc, front2, have2, size_in, byte2, bit2)
    of (EXT(source, source2), READ_LENGTHS3(source2, p, count, values), CL_ORDER(order), CODE_LENGTHS_FROM(order, count, values, 0, clc), LENGTHS_FIT(clc, 7), LENGTHS_FULL(clc, 7), $A.CLEN(source2, have2))

(* the code length code of a dynamic block, or why there is none: its lengths read, placed by CL_ORDER, and checked *)
datavtype clc_result(addr, $A.cells, int, int, int, int) =
  | {owner:addr}{source,source2,values,clc:$A.cells}{p,count,front2,have2,first_byte,size_in,byte2,bit2:nat | front2 <= have2; have2 <= size_in; bit2 < 8}
    clc_ready(owner, source, p, count, first_byte, size_in)
    of (CLC_READY(source, source2, p, count, values, clc, front2, have2, size_in, byte2, bit2) |
        lengths_view(clc, 19), tables(clc, 7), input(owner, source2, front2, have2, first_byte, size_in), int byte2, int bit2)
  | {owner:addr}{source,source2:$A.cells}{p,count,front2,have2,first_byte,size_in:nat | front2 <= have2; have2 <= size_in}
    clc_failed(owner, source, p, count, first_byte, size_in) of (input(owner, source2, front2, have2, first_byte, size_in))

fn read_clc {owner:addr}{source:$A.cells}{front,have,first_byte,size_in,byte_pos,bit_pos,count:nat | 4 <= count; count <= 19; front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (inp: input(owner, source, front, have, first_byte, size_in), byte_pos: int byte_pos, bit_pos: int bit_pos, count: int count)
  : clc_result(owner, source, 8 * byte_pos + bit_pos, count, first_byte, size_in) = let
  val (values_cells_len | values_barr) = $A.barr_alloc(32)
  val (values_opt | values_ok, inp2, values2, byte2, bit2) = read_values($A.CLEN_nil(), $A.APPEND_nil() | inp, values_barr, byte_pos, bit_pos, 0, count)
in
  if values_ok then let
    prval Some_v(VALUES_READ_mk(values_ext, values_read, values_total, values_app, values_have)) = values_opt
    prval $A.CELLS_EQ_refl() = $A.append_functional(values_total, $A.APPEND_nil())
    prval values_len = _read_lengths3_clen(values_read)
    val (clc_cells_len | clc_barr) = $A.barr_alloc(320)
    val (filled | clc_barr2) = fill_clc(CL_ORDER_mk(), values_len, values_app, $A.CLEN_nil(), $A.APPEND_nil() | values2, clc_barr, count, 0)
    prval CLC_FILLED_mk(from, clc_total, clc_app) = filled
    prval $A.CELLS_EQ_refl() = $A.append_functional(clc_total, $A.APPEND_nil())
    val () = $A.barr_free(values2)
    val view = lengths_of_array(code_lengths_from_len(from), clc_app | clc_barr2)
  in
    case+ make_code(view, 19, 7) of
    | ~code_ok(fit | tab) => let
        val (full_opt | full_ok) = tables_full(tab, 7)
      in
        if full_ok then let
          prval Some_v(full) = full_opt
        in clc_ready(CLC_READY_mk(values_ext, values_read, CL_ORDER_mk(), from, fit, full, values_have) | view, tab, inp2, byte2, bit2) end
        else let
          prval None_v() = full_opt
          val () = free_tables(tab)
          val () = free_view(view)
        in clc_failed(inp2) end
      end
    | ~code_refused() => let
        val () = free_view(view)
      in clc_failed(inp2) end
  end
  else let
    prval None_v() = values_opt
    val () = $A.barr_free(values2)
  in clc_failed(inp2) end
end

dataprop DATA_READ($A.cells, $A.cells, $A.cells, $A.cells, int, $A.cells, $A.cells, int, int, int, int) =
  | {litlen,dist,source,source2,out,out2:$A.cells}{p0,end_bit,front2,have2,size_in:nat | p0 < end_bit; 8 * front2 <= end_bit; end_bit <= 8 * have2; have2 <= size_in}
    DATA_READ_mk(litlen, dist, source, source2, p0, out, out2, end_bit, front2, have2, size_in)
    of (EXT(source, source2), LITLEN_USABLE(litlen), DIST_USABLE(dist), SYMS(litlen, dist, source2, p0, out, out2, end_bit), $A.CLEN(source2, have2))

(* the two codes of a dynamic block from their lengths, and the symbols they code *)
fn read_dynamic_data {in_memory:bool}{owner:addr}{litlen,dist,joined,junk,cells,source,out:$A.cells}{nlit,ndist:nat | 1 <= nlit; nlit <= 320; 1 <= ndist; ndist <= 320; nlit + ndist <= 320}{written:nat}{l:agz}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (litlen_len: $A.CLEN(litlen, nlit), dist_len: $A.CLEN(dist, ndist), joined_app: $A.APPEND(litlen, joined, cells), dist_app: $A.APPEND(dist, junk, joined) |
   lengths: $A.barr(l, 320, cells), inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, out, written),
   byte_pos: int byte_pos, bit_pos: int bit_pos, nlit: int nlit, ndist: int ndist)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][out2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(DATA_READ(litlen, dist, source, source2, 8 * byte_pos + bit_pos, out, out2, 8 * byte2 + bit2, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, out2, written2), int byte2, int bit2) = let
  val (dist_cells_len | dist_barr) = $A.barr_alloc(320)
  val (copied, dist_new_len | dist_barr2) = copy_range(litlen_len, dist_len, joined_app, dist_app, $A.CLEN_nil(), $A.APPEND_nil(), $A.APPEND_nil(), dist_cells_len | lengths, dist_barr, 0, nlit, ndist)
  val litlen_view = lengths_of_array(litlen_len, joined_app | lengths)
  val dist_view = lengths_of_array(dist_len, copied | dist_barr2)
  val litlen_code = make_code(litlen_view, nlit, 15)
  val dist_code = make_code(dist_view, ndist, 15)
in
  case+ litlen_code of
  | ~code_ok(litlen_fit | litlen_tab) =>
    (case+ dist_code of
     | ~code_ok(dist_fit | dist_tab) => let
         val (litlen_opt | litlen_ok) = litlen_usable(litlen_view, litlen_tab, litlen_fit, nlit)
         val (dist_opt | dist_ok) = dist_usable(dist_view, dist_tab, dist_fit, ndist)
       in
         if litlen_ok then begin
           if dist_ok then let
             prval Some_v(litlen_usable_pf) = litlen_opt
             prval Some_v(dist_usable_pf) = dist_opt
             val (have_len | _) = input_have(inp)
             val (syms_opt | syms_ok, inp2, snk2, byte2, bit2) =
               symbols_loop(SYMS_PREFIX_empty(), ext_refl(have_len) | litlen_view, litlen_tab, nlit, dist_view, dist_tab, ndist, inp, snk, byte_pos, bit_pos)
             val () = free_tables(litlen_tab)
             val () = free_tables(dist_tab)
             val () = free_view(litlen_view)
             val () = free_view(dist_view)
           in
             if syms_ok then let
               prval Some_v(SYMS_DONE_mk(syms_ext, syms, syms_len)) = syms_opt
             in (Some_v(DATA_READ_mk(syms_ext, litlen_usable_pf, dist_usable_pf, syms, syms_len)) | true, inp2, snk2, byte2, bit2) end
             else let prval None_v() = syms_opt in (None_v() | false, inp2, snk2, byte2, bit2) end
           end
           else let
             prval Some_v(litlen_usable_pf) = litlen_opt
             prval None_v() = dist_opt
             val () = free_tables(litlen_tab)
             val () = free_tables(dist_tab)
             val () = free_view(litlen_view)
             val () = free_view(dist_view)
           in (None_v() | false, inp, snk, 0, 0) end
         end
         else let
           prval None_v() = litlen_opt
           prval () = (case+ dist_opt of Some_v(_) => () | None_v() => ())
           val () = free_tables(litlen_tab)
           val () = free_tables(dist_tab)
           val () = free_view(litlen_view)
           val () = free_view(dist_view)
         in (None_v() | false, inp, snk, 0, 0) end
       end
     | ~code_refused() => let
         val () = free_tables(litlen_tab)
         val () = free_view(litlen_view)
         val () = free_view(dist_view)
       in (None_v() | false, inp, snk, 0, 0) end)
  | ~code_refused() => let
      val () = free_view(litlen_view)
      val () = free_view(dist_view)
      val () = (case+ dist_code of ~code_ok(_ | tab) => free_tables(tab) | ~code_refused() => ())
    in (None_v() | false, inp, snk, 0, 0) end
end

(* a block with codes of its own (3.2.7), its three header bits read *)
fn decode_dynamic {in_memory:bool}{owner:addr}{source:$A.cells}{out:$A.cells}{written:nat}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, out, written), byte_pos: int byte_pos, bit_pos: int bit_pos)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][out2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(BLOCK_DONE(block_dynamic(), source, source2, 8 * byte_pos + bit_pos, out, out2, 8 * byte2 + bit2, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, out2, written2), int byte2, int bit2) = let
  val (hlit_opt | hlit_ok, inp2, hlit) = read_bits(inp, byte_pos, bit_pos, 5)
  val @(byte1, bit1) = advance_position(byte_pos, bit_pos, 5)
in
  if hlit_ok then let
    prval Some_v(BITS_READ_mk{hlit_src1,hlit_src2}{hlit_f2,hlit_h2,hlit_sz,hlit_bp,hlit_bi,hlit_w,hlit_s}(hlit_ext, hlit_bits, hlit_len)) = hlit_opt
    val (hdist_opt | hdist_ok, inp3, hdist) = read_bits(inp2, byte1, bit1, 5)
    val @(byte2, bit2) = advance_position(byte1, bit1, 5)
  in
    if hdist_ok then let
      prval Some_v(BITS_READ_mk{hdist_src1,hdist_src2}{hdist_f2,hdist_h2,hdist_sz,hdist_bp,hdist_bi,hdist_w,hdist_s}(hdist_ext, hdist_bits, hdist_len)) = hdist_opt
      val (hclen_opt | hclen_ok, inp4, hclen) = read_bits(inp3, byte2, bit2, 4)
      val @(byte3, bit3) = advance_position(byte2, bit2, 4)
    in
      if hclen_ok then let
        prval Some_v(BITS_READ_mk(hclen_ext, hclen_bits, hclen_len)) = hclen_opt
        prval () = _bits_below_power(hclen_bits, $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_zero())))))
      in
        if hlit <= 29 then begin
          if hdist <= 29 then begin
            case+ read_clc(inp4, byte3, bit3, hclen + 4) of
            | ~clc_ready(ready | clc_view, clc_tab, inp5, byte5, bit5) => let
                prval CLC_READY_mk(clc_ext, values_read, order, from, clc_fit, clc_full, clc_len) = ready
                val (lengths_cells_len | lengths_barr) = $A.barr_alloc(320)
                val (cl_opt | cl_ok, inp6, lengths2, byte6, bit6) =
                  read_code_lengths($A.CLEN_nil(), $A.APPEND_nil() | clc_view, clc_tab, inp5, lengths_barr, byte5, bit5, 0, hlit + 257 + hdist + 1)
                val () = free_tables(clc_tab)
                val () = free_view(clc_view)
              in
                if cl_ok then let
                  prval Some_v(CL_READ_mk(cl_ext, cl_lengths, cl_app, cl_len)) = cl_opt
                  prval total_len = code_lengths_len(cl_lengths)
                  prval (litlen_len, dist_len, split) = append_split{hlit_s + 257 + hdist_s + 1, hlit_s + 257}(total_len)
                  prval $A.APPEND_made(split_sized) = split
                  prval (dist_app, joined_app) = append_compose(split_sized, cl_app)
                  val (data_opt | data_ok, inp7, snk2, byte7, bit7) =
                    read_dynamic_data(litlen_len, dist_len, joined_app, dist_app | lengths2, inp6, snk, byte6, bit6, hlit + 257, hdist + 1)
                in
                  if data_ok then let
                    prval Some_v(DATA_READ_mk(data_ext, litlen_usable_pf, dist_usable_pf, syms, data_len)) = data_opt
                    prval from_data = ext_trans(cl_ext, data_ext)
                    prval to_end = ext_trans(clc_ext, from_data)
                    prval hclen_to_end = ext_trans(hclen_ext, to_end)
                    prval hdist_to_end = ext_trans(hdist_ext, hclen_to_end)
                    prval hlit_to_end = ext_trans(hlit_ext, hdist_to_end)
                  in
                    (Some_v(BLOCK_DONE_mk(hlit_to_end,
                       BLOCK_dynamic(bits_in_ext(hdist_to_end, hlit_bits), bits_in_ext(hclen_to_end, hdist_bits), bits_in_ext(to_end, hclen_bits),
                                     read_lengths3_in_ext(from_data, values_read), order, from, clc_fit, clc_full,
                                     code_lengths_in_ext(data_ext, cl_lengths), litlen_len, split, litlen_usable_pf, dist_usable_pf, syms),
                       data_len)) | true, inp7, snk2, byte7, bit7)
                  end
                  else let prval None_v() = data_opt in (None_v() | false, inp7, snk2, byte7, bit7) end
                end
                else let
                  prval None_v() = cl_opt
                  val () = $A.barr_free(lengths2)
                in (None_v() | false, inp6, snk, byte6, bit6) end
              end
            | ~clc_failed(inp5) => (None_v() | false, inp5, snk, 0, 0)
          end
          else (None_v() | false, inp4, snk, byte3, bit3)
        end
        else (None_v() | false, inp4, snk, byte3, bit3)
      end
      else let prval None_v() = hclen_opt in (None_v() | false, inp4, snk, byte3, bit3) end
    end
    else let prval None_v() = hdist_opt in (None_v() | false, inp3, snk, byte2, bit2) end
  end
  else let prval None_v() = hlit_opt in (None_v() | false, inp2, snk, byte1, bit1) end
end

dataprop BLOCK_PACKED($A.cells, $A.cells, int, int, $A.cells, $A.cells, int, int, int, int) =
  | {source,source2:$A.cells}{kind:block_kind}{body_start,btype,end_bit,front2,have2,size_in:nat | body_start <= end_bit; 8 * front2 <= end_bit; end_bit <= 8 * have2; have2 <= size_in}{out,out2:$A.cells}
    BLOCK_PACKED_mk(source, source2, body_start, btype, out, out2, end_bit, front2, have2, size_in)
    of (EXT(source, source2), BTYPE(kind, btype), BLOCK(kind, source2, body_start, out, out2, end_bit), $A.CLEN(source2, have2))

(* the block of type btype whose body starts at the position byte_pos, bit_pos *)
fn decode_block {in_memory:bool}{owner:addr}{source:$A.cells}{out:$A.cells}{written:nat}
  {front,have,first_byte,size_in,byte_pos,bit_pos,btype:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8}
  (inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, out, written), byte_pos: int byte_pos, bit_pos: int bit_pos, btype: int btype, stored_only: bool)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][out2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(BLOCK_PACKED(source, source2, 8 * byte_pos + bit_pos, btype, out, out2, 8 * byte2 + bit2, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, out2, written2), int byte2, int bit2) =
  if btype = 0 then let
    val (block_opt | block_ok, inp2, snk2, end_byte) = decode_stored(inp, snk, byte_pos, bit_pos)
  in
    if block_ok then let
      prval Some_v(BLOCK_DONE_mk(block_ext, block, block_len)) = block_opt
    in (Some_v(BLOCK_PACKED_mk(block_ext, BTYPE_stored(), block, block_len)) | true, inp2, snk2, end_byte, 0) end
    else let prval None_v() = block_opt in (None_v() | false, inp2, snk2, 0, 0) end
  end
  else if stored_only then (None_v() | false, inp, snk, 0, 0)
  else if btype = 1 then let
    val (block_opt | block_ok, inp2, snk2, byte2, bit2) = decode_fixed(inp, snk, byte_pos, bit_pos)
  in
    if block_ok then let
      prval Some_v(BLOCK_DONE_mk(block_ext, block, block_len)) = block_opt
    in (Some_v(BLOCK_PACKED_mk(block_ext, BTYPE_fixed(), block, block_len)) | true, inp2, snk2, byte2, bit2) end
    else let prval None_v() = block_opt in (None_v() | false, inp2, snk2, 0, 0) end
  end
  else if btype = 2 then let
    val (block_opt | block_ok, inp2, snk2, byte2, bit2) = decode_dynamic(inp, snk, byte_pos, bit_pos)
  in
    if block_ok then let
      prval Some_v(BLOCK_DONE_mk(block_ext, block, block_len)) = block_opt
    in (Some_v(BLOCK_PACKED_mk(block_ext, BTYPE_dynamic(), block, block_len)) | true, inp2, snk2, byte2, bit2) end
    else let prval None_v() = block_opt in (None_v() | false, inp2, snk2, 0, 0) end
  end
  else (None_v() | false, inp, snk, 0, 0)

(* BLOCK_STEP(source, p, out, end_bit, out2): a block that is not the last, from bit p, takes the output out to out2 and ends at end_bit *)
dataprop BLOCK_STEP($A.cells, int, $A.cells, int, $A.cells) =
  | {source:$A.cells}{kind:block_kind}{p,btype,end_bit:nat}{out,out2:$A.cells}
    BLOCK_STEP_mk(source, p, out, end_bit, out2)
    of (BITS(source, p, 1, 0), BITS(source, p + 1, 2, btype), BTYPE(kind, btype), BLOCK(kind, source, p + 3, out, out2, end_bit))

(* BLOCKS_PREFIX(source, p0, out0, p, out, count): count blocks from bit p0, none the last, take the output out0 to out and end at bit p *)
dataprop BLOCKS_PREFIX($A.cells, int, $A.cells, int, $A.cells, int) =
  | {source:$A.cells}{p:nat}{out:$A.cells} BLOCKS_PREFIX_empty(source, p, out, p, out, 0)
  | {source_before,source:$A.cells}{p0,p,end_bit,count:nat}{out0,out,out2:$A.cells}
    BLOCKS_PREFIX_step(source, p0, out0, end_bit, out2, count + 1)
    of (BLOCKS_PREFIX(source_before, p0, out0, p, out, count), EXT(source_before, source), BLOCK_STEP(source, p, out, end_bit, out2))

prfun blocks_close {source,source_end:$A.cells}{p0,p,count:nat}{out0,out,after:$A.cells} .<count>.
  (leading: BLOCKS_PREFIX(source, p0, out0, p, out, count), ext: EXT(source, source_end), rest: BLOCKS(source_end, p, out, after))
  : BLOCKS(source_end, p0, out0, after) =
  case+ leading of
  | BLOCKS_PREFIX_empty() => rest
  | BLOCKS_PREFIX_step(leading_before, step_ext, step) =>
    (case+ step of
     | BLOCK_STEP_mk(final_bit, type_bits, btype_pf, block) =>
       blocks_close(leading_before, ext_trans(step_ext, ext),
                    BLOCKS_next(bits_in_ext(ext, final_bit), bits_in_ext(ext, type_bits), btype_pf, block_in_ext(ext, block), rest)))

dataprop BLOCKS_DONE($A.cells, $A.cells, $A.cells, int, int, int, int) =
  | {entry,source2:$A.cells}{end_bit,front2,have2,size_in:nat | 8 * front2 <= end_bit; end_bit <= 8 * have2; have2 <= size_in}{out2:$A.cells}
    BLOCKS_DONE_mk(entry, source2, out2, end_bit, front2, have2, size_in) of (EXT(entry, source2), BLOCKS(source2, 0, $A.cnil(), out2), $A.CLEN(source2, have2))

(* every block of the stream, to the last one *)
fun blocks_loop {in_memory:bool}{owner:addr}{entry,source:$A.cells}{count:nat}{out:$A.cells}{written:nat}
  {front,have,first_byte,size_in,byte_pos,bit_pos:nat | front <= byte_pos; front <= have; have <= size_in; 8 * byte_pos + bit_pos <= 8 * have; bit_pos < 8} .<8 * size_in - (8 * byte_pos + bit_pos)>.
  (leading: BLOCKS_PREFIX(source, 0, $A.cnil(), 8 * byte_pos + bit_pos, out, count), entry_ext: EXT(entry, source) |
   inp: input(owner, source, front, have, first_byte, size_in), snk: sink(in_memory, out, written), byte_pos: int byte_pos, bit_pos: int bit_pos, stored_only: bool)
  : [source2:$A.cells][front2,have2:nat | front2 <= have2; have2 <= size_in][out2:$A.cells][written2:nat][byte2,bit2:nat | bit2 < 8][ok:bool]
    (option_v(BLOCKS_DONE(entry, source2, out2, 8 * byte2 + bit2, front2, have2, size_in), ok) |
     bool ok, input(owner, source2, front2, have2, first_byte, size_in), sink(in_memory, out2, written2), int byte2, int bit2) = let
  val (final_opt | final_ok, inp2, final_bit) = read_bit(inp, byte_pos, bit_pos)
  val @(byte2, bit2) = next_position(byte_pos, bit_pos)
in
  if final_ok then let
    prval Some_v(BIT_READ_mk(final_ext, final_pf, final_len)) = final_opt
    prval final_bits = BITS_cons(final_pf, BITS_nil())
    val (type_opt | type_ok, inp3, btype) = read_bits(inp2, byte2, bit2, 2)
    val @(byte3, bit3) = advance_position(byte2, bit2, 2)
  in
    if type_ok then let
      prval Some_v(BITS_READ_mk(type_ext, type_bits, type_len)) = type_opt
      val (block_opt | block_ok, inp4, snk2, byte4, bit4) = decode_block(inp3, snk, byte3, bit3, btype, stored_only)
    in
      if block_ok then let
        prval Some_v(BLOCK_PACKED_mk(block_ext, btype_pf, block, block_len)) = block_opt
        prval header_ext = ext_trans(type_ext, block_ext)
        prval source_ext = ext_trans(final_ext, header_ext)
        prval final_bits2 = bits_in_ext(header_ext, final_bits)
        prval type_bits2 = bits_in_ext(block_ext, type_bits)
      in
        if final_bit = 1 then
          (Some_v(BLOCKS_DONE_mk(ext_trans(entry_ext, source_ext),
                                 blocks_close(leading, source_ext, BLOCKS_last(final_bits2, type_bits2, btype_pf, block)), block_len)) | true, inp4, snk2, byte4, bit4)
        else
          blocks_loop(BLOCKS_PREFIX_step(leading, source_ext, BLOCK_STEP_mk(bits_in_ext(header_ext, final_bits), type_bits2, btype_pf, block)),
                      ext_trans(entry_ext, source_ext) | inp4, snk2, byte4, bit4, stored_only)
      end
      else let prval None_v() = block_opt in (None_v() | false, inp4, snk2, byte4, bit4) end
    end
    else let prval None_v() = type_opt in (None_v() | false, inp3, snk, byte3, bit3) end
  end
  else let prval None_v() = final_opt in (None_v() | false, inp2, snk, byte2, bit2) end
end

prfun blocks_sized_in_ext {source,source2:$A.cells}{p,blocks:nat}{before,after:$A.cells} .<blocks>.
  (ext: EXT(source, source2), blocks: BLOCKS_SIZED(source, p, before, after, blocks)): BLOCKS_SIZED(source2, p, before, after, blocks) =
  case+ blocks of
  | BLOCKS_SIZED_last(final_bits, type_bits, btype_pf, block) =>
    BLOCKS_SIZED_last(bits_in_ext(ext, final_bits), bits_in_ext(ext, type_bits), btype_pf, block_in_ext(ext, block))
  | BLOCKS_SIZED_next(final_bits, type_bits, btype_pf, block, rest) =>
    BLOCKS_SIZED_next(bits_in_ext(ext, final_bits), bits_in_ext(ext, type_bits), btype_pf, block_in_ext(ext, block), blocks_sized_in_ext(ext, rest))

prfun blocks_in_ext {source,source2:$A.cells}{p:nat}{before,after:$A.cells} .<>.
  (ext: EXT(source, source2), blocks: BLOCKS(source, p, before, after)): BLOCKS(source2, p, before, after) =
  (case+ blocks of BLOCKS_made(sized) => BLOCKS_made(blocks_sized_in_ext(ext, sized)))

(* ===== the in-memory forms: array's barr in, array's barr out (keyword: decoder) ===== *)

prfn ext_same {a,b:$A.cells}{n,m:nat | m <= n} (ext: EXT(a, b), a_len: $A.CLEN(a, n), b_len: $A.CLEN(b, m)): $A.CELLS_EQ(a, b) =
  case+ ext of
  | EXT_mk($A.APPEND_made(sized)) => let
      prval () = _clen_functional(a_len, _append_sized_len(sized))
      prval rest_len = append_rest_len(sized, b_len)
      prval $A.CELLS_EQ_refl() = clen_zero(rest_len)
    in append_nil_right(sized) end

(* the cells of a borrowed array copied into a new array of the same size, one at a time *)
fun copy_borrowed {cells,leading,rest,new_junk,new_cells:$A.cells}{n,i:nat | i <= n}{l1,l2:agz} .<n - i>.
  (cells_len: $A.CLEN(cells, n), leading_len: $A.CLEN(leading, i), split: $A.APPEND(leading, rest, cells), filled: $A.APPEND(leading, new_junk, new_cells), new_len: $A.CLEN(new_cells, n) |
   old: !$A.cborrow(l1, n, cells), new: $A.barr(l2, n, new_cells), n: int n, i: int i)
  : [new_cells2:$A.cells] ($A.CELLS_EQ(cells, new_cells2) | $A.barr(l2, n, new_cells2)) =
  if i >= n then let
    prval $A.APPEND_made(split_sized) = split
    prval () = _clen_functional(leading_len, _append_sized_len(split_sized))
    prval rest_len = append_rest_len(split_sized, cells_len)
    prval $A.CELLS_EQ_refl() = clen_zero(rest_len)
    prval $A.CELLS_EQ_refl() = append_nil_right(split_sized)
    prval $A.APPEND_made(filled_sized) = filled
    prval () = _clen_functional(leading_len, _append_sized_len(filled_sized))
    prval junk_len = append_rest_len(filled_sized, new_len)
    prval $A.CELLS_EQ_refl() = clen_zero(junk_len)
    prval $A.CELLS_EQ_refl() = append_nil_right(filled_sized)
  in ($A.CELLS_EQ_refl() | new) end
  else let
    val (found | v) = $A.cborrow_get(old, i)
    prval $A.APPEND_made(split_sized) = split
    prval () = _clen_functional(leading_len, _append_sized_len(split_sized))
    prval (snoc, peeled) = append_peel(split_sized, found)
    val (set | new2) = $A.barr_set(new, i, v)
    prval $A.APPEND_made(filled_sized) = filled
    prval (snoc_set, filled2) = append_setc(leading_len, filled_sized, set)
    prval $A.CELLS_EQ_refl() = $A.append_functional(snoc, snoc_set)
    prval next_len = _append_clen(snoc, leading_len, $A.CLEN_cons($A.CLEN_nil()))
    prval new_len2 = $A.setc_len(set, new_len)
  in copy_borrowed(cells_len, next_len, peeled, filled2, new_len2 | old, new2, n, i + 1) end

#pub datavtype inflated_cells(compressed: $A.cells) =
  | {output:$A.cells}{size:pos | size <= 1048576}{l:agz}
    inflated_cells_done(compressed) of (INFLATES(inflate_deflated(), compressed, output), $A.CLEN(output, size) | $A.barr(l, size, output))
  | inflated_cells_empty(compressed) of (INFLATES(inflate_deflated(), compressed, $A.cnil()) | )
  | inflated_cells_malformed(compressed) of ()
  | inflated_cells_too_large(compressed) of ()

fn memory_inflate {l:agz}{n:nat | n <= 1048576}{cs:$A.cells}
  (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n, stored_only: bool)
  : inflated_cells(cs) =
  if n = 0 then inflated_cells_malformed()
  else let
    val (new_len | new_barr) = $A.barr_alloc(n)
    val (copied | input_barr) = copy_borrowed(size, $A.CLEN_nil(), $A.APPEND_nil(), $A.APPEND_nil(), new_len | compressed, new_barr, n, 0)
    prval $A.CELLS_EQ_refl() = copied
    val inp = input_memory(size | input_barr, n)
    val (out_len | out_barr) = $A.barr_alloc(1048576)
    val snk = sink_memory($A.CLEN_nil(), $A.APPEND_nil() | out_barr, 0)
    val (done_opt | ok, inp2, snk2, byte2, bit2) = blocks_loop(BLOCKS_PREFIX_empty(), ext_refl(size) | inp, snk, 0, 0, stored_only)
    val () = (case+ inp2 of ~input_memory(_ | held, _) => $A.barr_free(held))
  in
    if ok then let
      prval Some_v(BLOCKS_DONE_mk(done_ext, blocks, done_len)) = done_opt
      prval $A.CELLS_EQ_refl() = ext_same(done_ext, size, done_len)
    in
      case+ snk2 of
      | ~sink_memory(output_len, output_app | output_barr, written) =>
        if written = 0 then let
          prval $A.CELLS_EQ_refl() = clen_zero(output_len)
          val () = $A.barr_free(output_barr)
        in inflated_cells_empty(INFLATES_deflated(blocks) | ) end
        else let
          val (exact_len | exact) = $A.barr_alloc(written)
          val (copied2, exact_len2 | exact2) =
            copy_range($A.CLEN_nil(), output_len, $A.APPEND_nil(), output_app, $A.CLEN_nil(), $A.APPEND_nil(), $A.APPEND_nil(), exact_len | output_barr, exact, 0, 0, written)
          prval $A.APPEND_made(copied_sized) = copied2
          prval () = _clen_functional(output_len, _append_sized_len(copied_sized))
          prval junk_len = append_rest_len(copied_sized, exact_len2)
          prval $A.CELLS_EQ_refl() = clen_zero(junk_len)
          prval $A.CELLS_EQ_refl() = append_nil_right(copied_sized)
          val () = $A.barr_free(output_barr)
        in inflated_cells_done(INFLATES_deflated(blocks), output_len | exact2) end
      | ~sink_memory_overflow(output_barr) => let
          val () = $A.barr_free(output_barr)
        in inflated_cells_empty(INFLATES_deflated(blocks) | ) end
    end
    else let
      prval None_v() = done_opt
    in
      case+ snk2 of
      | ~sink_memory(_, _ | output_barr, _) => ($A.barr_free(output_barr); inflated_cells_malformed())
      | ~sink_memory_overflow(output_barr) => ($A.barr_free(output_barr); inflated_cells_too_large())
    end
  end

#pub fun inflate_stored_cells_proved {l:agz}{n:nat | n <= 1048576}{cs:$A.cells}
  (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): inflated_cells(cs)

#pub fun inflate_cells_proved {l:agz}{n:nat | n <= 1048576}{cs:$A.cells}
  (size: $A.CLEN(cs, n) | compressed: !$A.cborrow(l, n, cs), n: int n): inflated_cells(cs)

implement inflate_stored_cells_proved {l}{n}{cs} (size | compressed, n) = memory_inflate(size | compressed, n, true)

implement inflate_cells_proved {l}{n}{cs} (size | compressed, n) = memory_inflate(size | compressed, n, false)

#target native begin

(* ===== batch 16: the reader and writer forms ===== *)

#pub stadef INFLATE_OUTPUT_MOST = 2147483647

#pub datavtype reader_fate(int, int) =
  | {compressed:$A.cells}{start,size_in:nat} reader_ended(start, size_in) of ($F.FILE_READ(compressed, start, size_in) | )
  | {start,size_in:nat} reader_closed_early(start, size_in) of ()
  | {start,size_in:nat} reader_lost(start, size_in) of ($F.io_error)

#pub datavtype writer_fate =
  | {written:$A.cells} writer_held of ($F.FILE_HOLDS(written) | )
  | writer_lost of ($F.io_error)

#pub datatype inflate_failure =
  | failure_malformed
  | failure_read
  | failure_write
  | failure_too_large

#pub datavtype inflated(int, int) =
  | {compressed,output:$A.cells}{start,size_in,size:nat | size <= INFLATE_OUTPUT_MOST}
    inflated_done(start, size_in) of (INFLATES(inflate_deflated(), compressed, output), $A.CLEN(compressed, size_in), $A.CLEN(output, size),
                                      $F.FILE_READ(compressed, start, size_in), $F.FILE_HOLDS(output) | int size)
  | {compressed,output:$A.cells}{start,size_in:nat}
    inflated_decoded_unsaved(start, size_in) of (INFLATES(inflate_deflated(), compressed, output), $F.FILE_READ(compressed, start, size_in) | $F.io_error)
  | {start,size_in:nat} inflated_stopped(start, size_in) of (inflate_failure, reader_fate(start, size_in), writer_fate)

(* what is left of the entry's range once the blocks are decoded: read to its end *)
datavtype drained(int, int, $A.cells) =
  | {source,source2:$A.cells}{start,size_in:nat} drained_limit(start, size_in, source)
    of (EXT(source, source2), $F.FILE_READ(source2, start, size_in), $A.CLEN(source2, size_in) | )
  | {source,source2:$A.cells}{start,size_in:nat} drained_eof(start, size_in, source) of (EXT(source, source2), $F.FILE_READ(source2, start, size_in) | )
  | {source:$A.cells}{start,size_in:nat} drained_failed(start, size_in, source) of ($F.io_error)
  | {source:$A.cells}{start,size_in:nat} drained_overrun(start, size_in, source) of ()

fun input_drain {source,entry:$A.cells}{front,have,first_byte,size_in:nat | front <= have; have <= size_in} .<size_in - have>.
  (entry_ext: EXT(entry, source) | inp: input(null, source, front, have, first_byte, size_in), have: int have)
  : drained(first_byte, size_in, entry) =
  case+ input_more(inp, have) of
  | ~more_ready(more_ext, more_len | inp2) => let
      val (_ | have2) = input_have(inp2)
    in input_drain(ext_trans(entry_ext, more_ext) | inp2, have2) end
  | ~more_unavailable(inp2) => begin
      case+ inp2 of
      | ~input_external(_, _, _, ext) =>
        (case+ ext of
         | ~external_limit(file_read, whole_len, _ | ) => drained_limit(entry_ext, file_read, whole_len | )
         | ~external_eof(file_read, _ | ) => drained_eof(entry_ext, file_read | )
         | ~external_failed(_ | failure) => drained_failed(failure)
         | ~external_overrun(_ | ) => drained_overrun()
         | ~external_reading(_, _, _, _ | reader, buffer) => ($F.content_reader_close(reader); $A.barr_free(buffer); drained_overrun()))
    end

datavtype sink_closed($A.cells, int) =
  | {output:$A.cells}{written:nat | written <= INFLATE_OUTPUT_MOST} sink_closed_held(output, written) of ($A.CLEN(output, written), $F.FILE_HOLDS(output) | int written)
  | {output,held:$A.cells}{written:nat} sink_closed_partial(output, written) of ($F.FILE_HOLDS(held) | )
  | {output:$A.cells}{written:nat} sink_closed_lost(output, written) of ($F.io_error)

(* closes the writer of a streaming sink, which is over: the fate of the file *)
fn close_sink {output:$A.cells}{written:nat} (snk: sink(false, output, written)): sink_closed(output, written) =
  case+ snk of
  | ~sink_streaming(output_len, _, _, _ | writer, buffer, written, _) => let
      val () = $A.barr_free(buffer)
    in
      case+ writer of
      | ~writer_live(file_writer) =>
        (case+ $F.content_close(file_writer) of
         | ~$F.content_closed(holds | _) => sink_closed_held(output_len, holds | written)
         | ~$F.content_close_failed(failure) => sink_closed_lost(failure))
      | ~writer_failed(failure) => sink_closed_lost(failure)
    end
  | ~sink_streaming_stopped(writer, buffer) => let
      val () = $A.barr_free(buffer)
    in
      case+ writer of
      | ~writer_live(file_writer) =>
        (case+ $F.content_close(file_writer) of
         | ~$F.content_closed(holds | _) => sink_closed_partial(holds | )
         | ~$F.content_close_failed(failure) => sink_closed_lost(failure))
      | ~writer_failed(failure) => sink_closed_lost(failure)
    end

fn writer_fate_of {output:$A.cells}{written:nat} (closed: sink_closed(output, written)): writer_fate =
  case+ closed of
  | ~sink_closed_held(_, holds | _) => writer_held(holds | )
  | ~sink_closed_partial(holds | ) => writer_held(holds | )
  | ~sink_closed_lost(failure) => writer_lost(failure)

fn reader_fate_of {source:$A.cells}{front,have,first_byte,size_in:nat} (inp: input(null, source, front, have, first_byte, size_in)): reader_fate(first_byte, size_in) =
  case+ inp of
  | ~input_external(_, _, _, ext) =>
    (case+ ext of
     | ~external_reading(_, _, _, _ | reader, buffer) => ($F.content_reader_close(reader); $A.barr_free(buffer); reader_closed_early())
     | ~external_limit(file_read, _, _ | ) => reader_ended(file_read | )
     | ~external_eof(file_read, _ | ) => reader_ended(file_read | )
     | ~external_failed(_ | failure) => reader_lost(failure)
     | ~external_overrun(_ | ) => reader_closed_early())

(* 1 when the input could not be read (a failed read, or more than the entry's range), else 0 *)
fn input_unreadable {source:$A.cells}{front,have,first_byte,size_in:nat} (inp: !input(null, source, front, have, first_byte, size_in)): int =
  case+ inp of
  | @input_external(front_value, have_value, limit_value, ext) => (case+ ext of
      | @external_failed(failed_len | failure) => (fold@(ext); fold@(inp); 1)
      | @external_overrun(overrun_len | ) => (fold@(ext); fold@(inp); 1)
      | @external_reading(chunk_len, chunk_holds, previous_len, chunk_app | reader, buffer) => (fold@(ext); fold@(inp); 0)
      | @external_limit(limit_read, limit_len, limit_have | ) => (fold@(ext); fold@(inp); 0)
      | @external_eof(eof_read, eof_have | ) => (fold@(ext); fold@(inp); 0))

(* 1 when the writer failed, 2 when the output is over its bound, else 0 *)
fn sink_stopped_by {output:$A.cells}{written:nat} (snk: !sink(false, output, written)): int =
  case+ snk of
  | @sink_streaming(output_len, held_len, appended, tail | writer, buffer, written_value, fill) => (fold@(snk); 0)
  | @sink_streaming_stopped(writer, buffer) => (case+ writer of
      | @writer_failed(failure) => (fold@(writer); fold@(snk); 1)
      | @writer_live(file_writer) => (fold@(writer); fold@(snk); 2))

fn stopped_result {source,output:$A.cells}{front,have,first_byte,size_in,written:nat}
  (inp: input(null, source, front, have, first_byte, size_in), snk: sink(false, output, written)): inflated(first_byte, size_in) = let
  val unreadable = input_unreadable(inp)
  val stopped_by = sink_stopped_by(snk)
  val reader = reader_fate_of(inp)
  val writer = writer_fate_of(close_sink(snk))
in
  if unreadable = 1 then inflated_stopped(failure_read, reader, writer)
  else if stopped_by = 1 then inflated_stopped(failure_write, reader, writer)
  else if stopped_by = 2 then inflated_stopped(failure_too_large, reader, writer)
  else inflated_stopped(failure_malformed, reader, writer)
end

fn file_inflate {start,size_in:nat}
  (reader: $F.content_reader($A.cnil(), start, size_in), writer: $F.content_writer($A.cnil()), start: int start, size_in: int size_in, stored_only: bool)
  : inflated(start, size_in) = let
  val (buffer_len | buffer) = $A.barr_alloc(16384)
  val ext = external_reading($A.CLEN_nil(), $A.HOLDS_mk($A.APPEND_nil()), $A.CLEN_nil(), $A.APPEND_nil() | reader, buffer)
  val inp = input_external(0, 0, size_in, ext)
  val (window_len | window) = $A.barr_alloc(65536)
  val snk = sink_streaming($A.CLEN_nil(), $A.CLEN_nil(), $A.APPEND_nil(), _TAILWIN_whole($A.CLEN_nil()) | writer_live(writer), window, 0, 0)
  val (done_opt | ok, inp2, snk2, byte2, bit2) = blocks_loop(BLOCKS_PREFIX_empty(), ext_refl($A.CLEN_nil()) | inp, snk, 0, 0, stored_only)
in
  if ok then let
    prval Some_v(BLOCKS_DONE_mk(done_ext, blocks, done_len)) = done_opt
    val (_ | have2) = input_have(inp2)
  in
    case+ input_drain(ext_refl(done_len) | inp2, have2) of
    | ~drained_limit(drain_ext, file_read, whole_len | ) => begin
        case+ close_sink(snk2) of
        | ~sink_closed_held(output_len, holds | written) =>
          inflated_done(INFLATES_deflated(blocks_in_ext(drain_ext, blocks)), whole_len, output_len, file_read, holds | written)
        | ~sink_closed_partial(holds | ) => inflated_stopped(failure_write, reader_ended(file_read | ), writer_held(holds | ))
        | ~sink_closed_lost(failure) => inflated_decoded_unsaved(INFLATES_deflated(blocks_in_ext(drain_ext, blocks)), file_read | failure)
      end
    | ~drained_eof(drain_ext, file_read | ) => inflated_stopped(failure_read, reader_ended(file_read | ), writer_fate_of(close_sink(snk2)))
    | ~drained_failed(failure) => inflated_stopped(failure_read, reader_lost(failure), writer_fate_of(close_sink(snk2)))
    | ~drained_overrun() => inflated_stopped(failure_read, reader_closed_early(), writer_fate_of(close_sink(snk2)))
  end
  else let prval None_v() = done_opt in stopped_result(inp2, snk2) end
end


#pub fun inflate_stored_proved {start,size_in:nat}
  (reader: $F.content_reader($A.cnil(), start, size_in), writer: $F.content_writer($A.cnil()), start: int start, size_in: int size_in): inflated(start, size_in)

#pub fun inflate_proved {start,size_in:nat}
  (reader: $F.content_reader($A.cnil(), start, size_in), writer: $F.content_writer($A.cnil()), start: int start, size_in: int size_in): inflated(start, size_in)

implement inflate_stored_proved {start,size_in} (reader, writer, start, size_in) = file_inflate(reader, writer, start, size_in, true)

implement inflate_proved {start,size_in} (reader, writer, start, size_in) = file_inflate(reader, writer, start, size_in, false)

end (* native *)

