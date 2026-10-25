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

(* ============================================================
   RFC 1951 as relations (quire#608, zip#64): the declarations
   ============================================================ *)

(* cells and cells are the same cells: the one constructor is the only way
   to have it, so a lemma's conclusion that two outputs are the same is
   this *)
#pub dataprop CELLS_EQ($A.cells, $A.cells) =
  | {cells:$A.cells} CELLS_EQ_refl(cells, cells)

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

(* Cells built from cells *)

(* APPEND(first, second, both): both is first and then second *)
#pub dataprop APPEND($A.cells, $A.cells, $A.cells) =
  | {second:$A.cells} APPEND_nil($A.cnil(), second, second)
  | {head:int}{first,second,both:$A.cells} APPEND_cons($A.ccons(head, first), second, $A.ccons(head, both)) of APPEND(first, second, both)

(* SLICE(source, start, width, part): the width cells from cell start are part *)
#pub dataprop SLICE($A.cells, int, int, $A.cells) =
  | {source:$A.cells}{start:nat} SLICE_nil(source, start, 0, $A.cnil())
  | {source:$A.cells}{start,width:nat}{head:int}{rest:$A.cells}
    SLICE_cons(source, start, width + 1, $A.ccons(head, rest)) of ($A.NTH(source, start, head), SLICE(source, start + 1, width, rest))

(* RUN(count, value, rest, all): all is count cells value and then rest *)
#pub dataprop RUN(int, int, $A.cells, $A.cells) =
  | {value:int}{rest:$A.cells} RUN_zero(0, value, rest, rest)
  | {count:nat}{value:int}{rest,all:$A.cells} RUN_cons(count + 1, value, rest, $A.ccons(value, all)) of RUN(count, value, rest, all)

#pub prfun append_functional {first,second,both,other:$A.cells} (APPEND(first, second, both), APPEND(first, second, other)): CELLS_EQ(both, other)
#pub prfun slice_functional {source:$A.cells}{start,width:nat}{first,second:$A.cells} (SLICE(source, start, width, first), SLICE(source, start, width, second)): CELLS_EQ(first, second)

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

(* LENGTH_SYMBOL(sym, extra_bits, base): length symbol sym (257 to 285) has
   extra_bits extra bits and its match lengths start at base (the table of
   3.2.5): symbols 257 to 264 have none; then four symbols for each extra
   bit count 1 to 5, whose bases are 4, 5, 6 and 7 times 2 to the extra
   bit count, plus 3; symbol 285 is the length 258 alone *)
#pub dataprop LENGTH_SYMBOL(int, int, int) =
  | {sym:int | 257 <= sym; sym <= 264} LENGTH_SYMBOL_short(sym, 0, sym - 254)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_group_0(261 + 4 * extra_bits, extra_bits, 4 * power + 3) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_group_1(262 + 4 * extra_bits, extra_bits, 5 * power + 3) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_group_2(263 + 4 * extra_bits, extra_bits, 6 * power + 3) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 5} LENGTH_SYMBOL_group_3(264 + 4 * extra_bits, extra_bits, 7 * power + 3) of $AR.POW2(extra_bits, power)
  | LENGTH_SYMBOL_last(285, 0, 258)

(* DISTANCE_SYMBOL(sym, extra_bits, base): distance symbol sym (0 to 29),
   the table of 3.2.5: symbols 0 to 3 have no extra bits; then two symbols
   for each extra bit count 1 to 13, whose bases are 2 and 3 times 2 to the
   extra bit count, plus 1 *)
#pub dataprop DISTANCE_SYMBOL(int, int, int) =
  | {sym:nat | sym < 4} DISTANCE_SYMBOL_short(sym, 0, sym + 1)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 13} DISTANCE_SYMBOL_group_0(2 * extra_bits + 2, extra_bits, 2 * power + 1) of $AR.POW2(extra_bits, power)
  | {extra_bits,power:nat | 1 <= extra_bits; extra_bits <= 13} DISTANCE_SYMBOL_group_1(2 * extra_bits + 3, extra_bits, 3 * power + 1) of $AR.POW2(extra_bits, power)

(* FIXED_LITLEN(lengths) and FIXED_DIST(lengths): the code lengths of the
   fixed Huffman codes (3.2.6): 144 of 8 bits, 112 of 9, 24 of 7 and 8 of 8;
   and 32 distance codes of 5 bits *)
#pub dataprop FIXED_LITLEN($A.cells) =
  | {lengths,after_144,after_112,after_24:$A.cells}
    FIXED_LITLEN_mk(lengths) of (RUN(144, 8, after_144, lengths), RUN(112, 9, after_112, after_144), RUN(24, 7, after_24, after_112), RUN(8, 8, $A.cnil(), after_24))
#pub dataprop FIXED_DIST($A.cells) =
  | {lengths:$A.cells} FIXED_DIST_mk(lengths) of RUN(32, 5, $A.cnil(), lengths)

(* COPY(before, distance, length, after): length bytes are each copied
   from distance back in the output so far, one after the other, so a
   copy with distance < length reads bytes it has just written *)
#pub dataprop COPY($A.cells, int, int, $A.cells) =
  | {output:$A.cells}{distance:int} COPY_done(output, distance, 0, output)
  | {output,next,after:$A.cells}{output_count,distance,length,copied:nat | 1 <= distance; distance <= output_count}
    COPY_step(output, distance, length + 1, after) of ($A.CLEN(output, output_count), $A.NTH(output, output_count - distance, copied), APPEND(output, $A.ccons(copied, $A.cnil()), next), COPY(next, distance, length, after))

#pub prfun copy_functional {output:$A.cells}{distance,length:nat}{first,second:$A.cells} (COPY(output, distance, length, first), COPY(output, distance, length, second)): CELLS_EQ(first, second)

(* SYMS(litlen, dist, source, p, before, after, end_bit): the symbols from
   bit p, decoded by the literal/length code litlen and the distance code
   dist, up to the end-of-block symbol, take the output before to after,
   and the end-of-block symbol ends at bit end_bit. A literal appends
   itself; a length symbol, its extra bits, a distance symbol and its extra
   bits are a copy. *)
#pub dataprop SYMS($A.cells, $A.cells, $A.cells, int, $A.cells, $A.cells, int) =
  | {litlen,dist,source:$A.cells}{p,sym,used:nat}{output:$A.cells}
    SYMS_end(litlen, dist, source, p, output, output, p + used) of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_end_of_block(), sym))
  | {litlen,dist,source:$A.cells}{p,sym,used,end_bit:nat}{output,next,after:$A.cells}
    SYMS_literal(litlen, dist, source, p, output, after, end_bit)
    of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_literal(), sym),
        APPEND(output, $A.ccons(sym, $A.cnil()), next), SYMS(litlen, dist, source, p + used, next, after, end_bit))
  | {litlen,dist,source:$A.cells}{p,sym,used,length_extra_bits,length_base,length_extra_value,dist_sym,dist_used,dist_extra_bits,dist_base,dist_extra_value,end_bit:nat}{output,next,after:$A.cells}
    SYMS_copy(litlen, dist, source, p, output, after, end_bit)
    of (DECSYM(litlen, source, p, sym, used), SYMBOL_CLASS(symbol_length(), sym),
        LENGTH_SYMBOL(sym, length_extra_bits, length_base), BITS(source, p + used, length_extra_bits, length_extra_value),
        DECSYM(dist, source, p + used + length_extra_bits, dist_sym, dist_used), DISTANCE_SYMBOL(dist_sym, dist_extra_bits, dist_base),
        BITS(source, p + used + length_extra_bits + dist_used, dist_extra_bits, dist_extra_value),
        COPY(output, dist_base + dist_extra_value, length_base + length_extra_value, next),
        SYMS(litlen, dist, source, p + used + length_extra_bits + dist_used + dist_extra_bits, next, after, end_bit))

#pub prfun syms_functional {litlen,dist,source:$A.cells}{p:nat}{output,first,second:$A.cells}{first_end,second_end:nat}
  (LENGTHS_FIT(litlen, 15), LENGTHS_FIT(dist, 15), SYMS(litlen, dist, source, p, output, first, first_end), SYMS(litlen, dist, source, p, output, second, second_end)): [first_end == second_end] CELLS_EQ(first, second)

(* The dynamic block's header, RFC 1951 3.2.7 *)

(* CL_ORDER(order): the order in which the code length code's lengths are
   stored: 16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15 *)
#pub dataprop CL_ORDER($A.cells) =
  | CL_ORDER_mk($A.ccons(16, $A.ccons(17, $A.ccons(18, $A.ccons(0, $A.ccons(8, $A.ccons(7, $A.ccons(9, $A.ccons(6, $A.ccons(10, $A.ccons(5, $A.ccons(11, $A.ccons(4, $A.ccons(12, $A.ccons(3, $A.ccons(13, $A.ccons(2, $A.ccons(14, $A.ccons(1, $A.ccons(15, $A.cnil())))))))))))))))))))))

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

(* CODE_LENGTHS(code_length_code, source, p, so_far, total, lengths, end_bit):
   the code lengths so far, decoded by the code length code from bit p, go
   on until there are total of them, lengths, ending at bit end_bit; a
   repeat or run never goes past total, and the repeat of the previous
   length needs one *)
#pub dataprop CODE_LENGTHS($A.cells, $A.cells, int, $A.cells, int, $A.cells, int) =
  | {code_length_code,source:$A.cells}{p,total:nat}{so_far:$A.cells} CODE_LENGTHS_done(code_length_code, source, p, so_far, total, so_far, p) of $A.CLEN(so_far, total)
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,end_bit:nat | so_far_count < total}{so_far,next,lengths:$A.cells}
    CODE_LENGTHS_literal(code_length_code, source, p, so_far, total, lengths, end_bit)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_literal(), sym),
        APPEND(so_far, $A.ccons(sym, $A.cnil()), next), CODE_LENGTHS(code_length_code, source, p + used, next, total, lengths, end_bit))
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit,previous:nat | 1 <= so_far_count; so_far_count + 3 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
    CODE_LENGTHS_repeat_previous(code_length_code, source, p, so_far, total, lengths, end_bit)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_repeat_previous(), sym),
        BITS(source, p + used, 2, extra_value), $A.NTH(so_far, so_far_count - 1, previous),
        RUN(3 + extra_value, previous, $A.cnil(), run), APPEND(so_far, run, next), CODE_LENGTHS(code_length_code, source, p + used + 2, next, total, lengths, end_bit))
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit:nat | so_far_count + 3 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
    CODE_LENGTHS_zeros_short(code_length_code, source, p, so_far, total, lengths, end_bit)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_zeros_short(), sym),
        BITS(source, p + used, 3, extra_value),
        RUN(3 + extra_value, 0, $A.cnil(), run), APPEND(so_far, run, next), CODE_LENGTHS(code_length_code, source, p + used + 3, next, total, lengths, end_bit))
  | {code_length_code,source:$A.cells}{p,total,so_far_count,sym,used,extra_value,end_bit:nat | so_far_count + 11 + extra_value <= total}{so_far,run,next,lengths:$A.cells}
    CODE_LENGTHS_zeros_long(code_length_code, source, p, so_far, total, lengths, end_bit)
    of ($A.CLEN(so_far, so_far_count), DECSYM(code_length_code, source, p, sym, used), LENGTH_CLASS(length_zeros_long(), sym),
        BITS(source, p + used, 7, extra_value),
        RUN(11 + extra_value, 0, $A.cnil(), run), APPEND(so_far, run, next), CODE_LENGTHS(code_length_code, source, p + used + 7, next, total, lengths, end_bit))

#pub prfun code_lengths_functional {code_length_code,source:$A.cells}{p,total:nat}{so_far,first,second:$A.cells}{first_end,second_end:nat}
  (LENGTHS_FIT(code_length_code, 7), CODE_LENGTHS(code_length_code, source, p, so_far, total, first, first_end), CODE_LENGTHS(code_length_code, source, p, so_far, total, second, second_end)): [first_end == second_end] CELLS_EQ(first, second)

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

(* BLOCK(kind, source, p, before, after, end_bit): a block of the kind
   whose body starts at bit p (after its 3 header bits) takes the output
   before to after, and ends at bit end_bit *)
#pub dataprop BLOCK(block_kind, $A.cells, int, $A.cells, $A.cells, int) =
  (* skips to the byte boundary, LEN, NLEN = the complement of LEN, then LEN bytes *)
  | {source:$A.cells}{p,data_byte,len,nlen:nat | 8 * data_byte >= p; 8 * data_byte < p + 8; len + nlen == 65535}{before,data,after:$A.cells}
    BLOCK_stored(block_stored(), source, p, before, after, 8 * (data_byte + 4 + len))
    of (BITS(source, 8 * data_byte, 16, len), BITS(source, 8 * data_byte + 16, 16, nlen), SLICE(source, data_byte + 4, len, data), APPEND(before, data, after))
  | {source,litlen,dist:$A.cells}{p,end_bit:nat}{before,after:$A.cells}
    BLOCK_fixed(block_fixed(), source, p, before, after, end_bit)
    of (FIXED_LITLEN(litlen), FIXED_DIST(dist), LENGTHS_FIT(litlen, 15), LENGTHS_FIT(dist, 15), SYMS(litlen, dist, source, p, before, after, end_bit))
  | {source,values,order,code_length_code,all_lengths,litlen,dist:$A.cells}{p,hlit,hdist,hclen,data_start,end_bit:nat | hlit <= 29; hdist <= 29}{before,after:$A.cells}
    BLOCK_dynamic(block_dynamic(), source, p, before, after, end_bit)
    of (BITS(source, p, 5, hlit), BITS(source, p + 5, 5, hdist), BITS(source, p + 10, 4, hclen),
        READ_LENGTHS3(source, p + 14, hclen + 4, values), CL_ORDER(order), CODE_LENGTHS_FROM(order, hclen + 4, values, 0, code_length_code),
        LENGTHS_FIT(code_length_code, 7), LENGTHS_FULL(code_length_code, 7),
        CODE_LENGTHS(code_length_code, source, p + 14 + 3 * (hclen + 4), $A.cnil(), hlit + 257 + hdist + 1, all_lengths, data_start),
        $A.CLEN(litlen, hlit + 257), APPEND(litlen, dist, all_lengths), LITLEN_USABLE(litlen), DIST_USABLE(dist),
        SYMS(litlen, dist, source, data_start, before, after, end_bit))

#pub prfun block_functional {kind:block_kind}{source:$A.cells}{p:nat}{before,first,second:$A.cells}{first_end,second_end:nat}
  (BLOCK(kind, source, p, before, first, first_end), BLOCK(kind, source, p, before, second, second_end)): [first_end == second_end] CELLS_EQ(first, second)

(* BLOCKS(source, p, before, after): the blocks from bit p, ending at the
   one with BFINAL 1, take the output before to after *)
#pub dataprop BLOCKS($A.cells, int, $A.cells, $A.cells) =
  | {source:$A.cells}{p,btype,end_bit:nat}{kind:block_kind}{before,after:$A.cells}
    BLOCKS_last(source, p, before, after) of (BITS(source, p, 1, 1), BITS(source, p + 1, 2, btype), BTYPE(kind, btype), BLOCK(kind, source, p + 3, before, after, end_bit))
  | {source:$A.cells}{p,btype,end_bit:nat}{kind:block_kind}{before,middle,after:$A.cells}
    BLOCKS_next(source, p, before, after) of (BITS(source, p, 1, 0), BITS(source, p + 1, 2, btype), BTYPE(kind, btype), BLOCK(kind, source, p + 3, before, middle, end_bit), BLOCKS(source, end_bit, middle, after))

#pub prfun blocks_functional {source:$A.cells}{p:nat}{before,first,second:$A.cells}
  (BLOCKS(source, p, before, first), BLOCKS(source, p, before, second)): CELLS_EQ(first, second)

(* ============================================================
   What inflating an entry's data gives, as a relation (quire#608, INFLATES)
   ============================================================ *)

(* How an entry's data is stored, as a static index: the method field 0
   (stored) or 8 (deflated), as `compression` is its dynamic form *)
#pub datasort inflate_kind =
  | inflate_stored of ()
  | inflate_deflated of ()

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

(* The decoders that return the proof (zip#64): a function over array's
   barr that gives the output cells with INFLATES, or none for a stream it
   cannot take. inflate_stored_proved takes the streams of stored blocks.
   The sizes are any natural numbers: an empty output (a deflate stream of an empty file), and sizes up
   to the 2 to the 31 minus 1 the archive check allows; what a barr can hold
   is array's bound, which the implementation meets by refusing (none). *)
#pub fun inflate_stored_proved {l:agz}{n:nat}{compressed:$A.cells}{size:nat}
  (source: !$A.barr(l, n, compressed), n: int n, size: int size)
  : $R.option([lo:agz][output:$A.cells] (INFLATES(inflate_deflated(), compressed, output) | $A.barr(lo, size, output)))

#pub fun inflate_proved {l:agz}{n:nat}{compressed:$A.cells}{size:nat}
  (source: !$A.barr(l, n, compressed), n: int n, size: int size)
  : $R.option([lo:agz][output:$A.cells] (INFLATES(inflate_deflated(), compressed, output) | $A.barr(lo, size, output)))
