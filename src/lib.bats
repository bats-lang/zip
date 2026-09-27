(* zip -- ZIP central directory parser *)
(* Parses ZIP files from byte buffers. Pure computation. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   Types
   ============================================================ *)

(* The central directory of an n-byte archive: its offset, proven inside
   the archive, and its entry count. *)
#pub datatype zip_dir(n:int) =
  | {c:nat | c <= n}{d:nat | d < 65536} zip_dir_mk(n) of (int c, int d)

(* An entry of an n-byte archive: its name [name_off, name_off + name_len)
   and its compressed data [data_off, data_off + csize), both proven
   inside the archive; its compression method (0 stored, 8 deflate, the
   ones an EPUB uses); its uncompressed size. *)
#pub datatype zip_entry(n:int) =
  | {no,nl:nat | no + nl <= n}{d,s:nat | d + s <= n}{m:int | m == 0 || m == 8}{u:nat}
    zip_entry_mk(n) of (int no, int nl, int d, int s, int m, int u)

(* Ranged reading: an archive of z bytes need not be in memory at once.
   find_cd reads its end (the last t bytes), find_ref its central
   directory, find_data an entry's local header; each result names the
   next range to read, proven inside the archive. *)

(* The central directory of a z-byte archive: [c, c + s), inside it,
   holding d entries *)
#pub datatype zip_cd(z:int, s:int) =
  | {c:nat | c + s <= z}{d:nat | d < 65536} zip_cd_mk(z, s) of (int c, int s, int d)

(* An entry of a z-byte archive, from its central directory: its local
   header at h, its compressed size s, method m (0 stored, 8 deflate),
   uncompressed size u, and its name [no, no + nl) in the archive (in the
   central directory) *)
#pub datatype zip_ref(z:int) =
  | {h:nat | h + 30 <= z}{s:nat}{m:int | m == 0 || m == 8}{u:nat}{no,nl:nat | no + nl <= z}
    zip_ref_mk(z) of (int h, int s, int m, int u, int no, int nl)

(* An entry's compressed data [d, d + s) inside a z-byte archive, its
   method and its uncompressed size *)
#pub datatype zip_span(z:int) =
  | {d,s:nat | d + s <= z}{m:int | m == 0 || m == 8}{u:nat}
    zip_span_mk(z) of (int d, int s, int m, int u)

(* The most bytes at an archive's end that its end-of-central-directory
   record (22 bytes and a comment of at most 65535) spans *)
#pub stadef ZIP_TAIL_MAX = 65557

(* ============================================================
   Public API
   ============================================================ *)

(* The central directory of a z-byte archive whose last t bytes are tail
   (read from offset z - t; t = min(z, ZIP_TAIL_MAX) finds any record),
   or none when tail holds no end-of-central-directory record or the
   directory it names is empty or outside the archive *)
#pub fun find_cd
  {l:agz}{t:pos}{z:int | t <= z}
  (tail: !$A.arr(byte, l, t), t: int t, z: int z): $R.option([s:pos] zip_cd(z, s))

(* The directory's size *)
#pub fun cd_size {z,s:int} (dir: zip_cd(z, s)): int s

(* The directory's offset *)
#pub fun cd_offset {z,s:int} (dir: zip_cd(z, s)): [c:nat | c + s <= z] int c

(* The entry named name in the central directory cd (read from the
   directory's offset), or none when there is none or its local header
   is outside the archive or its method is neither 0 nor 8 *)
#pub fun find_ref
  {l:agz}{z:int}{s:pos}{lb:agz}{nb:pos}
  (cd: !$A.arr(byte, l, s), dir: zip_cd(z, s), z: int z,
   name: !$A.borrow(byte, lb, nb), name_len: int nb): $R.option(zip_ref(z))

(* The entry's compressed data, given hdr, its 30-byte local header (read
   from the ref's h), or none when hdr is not a local header or the data
   is outside the archive *)
#pub fun find_data
  {l:agz}{z:int}
  (hdr: !$A.arr(byte, l, 30), r: zip_ref(z), z: int z): $R.option(zip_span(z))

(* The central directory named by the archive's end-of-central-directory
   record, or none when there is no such record or its directory offset
   is outside the archive. *)
#pub fun find_dir
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n): $R.option(zip_dir(n))

(* The entry named name, or none when there is none (or the directory
   ends before it, or the entry's local header or data is not inside
   the archive, or it uses a compression method other than 0 or 8). *)
#pub fun find_entry
  {l:agz}{n:pos}{lb:agz}{nb:pos}
  (data: !$A.arr(byte, l, n), data_len: int n, dir: zip_dir(n),
   name: !$A.borrow(byte, lb, nb), name_len: int nb): $R.option(zip_entry(n))

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

implement find_dir {l}{n} (data, data_len) = let
  (* Scan backwards from the last position an EOCD record fits. *)
  fun loop {i:int | i >= ~1; i + 22 <= n} .<i + 1>.
    (data: !$A.arr(byte, l, n), i: int i): $R.option(zip_dir(n)) =
    if i < 0 then $R.none()
    else if _u32(data, i) = 101010256 then let
      val c = _u32(data, i + 16)
    in
      if c < 0 then $R.none()
      else if c > data_len then $R.none()
      else $R.some(zip_dir_mk(c, _u16(data, i + 10)))
    end
    else loop(data, i - 1)
in
  if data_len < 22 then $R.none() else loop(data, data_len - 22)
end

(* The entry whose central directory record is at c and whose name
 (nl bytes) follows it, if its local header and data are inside the
 archive and its method is 0 or 8 *)
fn _found {l:agz}{n:pos}{c:nat | c + 46 <= n}{nl:nat | c + 46 + nl <= n}
  (data: !$A.arr(byte, l, n), data_len: int n, c: int c, nl: int nl): $R.option(zip_entry(n)) = let
  val lh = _u32(data, c + 42)
  val s = _u32(data, c + 20)
  val m = _u16(data, c + 10)
  val u = _u32(data, c + 24)
in
  if lh < 0 then $R.none()
  else if s < 0 then $R.none()
  else if u < 0 then $R.none()
  else if lh + 30 > data_len then $R.none()
  else if _u32(data, lh) <> 67324752 then $R.none()
  else let
    val d = lh + 30 + _u16(data, lh + 26) + _u16(data, lh + 28)
  in
    if d + s > data_len then $R.none()
    else if m = 0 then $R.some(zip_entry_mk(c + 46, nl, d, s, 0, u))
    else if m = 8 then $R.some(zip_entry_mk(c + 46, nl, d, s, 8, u))
    else $R.none()
  end
end

implement find_entry {l}{n}{lb}{nb} (data, data_len, dir, name, name_len) = let
  (* Entry at c, with r entries left in the directory *)
  fun loop {c:nat | c <= n}{r:nat} .<r>.
    (data: !$A.arr(byte, l, n), c: int c, r: int r,
     name: !$A.borrow(byte, lb, nb)): $R.option(zip_entry(n)) =
    if r <= 0 then $R.none()
    else if c + 46 > data_len then $R.none()
    else if _u32(data, c) <> 33639248 then $R.none()
    else let
      val nl = _u16(data, c + 28)
      val next = c + 46 + nl + _u16(data, c + 30) + _u16(data, c + 32)
    in
      if c + 46 + nl > data_len then $R.none()
      else if nl = name_len && _name_eq(data, c + 46, name, name_len) then
        _found(data, data_len, c, nl)
      else if next > data_len then $R.none()
      else loop(data, next, r - 1, name)
    end
  val+ zip_dir_mk(c, d) = dir
in loop(data, c, d, name) end

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
      if c < 0 then $R.none()
      else if s <= 0 then $R.none()
      else if c > z - s then $R.none()
      else $R.some(zip_cd_mk(c, s, d))
    end
    else loop(tail, i - 1)
in
  if t < 22 then $R.none() else loop(tail, t - 22)
end

implement cd_size {z,s} (dir) = let
  val+ zip_cd_mk(_, n, _) = dir
in n end

implement cd_offset {z,s} (dir) = let
  val+ zip_cd_mk(c, _, _) = dir
in c end

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
      else if nl = name_len && _name_eq(cd, c + 46, name, name_len) then let
        val h = _u32(cd, c + 42)
        val cs = _u32(cd, c + 20)
        val m = _u16(cd, c + 10)
        val u = _u32(cd, c + 24)
      in
        if h < 0 then $R.none()
        else if cs < 0 then $R.none()
        else if u < 0 then $R.none()
        else if h > z - 30 then $R.none()
        else if m = 0 then $R.some(zip_ref_mk(h, cs, 0, u, co + c + 46, nl))
        else if m = 8 then $R.some(zip_ref_mk(h, cs, 8, u, co + c + 46, nl))
        else $R.none()
      end
      else if next > s then $R.none()
      else loop(cd, s, co, next, r - 1, name)
    end
  val+ zip_cd_mk(co, s, d) = dir
in loop(cd, s, co, 0, d, name) end

implement find_data {l}{z} (hdr, r, z) = let
  val+ zip_ref_mk(h, cs, m, u, _, _) = r
in
  if _u32(hdr, 0) <> 67324752 then $R.none()
  else let
    val d = h + 30 + _u16(hdr, 26) + _u16(hdr, 28)
  in
    if d > z - cs then $R.none()
    else $R.some(zip_span_mk(d, cs, m, u))
  end
end
