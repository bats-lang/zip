(* zip -- ZIP central directory parser *)
(* Parses ZIP files from byte buffers. Pure computation. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   Types
   ============================================================ *)

(* An offset or value read from the archive. Indexed, so it can be
   checked against the buffer length and then used as a read position
   with no cast. *)
#pub typedef zint = [x:int] int x

#pub typedef zip_entry = @{
    name_offset = zint,
    name_len = zint,
    compression = zint,
    compressed_size = zint,
    uncompressed_size = zint,
    local_header_offset = zint
}

(* ============================================================
   Signature constants
   ============================================================ *)

val EOCD_SIG = 101010256

val CD_SIG = 33639248

val LOCAL_SIG = 67324752

(* ============================================================
   Public API
   ============================================================ *)

#pub fun find_eocd
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n): $R.option([o:nat] int o)

(* (cd_offset, cd_count); (~1, 0) when eocd_offset is not an EOCD record. *)
#pub fun parse_eocd
  {l:agz}{n:pos}{e:int}
  (data: !$A.arr(byte, l, n), data_len: int n, eocd_offset: int e)
  : @(zint, zint)

#pub fun find_entry_by_name
  {l:agz}{n:pos}{lb:agz}{nb:pos}{c:int}{d:int}
  (data: !$A.arr(byte, l, n), data_len: int n,
   cd_offset: int c, cd_count: int d,
   name: !$A.borrow(byte, lb, nb), name_len: int nb): zip_entry

#pub fun get_data_offset
  {l:agz}{n:pos}{o:int}
  (data: !$A.arr(byte, l, n), data_len: int n, local_offset: int o): $R.option([o:nat] int o)

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
   overflow: the high byte contributes b3 - 256 when its top bit is set. *)
fn _u32 {l:agz}{n:pos}{o:nat | o + 4 <= n}
  (arr: !$A.arr(byte, l, n), off: int o): zint = let
  val lo = _u8(arr, off) + 256 * _u8(arr, off + 1) + 65536 * _u8(arr, off + 2)
  val b3 = _u8(arr, off + 3)
  val hi = (if b3 < 128 then b3 else b3 - 256): [h:int | ~128 <= h; h < 128] int h
in lo + 16777216 * hi end

(* ============================================================
   Internal: parse one CD entry
   ============================================================ *)

fn _parse_cd_entry {l:agz}{n:pos}{c:int}
  (data: !$A.arr(byte, l, n), data_len: int n, cd_offset: int c)
  : @(zip_entry, zint) = let
  val empty = @{
    name_offset = 0, name_len = 0, compression = 0,
    compressed_size = 0, uncompressed_size = 0, local_header_offset = 0
  } : zip_entry
in
  if cd_offset < 0 then @(empty, 0)
  else if cd_offset + 46 > data_len then @(empty, 0)
  else if _u32(data, cd_offset) != 33639248 then @(empty, 0)
  else let
    val name_len = _u16(data, cd_offset + 28)
    val extra_len = _u16(data, cd_offset + 30)
    val comment_len = _u16(data, cd_offset + 32)
    val entry = @{
      name_offset = cd_offset + 46,
      name_len = name_len,
      compression = _u16(data, cd_offset + 10),
      compressed_size = _u32(data, cd_offset + 20),
      uncompressed_size = _u32(data, cd_offset + 24),
      local_header_offset = _u32(data, cd_offset + 42)
    } : zip_entry
  in @(entry, cd_offset + 46 + name_len + extra_len + comment_len) end
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

implement find_eocd {l}{n} (data, data_len) = let
  (* Scan backwards from the last position an EOCD record fits. *)
  fun loop {i:int | i >= ~1; i + 22 <= n} .<i + 1>.
    (data: !$A.arr(byte, l, n), i: int i): [r:int | r >= ~1] int r =
    if i < 0 then ~1
    else if _u32(data, i) = 101010256 then i
    else loop(data, i - 1)
  val raw = (if data_len < 22 then ~1 else loop(data, data_len - 22)): [r:int | r >= ~1] int r
in
  if raw >= 0 then $R.some(raw)
  else $R.none()
end

implement parse_eocd {l}{n}{e} (data, data_len, eocd_offset) =
  if eocd_offset < 0 then @(~1, 0)
  else if eocd_offset + 22 > data_len then @(~1, 0)
  else if _u32(data, eocd_offset) != 101010256 then @(~1, 0)
  else @(_u32(data, eocd_offset + 16), _u16(data, eocd_offset + 10))

implement find_entry_by_name {l}{n}{lb}{nb}{c}{d}
  (data, data_len, cd_offset, cd_count, name, name_len) = let
  fun loop {r:nat} .<r>.
    (data: !$A.arr(byte, l, n), cd_off: zint, remaining: int r,
     name: !$A.borrow(byte, lb, nb)): zip_entry =
    if remaining <= 0 then
      @{name_offset= ~1, name_len= 0, compression= 0,
        compressed_size= 0, uncompressed_size= 0,
        local_header_offset= 0}
    else let
      val @(entry, next_off) = _parse_cd_entry(data, data_len, cd_off)
      val off = entry.name_offset
      val matched =
        (if entry.name_len != name_len then false
         else if off < 0 then false
         else if off + name_len > data_len then false
         else _name_eq(data, off, name, name_len)): bool
    in
      if matched then entry
      else loop(data, next_off, remaining - 1, name)
    end
in
  if cd_count <= 0 then loop(data, cd_offset, 0, name)
  else loop(data, cd_offset, cd_count, name)
end

implement get_data_offset {l}{n}{o} (data, data_len, local_offset) = let
  val raw =
    (if local_offset < 0 then ~1
     else if local_offset + 30 > data_len then ~1
     else if _u32(data, local_offset) != 67324752 then ~1
     else local_offset + 30 + _u16(data, local_offset + 26) + _u16(data, local_offset + 28)
    ): [r:int | r >= ~1] int r
in
  if raw >= 0 then $R.some(raw)
  else $R.none()
end
