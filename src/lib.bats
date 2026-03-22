(* zip -- ZIP central directory parser *)
(* Parses ZIP files from byte buffers. Pure computation. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   Types
   ============================================================ *)

#pub typedef zip_entry = @{
    name_offset = int,
    name_len = int,
    compression = int,
    compressed_size = int,
    uncompressed_size = int,
    local_header_offset = int
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
  (data: !$A.arr(byte, l, n), data_len: int n): $R.option(int)

#pub fun parse_eocd
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n, eocd_offset: int)
  : @(int, int)

#pub fun find_entry_by_name
  {l:agz}{n:pos}{lb:agz}{nb:pos}
  (data: !$A.arr(byte, l, n), data_len: int n,
   cd_offset: int, cd_count: int,
   name: !$A.borrow(byte, lb, nb), name_len: int nb): zip_entry

#pub fun get_data_offset
  {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n, local_offset: int): $R.option(int)

(* ============================================================
   Internal byte reading
   ============================================================ *)

fn _u8 {l:agz}{n:pos}
  (arr: !$A.arr(byte, l, n), off: int, len: int n): int =
  byte2int0($A.get<byte>(arr, $AR.checked_idx(off, len)))

fn _u16 {l:agz}{n:pos}
  (arr: !$A.arr(byte, l, n), off: int, len: int n): int = let
  val b0 = _u8(arr, off, len)
  val b1 = _u8(arr, off + 1, len)
in $AR.bor_int_int(b0, $AR.bsl_int_int(b1, 8)) end

fn _u32 {l:agz}{n:pos}
  (arr: !$A.arr(byte, l, n), off: int, len: int n): int = let
  val b0 = _u8(arr, off, len)
  val b1 = _u8(arr, off + 1, len)
  val b2 = _u8(arr, off + 2, len)
  val b3 = _u8(arr, off + 3, len)
in $AR.bor_int_int($AR.bor_int_int(b0, $AR.bsl_int_int(b1, 8)),
                   $AR.bor_int_int($AR.bsl_int_int(b2, 16), $AR.bsl_int_int(b3, 24))) end

(* ============================================================
   Internal: parse one CD entry
   ============================================================ *)

fn _parse_cd_entry {l:agz}{n:pos}
  (data: !$A.arr(byte, l, n), data_len: int n, cd_offset: int)
  : @(zip_entry, int) = let
  val empty = @{
    name_offset = 0, name_len = 0, compression = 0,
    compressed_size = 0, uncompressed_size = 0, local_header_offset = 0
  }
in
  if $AR.gt_int_int(cd_offset + 46, data_len) then @(empty, 0)
  else if $AR.neq_int_int(_u32(data, cd_offset, data_len), 33639248) then @(empty, 0)
  else let
    val compression = _u16(data, cd_offset + 10, data_len)
    val compressed_size = _u32(data, cd_offset + 20, data_len)
    val uncompressed_size = _u32(data, cd_offset + 24, data_len)
    val name_len = _u16(data, cd_offset + 28, data_len)
    val extra_len = _u16(data, cd_offset + 30, data_len)
    val comment_len = _u16(data, cd_offset + 32, data_len)
    val local_offset = _u32(data, cd_offset + 42, data_len)
    val header_size = 46 + name_len + extra_len + comment_len
    val entry = @{
      name_offset = cd_offset + 46,
      name_len = name_len,
      compression = compression,
      compressed_size = compressed_size,
      uncompressed_size = uncompressed_size,
      local_header_offset = local_offset
    }
  in @(entry, cd_offset + header_size) end
end

(* ============================================================
   Internal: compare array region with borrow
   ============================================================ *)

fun _name_eq
  {l:agz}{n:pos}{lb:agz}{nb:pos}{fuel:nat} .<fuel>.
  (data: !$A.arr(byte, l, n), d_off: int, d_len: int n,
   name: !$A.borrow(byte, lb, nb), n_off: int, n_len: int nb,
   count: int fuel): bool =
  if count <= 0 then true
  else if d_off < 0 then false
  else if n_off < 0 then false
  else if d_off >= d_len then false
  else if n_off >= n_len then false
  else let
    val db = byte2int0($A.get<byte>(data, $AR.checked_idx(d_off, d_len)))
    val nb = byte2int0($A.read<byte>(name, $AR.checked_idx(n_off, n_len)))
  in
    if db != nb then false
    else _name_eq(data, d_off + 1, d_len, name, n_off + 1, n_len, count - 1)
  end

(* ============================================================
   Implementations
   ============================================================ *)

implement find_eocd {l}{n} (data, data_len) = let
  fun loop {l:agz}{n:pos}{k:nat} .<k>.
    (data: !$A.arr(byte, l, n), i: int, len: int n, rem: int(k)): int =
    if $AR.lte_g1(rem, 0) then ~1
    else if $AR.gt_int_int(0, i) then ~1
    else if $AR.eq_int_int(_u32(data, i, len), 101010256) then i
    else loop(data, i - 1, len, $AR.sub_g1(rem, 1))
  val raw =
    if $AR.gt_int_int(22, data_len) then ~1
    else loop(data, data_len - 22, data_len, $AR.checked_nat(data_len))
in
  if $AR.gte_int_int(raw, 0) then $R.some(raw)
  else $R.none()
end

implement parse_eocd {l}{n} (data, data_len, eocd_offset) =
  if $AR.gt_int_int(eocd_offset + 22, data_len) then @(~1, 0)
  else if $AR.neq_int_int(_u32(data, eocd_offset, data_len), 101010256) then @(~1, 0)
  else @(_u32(data, eocd_offset + 16, data_len), _u16(data, eocd_offset + 10, data_len))

implement find_entry_by_name {l}{n}{lb}{nb}
  (data, data_len, cd_offset, cd_count, name, name_len) = let
  val not_found = @{
    name_offset = ~1, name_len = 0, compression = 0,
    compressed_size = 0, uncompressed_size = 0, local_header_offset = 0
  }
  fun loop {l:agz}{n:pos}{lb:agz}{nb:pos}{fuel:nat} .<fuel>.
    (data: !$A.arr(byte, l, n), data_len: int n,
     cd_off: int, remaining: int fuel,
     name: !$A.borrow(byte, lb, nb), name_len: int nb): zip_entry =
    if remaining <= 0 then
      @{name_offset= ~1, name_len= 0, compression= 0,
        compressed_size= 0, uncompressed_size= 0,
        local_header_offset= 0}
    else let
      val @(entry, next_off) = _parse_cd_entry(data, data_len, cd_off)
    in
      if entry.name_len = name_len then
        if _name_eq(data, entry.name_offset, data_len,
                    name, 0, name_len, name_len) then
          entry
        else loop(data, data_len, next_off, remaining - 1, name, name_len)
      else loop(data, data_len, next_off, remaining - 1, name, name_len)
    end
in
  if cd_count <= 0 then not_found
  else loop(data, data_len, cd_offset, $AR.checked_nat(cd_count), name, name_len)
end

implement get_data_offset {l}{n} (data, data_len, local_offset) = let
  val raw =
    if $AR.gt_int_int(local_offset + 30, data_len) then ~1
    else if $AR.neq_int_int(_u32(data, local_offset, data_len), 67324752) then ~1
    else let
      val name_len = _u16(data, local_offset + 26, data_len)
      val extra_len = _u16(data, local_offset + 28, data_len)
    in local_offset + 30 + name_len + extra_len end
in
  if $AR.gte_int_int(raw, 0) then $R.some(raw)
  else $R.none()
end
