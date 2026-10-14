#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use result as R
#use zip as Z

(* A 375-byte archive in ZIP64 form, written as Python's zipfile and Info-ZIP
   write one whose end record is saturated: two stored entries, a.txt
   ("hello", header at 0) and dir/b.xml ("<b/>", header at 60), each with
   its sizes 0xFFFFFFFF in the central directory and the real ones in a
   ZIP64 extra field (dir/b.xml's local header offset too, third in its
   extra), the directory at 123 (154 bytes, 2 entries), the ZIP64 end
   record at 277 (56 bytes), its locator at 333 (20) and the end record
   at 353 (22) with its entry count 0xFFFF and its size and offset
   0xFFFFFFFF. *)
fn _hex_value (c: char): int =
  if c >= '0' then (if c <= '9' then char2int0(c) - char2int0('0') else char2int0(c) - char2int0('a') + 10)
  else 0

fn _archive (): [l:agz] $A.arr(byte, l, 375) = let
  val hex = "504b03042d00000000000000000086a61036ffffffffffffffff05001400612e747874010010000500000000000000050000000000000068656c6c6f504b03042d00000000000000000078563412ffffffffffffffff090014006469722f622e786d6c01001000040000000000000004000000000000003c622f3e504b01022d002d00000000000000000086a61036ffffffffffffffff050014000000000000000000000000000000612e7478740100100005000000000000000500000000000000504b01022d002d00000000000000000078563412ffffffffffffffff09001c0000000000000000000000ffffffff6469722f622e786d6c01001800040000000000000004000000000000003c00000000000000504b06062c000000000000002d002d000000000000000000020000000000000002000000000000009a000000000000007b00000000000000504b060700000000150100000000000001000000504b050600000000ffffffffffffffffffffffff0000"
  val a = $A.alloc<byte>(375)
  fun fill {l:agz}{i:nat | i <= 375} .<375 - i>. (a: !$A.arr(byte, l, 375), i: int i): void =
    if i >= 375 then ()
    else let
      val high = _hex_value(string_get_at(hex, 2 * i))
      val low = _hex_value(string_get_at(hex, 2 * i + 1))
      val () = $A.set<byte>(a, i, $A.int2byte($AR.low_byte(16 * high + low)))
    in fill(a, i + 1) end
  val () = fill(a, 0)
in a end

(* The last t bytes of the archive *)
fn _tail {l:agz}{t:pos | t <= 375} (a: !$A.arr(byte, l, 375), t: int t): [l2:agz] $A.arr(byte, l2, t) = let
  val tail = $A.alloc<byte>(t)
  fun copy {l:agz}{l2:agz}{i:nat | i <= t} .<t - i>.
    (a: !$A.arr(byte, l, 375), tail: !$A.arr(byte, l2, t), i: int i): void =
    if i >= t then ()
    else let
      val () = $A.set<byte>(tail, i, $A.get<byte>(a, 375 - t + i))
    in copy(a, tail, i + 1) end
  val () = copy(a, tail, 0)
in tail end

fn _slice {l:agz}{o:nat}{k:pos | o + k <= 375} (a: !$A.arr(byte, l, 375), o: int o, k: int k): [l2:agz] $A.arr(byte, l2, k) = let
  val part = $A.alloc<byte>(k)
  fun copy {l:agz}{l2:agz}{i:nat | i <= k} .<k - i>.
    (a: !$A.arr(byte, l, 375), part: !$A.arr(byte, l2, k), i: int i): void =
    if i >= k then ()
    else let
      val () = $A.set<byte>(part, i, $A.get<byte>(a, o + i))
    in copy(a, part, i + 1) end
  val () = copy(a, part, 0)
in part end

(* Sets the byte at o *)
fn _put {l:agz}{o:nat | o < 375} (a: !$A.arr(byte, l, 375), o: int o, v: int): void =
  $A.set<byte>(a, o, $A.int2byte($AR.low_byte(v)))

fn _is_stored (found: $Z.compression): bool =
  case+ found of
  | $Z.Stored() => true
  | $Z.Deflated() => false

(* The directory found in the archive's last t bytes: its offset, size and
   entry count, or -1 three times when there is none *)
fn _directory {l:agz}{t:pos | t <= 375} (a: !$A.arr(byte, l, 375), t: int t): @(int, int, int) = let
  val tail = _tail(a, t)
  val found = $Z.find_cd(tail, t, 375)
  val () = $A.free<byte>(tail)
in
  case+ found of
  | ~$R.some(~$Z.zip_cd_mk(c, s, d)) => @(c, s, d)
  | ~$R.none() => @(~1, ~1, ~1)
end

(* The entries cd_refs lists from the archive's directory: how many, and
   whether each is what is expected *)
fn _entries {l:agz} (a: !$A.arr(byte, l, 375)): @(int, bool) = let
  val tail = _tail(a, 375)
  val found = $Z.find_cd(tail, 375, 375)
  val () = $A.free<byte>(tail)
in
  case+ found of
  | ~$R.none() => @(~1, false)
  | ~$R.some(dir) => let
      val cd = _slice(a, $Z.cd_offset(dir), $Z.cd_size(dir))
      val result = (case+ $Z.cd_refs(cd, dir, 375) of
        | ~$R.none() => @(~1, false)
        | ~$R.some(rs) => (case+ rs of
          | ~$Z.zip_refs_nil() => @(0, true)
          | ~$Z.zip_refs_cons(h1, cs1, m1, u1, no1, nl1, rest) => let
              val first = h1 = 0 && cs1 = 5 && _is_stored(m1) && u1 = 5 && no1 = 46 && nl1 = 5
            in
              case+ rest of
              | ~$Z.zip_refs_nil() => @(1, first)
              | ~$Z.zip_refs_cons(h2, cs2, m2, u2, no2, nl2, rest2) => let
                  val second = h2 = 60 && cs2 = 4 && _is_stored(m2) && u2 = 4 && no2 = 117 && nl2 = 9
                  val () = $Z.zip_refs_free(rest2)
                in @(2, first && second) end
            end)): @(int, bool)
      val () = $A.free<byte>(cd)
      val+ ~$Z.zip_cd_mk(_, _, _) = dir
    in result end
end

(* find_ref for dir/b.xml and the data its local header names *)
fn _second_by_name {l:agz} (a: !$A.arr(byte, l, 375)): bool = let
  val tail = _tail(a, 375)
  val found = $Z.find_cd(tail, 375, 375)
  val () = $A.free<byte>(tail)
in
  case+ found of
  | ~$R.none() => false
  | ~$R.some(dir) => let
      val cd = _slice(a, $Z.cd_offset(dir), $Z.cd_size(dir))
      val name = $A.alloc<byte>(9)
      val () = $A.set<byte>(name, 0, $A.int2byte(100))
      val () = $A.set<byte>(name, 1, $A.int2byte(105))
      val () = $A.set<byte>(name, 2, $A.int2byte(114))
      val () = $A.set<byte>(name, 3, $A.int2byte(47))
      val () = $A.set<byte>(name, 4, $A.int2byte(98))
      val () = $A.set<byte>(name, 5, $A.int2byte(46))
      val () = $A.set<byte>(name, 6, $A.int2byte(120))
      val () = $A.set<byte>(name, 7, $A.int2byte(109))
      val () = $A.set<byte>(name, 8, $A.int2byte(108))
      val @(frozen, borrowed) = $A.freeze<byte>(name)
      val ok = (case+ $Z.find_ref(cd, dir, 375, borrowed, 9) of
        | ~$R.none() => false
        | ~$R.some(r) => let
            val header = _slice(a, $Z.ref_header(r), 30)
            val span = $Z.find_data(header, r, 375)
            val () = $A.free<byte>(header)
            val+ ~$Z.zip_ref_mk(h, cs, m, u, no, nl) = r
            val here = h = 60 && cs = 4 && _is_stored(m) && u = 4 && no = 240 && nl = 9
          in
            case+ span of
            | ~$R.some(~$Z.zip_span_mk(d, s, _, _)) => here && d = 119 && s = 4
            | ~$R.none() => false
          end): bool
      val () = $A.drop<byte>(frozen, borrowed)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
      val () = $A.free<byte>(cd)
      val+ ~$Z.zip_cd_mk(_, _, _) = dir
    in ok end
end

fn _report (label: string, ok: bool): bool = let
  val () = (if ok then () else println! ("FAIL ", label))
in ok end

implement main0 () = let
  val a = _archive()
  (* the whole archive, and the last 98 bytes alone: the ZIP64 record, its
     locator and the end record *)
  val @(c1, s1, d1) = _directory(a, 375)
  val t1 = _report("zip64 directory", c1 = 123 && s1 = 154 && d1 = 2)
  val @(c2, s2, d2) = _directory(a, 98)
  val t2 = _report("zip64 directory from the last 98 bytes", c2 = 123 && s2 = 154 && d2 = 2)
  (* the last 97 bytes lack the first byte of the ZIP64 record: not found *)
  val @(c3, _, _) = _directory(a, 97)
  val t3 = _report("zip64 record outside the tail", c3 = ~1)
  val @(count, entries_ok) = _entries(a)
  val t4 = _report("zip64 entries", count = 2 && entries_ok)
  val t5 = _report("zip64 entry by name", _second_by_name(a))
  (* the ZIP64 record's directory offset with a high half: not a directory
     this reader takes *)
  val () = _put(a, 329, 1)
  val @(c6, _, _) = _directory(a, 375)
  val t6 = _report("zip64 offset of 2^32 or more", c6 = ~1)
  val () = _put(a, 329, 0)
  (* a.txt's uncompressed size in its extra field with a high half: the
     entry is left out, dir/b.xml is not *)
  val () = _put(a, 182, 1)
  val @(count7, _) = _entries(a)
  val t7 = _report("zip64 entry of 2^32 or more", count7 = 1)
  val () = _put(a, 182, 0)
  (* the locator's signature broken: the end record's saturated fields
     name no directory *)
  val () = _put(a, 333, 0)
  val @(c8, _, _) = _directory(a, 375)
  val t8 = _report("saturated end record without a locator", c8 = ~1)
  val () = _put(a, 333, 80)
  (* the ZIP64 record's entry count 65536: more than a directory this reader
     takes (a count is under 65536), so none *)
  val () = _put(a, 311, 1)
  val () = _put(a, 309, 0)
  val @(c9, _, _) = _directory(a, 375)
  val t9 = _report("zip64 entry count 65536", c9 = ~1)
  val () = _put(a, 311, 0)
  val () = _put(a, 309, 2)
  (* a.txt's extra field has another id: its saturated sizes have no ZIP64
     field to come from, the entry is left out, dir/b.xml is not *)
  val () = _put(a, 174, 2)
  val @(count10, _) = _entries(a)
  val t10 = _report("saturated field without a ZIP64 extra", count10 = 1)
  val () = _put(a, 174, 1)
  (* a.txt's ZIP64 extra field 8 bytes long holds the size but not the
     compressed size: the entry is left out *)
  val () = _put(a, 176, 8)
  val @(count11, _) = _entries(a)
  val t11 = _report("truncated ZIP64 extra, second value missing", count11 = 1)
  (* and 4 bytes long it holds neither *)
  val () = _put(a, 176, 4)
  val @(count12, _) = _entries(a)
  val t12 = _report("truncated ZIP64 extra, no value", count12 = 1)
  val () = _put(a, 176, 16)
  (* a.txt's compressed size in its record, so its extra field holds the
     size alone, 8 bytes, then another ZIP64 field (4 bytes) after it: the
     first field is the one read, so the entry is the same as before *)
  val () = _put(a, 143, 5)
  val () = _put(a, 144, 0)
  val () = _put(a, 145, 0)
  val () = _put(a, 146, 0)
  val () = _put(a, 176, 8)
  val () = _put(a, 186, 1)
  val () = _put(a, 187, 0)
  val () = _put(a, 188, 4)
  val () = _put(a, 189, 0)
  val () = _put(a, 190, 99)
  val @(count13, entries13) = _entries(a)
  val t13 = _report("duplicated ZIP64 extra, the first is read", count13 = 2 && entries13)
  (* the end record's count 65535 and its real size and offset, with no
     locator: a classic archive of that many entries, found as it says *)
  val () = _put(a, 333, 0)
  val () = _put(a, 363, 255)
  val () = _put(a, 364, 255)
  val () = _put(a, 365, 154)
  val () = _put(a, 366, 0)
  val () = _put(a, 367, 0)
  val () = _put(a, 368, 0)
  val () = _put(a, 369, 123)
  val () = _put(a, 370, 0)
  val () = _put(a, 371, 0)
  val () = _put(a, 372, 0)
  val @(c14, s14, d14) = _directory(a, 375)
  val t14 = _report("entry count 65535 without a locator", c14 = 123 && s14 = 154 && d14 = 65535)
  val () = $A.free<byte>(a)
  val ok = t1 && t2 && t3 && t4 && t5 && t6 && t7 && t8 && t9 && t10 && t11 && t12 && t13 && t14
in
  if ok then println! ("zip64: all cases pass")
  else exit_void(1)
end
