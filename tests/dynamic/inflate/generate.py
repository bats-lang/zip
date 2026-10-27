#!/usr/bin/env python3
"""Makes tests/dynamic/inflate/data and refuse: the streams the dynamic test inflates.

zlib is the reference, used as it is: every expected output below is zlib's
own (`zlib.decompress(stream, -15)`), never ours. Bats has no deflate
compressor, so streams of chosen kinds (stored, fixed, dynamic, real
chapters) can only come from zlib; a decoder tested on streams of its own
making would test nothing about RFC 1951. The hand-made fixed-code streams
below are bit strings written by `Bits`; zlib decides what they inflate to.

usage: generate.py QUIRE_CHECKOUT OUT_DIR [CHAPTER_DIR]   (python3, the standard library only)
With CHAPTER_DIR it also writes the 1 MiB chapter of the wasm speed measure there: chapter.deflate and
chapter.expect (sha256, size, compressed size).
Writes OUT_DIR/data/NN.deflate and NN.expect, OUT_DIR/refuse/NN.deflate and
NN.expect, and the two cases.txt that name each stream.
  data   NN.expect is "<s|o> <sha256 of zlib's output, 64 hex digits> <its size>":
         s all blocks stored (the stored decoders must take it), o otherwise
         (they must refuse it).
  refuse NN.expect is two letters, the reader fate (c closed before its end,
         e ended) for the stored decoder and for the full decoder.
"""
import hashlib
import os
import random
import struct
import sys
import zipfile
import zlib

EPUBS = ['e2e/calculus101-mathml-test.epub', 'test/fixtures/conan-stories.epub', 'test/fixtures/strikerville-he.epub']


def raw_deflate(data, level=6, strategy=zlib.Z_DEFAULT_STRATEGY):
    c = zlib.compressobj(level, zlib.DEFLATED, -15, 9, strategy)
    return c.compress(data) + c.flush()


def inflate(stream):
    d = zlib.decompressobj(-15)
    out = d.decompress(stream)
    assert d.eof and not d.unused_data, 'zlib does not take the stream whole'
    return out


class Bits:
    """The bit string of a deflate stream: data elements least significant bit first,
    Huffman codes most significant bit first (RFC 1951 3.1.1)."""

    def __init__(self):
        self.bits = []

    def value(self, v, width):
        for i in range(width):
            self.bits.append((v >> i) & 1)

    def code(self, v, width):
        for i in range(width - 1, -1, -1):
            self.bits.append((v >> i) & 1)

    def align(self):
        while len(self.bits) % 8:
            self.bits.append(0)

    def header(self, final, btype):
        self.value(final, 1)
        self.value(btype, 2)

    def literal(self, sym):  # 3.2.6, the fixed literal/length code
        if sym < 144:
            self.code(0x30 + sym, 8)
        elif sym < 256:
            self.code(0x190 + sym - 144, 9)
        elif sym < 280:
            self.code(sym - 256, 7)
        else:
            self.code(0xC0 + sym - 280, 8)

    def end(self):
        self.literal(256)

    LENGTH_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]
    LENGTH_EXTRA = [0] * 8 + [1] * 4 + [2] * 4 + [3] * 4 + [4] * 4 + [5] * 4 + [0]
    DISTANCE_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073,
                     4097, 6145, 8193, 12289, 16385, 24577]
    DISTANCE_EXTRA = [0] * 4 + [e for e in range(1, 14) for _ in range(2)]

    def copy(self, length, distance):
        li = max(i for i, base in enumerate(self.LENGTH_BASE) if base <= length)
        if length == 258:
            li = 28
        self.literal(257 + li)
        self.value(length - self.LENGTH_BASE[li], self.LENGTH_EXTRA[li])
        di = max(i for i, base in enumerate(self.DISTANCE_BASE) if base <= distance)
        self.code(di, 5)
        self.value(distance - self.DISTANCE_BASE[di], self.DISTANCE_EXTRA[di])

    def stored(self, data, final):  # a stored block: its header, the padding, LEN, NLEN, the data
        self.header(final, 0)
        self.align()
        for byte in struct.pack('<HH', len(data), len(data) ^ 0xFFFF) + data:
            self.value(byte, 8)

    def bytes(self):
        self.align()
        return bytes(sum(b << i for i, b in enumerate(self.bits[k:k + 8])) for k in range(0, len(self.bits), 8))


def stored_block(data, final):
    return bytes([1 if final else 0]) + struct.pack('<HH', len(data), len(data) ^ 0xFFFF) + data


def text(seed, size):
    rng = random.Random(seed)
    words = ['chapter', 'the', 'of', 'and', 'a', 'to', 'in', 'is', 'that', 'it', 'was', 'for', 'on', 'are', 'with', 'as', 'his', 'they',
             'be', 'at', 'one', 'have', 'this', 'from', 'or', 'had', 'by', 'hot', 'word', 'but', 'what', 'some', 'we', 'can', 'out',
             'other', 'were', 'all', 'there', 'when', 'up', 'use', 'your', 'how', 'said', 'an', 'each', 'she', '<p class="x">', '</p>',
             'derivative', 'integral', 'limit', 'x', '2', '3.14159', '&amp;', '\n']
    out = bytearray()
    while len(out) < size:
        out += rng.choice(words).encode() + b' '
    return bytes(out[:size])


def pseudo(seed, size):
    return random.Random(seed).randbytes(size)


def all_stored(stream):
    """Whether every block is stored (a stored block starts on a byte, after its 3 header bits and the padding)."""
    at = 0
    while True:
        header = stream[at]
        if (header >> 1) & 3:
            return False
        length = struct.unpack('<H', stream[at + 1:at + 3])[0]
        at += 5 + length
        if header & 1:
            return True


def data_cases(quire):
    cases = []  # (description, stream, all_stored)
    for size in (0, 1, 65535, 65536, 200000):
        c = zlib.compressobj(0, zlib.DEFLATED, -15)
        cases.append((f'zlib level 0, {size} pseudo-random bytes (stored blocks)', c.compress(pseudo(size, size)) + c.flush(), True))
    sample = text(1, 5000)
    cases.append(('zlib Z_FIXED, 5000 bytes of text', raw_deflate(sample, 6, zlib.Z_FIXED), False))
    cases.append(('zlib Z_FIXED, 1000 pseudo-random bytes (9 bit literals)', raw_deflate(pseudo(2, 1000), 6, zlib.Z_FIXED), False))
    cases.append(('zlib Z_FIXED, 300 times a (length 258, distance 1)', raw_deflate(b'a' * 300, 6, zlib.Z_FIXED), False))
    cases.append(('zlib Z_FIXED, no input (the end of block alone)', raw_deflate(b'', 6, zlib.Z_FIXED), False))

    b = Bits(); b.header(1, 1); b.literal(97); b.copy(258, 1); b.end()
    cases.append(('hand-made fixed: a, then a copy of length 258 distance 1, end of block right after the copy', b.bytes(), False))
    b = Bits(); b.header(1, 1)
    history = bytes((i * 7 + 3) % 251 for i in range(32768))
    for v in history:
        b.literal(v)
    b.copy(3, 32768); b.end()
    cases.append(('hand-made fixed: 32768 literals, then a copy of distance 32768', b.bytes(), False))
    b = Bits(); b.header(1, 1); b.literal(97); b.literal(98); b.copy(10, 2); b.end()
    cases.append(('hand-made fixed: ab, then a copy of length 10 distance 2 (overlaps itself)', b.bytes(), False))
    b = Bits(); b.header(1, 1)
    for v in b'xyz':
        b.literal(v)
    b.copy(3, 3); b.end()
    cases.append(('hand-made fixed: xyz, a copy of length 3 distance 3, end of block', b.bytes(), False))
    b = Bits(); b.header(1, 1); b.literal(97)
    for length in range(3, 259):
        b.copy(length, 1)
    b.end()
    cases.append(('hand-made fixed: a, then a copy of each length 3 to 258 at distance 1', b.bytes(), False))
    b = Bits(); b.header(1, 1)
    for v in history:
        b.literal(v)
    for di in range(30):
        lo = Bits.DISTANCE_BASE[di]
        hi = lo + (1 << Bits.DISTANCE_EXTRA[di]) - 1
        for distance in (lo, hi):
            b.copy(4, min(distance, 32768))
    b.end()
    cases.append(('hand-made fixed: 32768 literals, then copies at the first and last distance of each distance symbol', b.bytes(), False))
    b = Bits(); b.header(0, 1)
    for v in b'abcdef':
        b.literal(v)
    b.end(); b.header(1, 1); b.copy(6, 6); b.end()
    cases.append(('hand-made: a fixed block, then a fixed block that copies from the first', b.bytes(), False))
    b = Bits(); b.header(0, 1)
    for v in b'abc':
        b.literal(v)
    b.end(); b.stored(b'XY', 0); b.header(1, 1); b.copy(3, 3); b.end()
    cases.append(('hand-made: a fixed block, a stored block, a fixed block that copies from the first', b.bytes(), False))

    chapter = text(3, 60000)
    for level in range(1, 10):
        cases.append((f'zlib level {level}, 60000 bytes of text', raw_deflate(chapter, level), False))
    cases.append(('zlib Z_FILTERED level 6, text', raw_deflate(chapter, 6, zlib.Z_FILTERED), False))
    cases.append(('zlib Z_HUFFMAN_ONLY, text (no copies)', raw_deflate(chapter, 6, zlib.Z_HUFFMAN_ONLY), False))
    cases.append(('zlib Z_RLE, text', raw_deflate(chapter, 6, zlib.Z_RLE), False))
    cases.append(('zlib level 9, 100000 times a (a single distance code)', raw_deflate(b'a' * 100000, 9), False))
    cases.append(('zlib level 6, pseudo-random bytes (stored blocks in a compressed stream)', raw_deflate(pseudo(4, 70000), 6), False))

    for epub in EPUBS:
        path = os.path.join(quire, epub)
        with zipfile.ZipFile(path) as z, open(path, 'rb') as f:
            for info in z.infolist():
                if info.compress_type != 8:
                    continue
                f.seek(info.header_offset)
                local = f.read(30)
                name_len, extra_len = struct.unpack('<HH', local[26:30])
                f.seek(info.header_offset + 30 + name_len + extra_len)
                raw = f.read(info.compress_size)
                assert inflate(raw) == z.read(info), f'{epub} {info.filename}'
                cases.append((f'{os.path.basename(epub)} {info.filename} ({info.file_size} bytes)', raw, False))
    return cases


def chapter(quire):
    """The 1 MiB chapter of the speed measure: the XHTML of the three EPUBs' chapters, repeated and cut to exactly 1048576 bytes."""
    pages = []
    for epub in EPUBS:
        with zipfile.ZipFile(os.path.join(quire, epub)) as z:
            for info in z.infolist():
                if info.filename.endswith('.xhtml') or info.filename.endswith('.html'):
                    pages.append(z.read(info))
    body = b''.join(pages)
    return (body * (1048576 // len(body) + 1))[:1048576]


def refuse_cases(data):
    fixed_text = raw_deflate(text(1, 5000), 6, zlib.Z_FIXED)
    dynamic_text = raw_deflate(text(3, 60000), 6)
    cases = []  # (description, stream, fate letters for the stored decoder and the full decoder)
    cases.append(('no bytes', b'', 'ee'))
    cases.append(('a final stored block header and nothing after it', b'\x01', 'ee'))
    cases.append(('BTYPE 3 (reserved), final', b'\x07\x00\x00\x00\x00', 'cc'))
    cases.append(('BTYPE 3 (reserved), not final', b'\x06', 'cc'))
    cases.append(('a stored block whose NLEN is not the complement of LEN', b'\x01\x05\x00\x00\x00hello', 'cc'))
    cases.append(('a stored block that ends inside its data', b'\x01\x05\x00\xfa\xffhel', 'ee'))
    cases.append(('a stored block that is not final, and no block after it', b'\x00\x00\x00\xff\xff', 'ee'))
    cases.append(('a fixed block cut in the middle', fixed_text[:len(fixed_text) // 2], 'ce'))
    cases.append(('a dynamic block cut in the middle', dynamic_text[:len(dynamic_text) // 2], 'ce'))
    b = Bits(); b.header(1, 1); b.literal(97); b.copy(3, 2); b.end()
    cases.append(('a fixed block with a copy from before the start of the output', b.bytes(), 'cc'))
    b = Bits(); b.header(1, 1); b.literal(97); b.literal(257); b.code(30, 5); b.end()
    cases.append(('a fixed block with distance symbol 30', b.bytes(), 'cc'))
    b = Bits(); b.header(1, 2); b.value(30, 5); b.value(0, 5); b.value(0, 4)
    cases.append(('a dynamic block with HLIT 30 (more than 286 literal/length codes)', b.bytes() + bytes(40), 'cc'))
    b = Bits(); b.header(1, 2); b.value(0, 5); b.value(0, 5); b.value(0, 4)
    for _ in range(4):
        b.value(1, 3)
    cases.append(('a dynamic block whose code length code is over-subscribed (four codes of one bit)', b.bytes() + bytes(40), 'cc'))
    for description, stream, _ in cases:
        d = zlib.decompressobj(-15)
        try:
            d.decompress(stream)
            failed = not d.eof
        except zlib.error:
            failed = True
        assert failed, f'zlib takes the refusal case: {description}'
    return cases


def write(directory, index, stream, expect):
    with open(os.path.join(directory, '%02d.deflate' % index), 'wb') as f:
        f.write(stream)
    with open(os.path.join(directory, '%02d.expect' % index), 'w') as f:
        f.write(expect)


def main(argv):
    quire, out = argv[1], argv[2]
    data, refuse = os.path.join(out, 'data'), os.path.join(out, 'refuse')
    for d in (data, refuse):
        os.makedirs(d, exist_ok=True)
    listing = []
    kinds = {0: 0, 1: 0, 2: 0}
    for index, (description, stream, _) in enumerate(data_cases(quire)):
        output = inflate(stream)
        digest = hashlib.sha256(output).hexdigest()
        write(data, index, stream, '%s %s %d' % ('s' if all_stored(stream) else 'o', digest, len(output)))
        listing.append('%02d %s' % (index, description))
        kinds[(stream[0] >> 1) & 3] += 1
    with open(os.path.join(data, 'cases.txt'), 'w') as f:
        f.write('\n'.join(listing) + '\n')
    listing = []
    for index, (description, stream, fates) in enumerate(refuse_cases(data)):
        write(refuse, index, stream, fates)
        listing.append('%02d %s' % (index, description))
    with open(os.path.join(refuse, 'cases.txt'), 'w') as f:
        f.write('\n'.join(listing) + '\n')
    if len(argv) > 3:  # the speed measure's chapter (step 10 of zip#64), in its own directory
        os.makedirs(argv[3], exist_ok=True)
        output = chapter(quire)
        stream = raw_deflate(output, 6)
        assert inflate(stream) == output and len(output) == 1048576
        with open(os.path.join(argv[3], 'chapter.deflate'), 'wb') as f:
            f.write(stream)
        with open(os.path.join(argv[3], 'chapter.expect'), 'w') as f:
            f.write('%s %d %d\n' % (hashlib.sha256(output).hexdigest(), len(output), len(stream)))
        print('chapter:', open(os.path.join(argv[3], 'chapter.expect')).read().strip())
    print('data cases:', len(data_cases(quire)), 'first block stored/fixed/dynamic:', kinds[0], kinds[1], kinds[2])
    print('refuse cases:', len(listing))


if __name__ == '__main__':
    main(sys.argv)
