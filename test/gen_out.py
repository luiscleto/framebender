#!/usr/bin/env python3
# test/gen_out.py DIR [PAD PAD2 PAD3]: VCFs (for test/edge/ref.fa) whose output
# tests the BGZF writer's block cuts (test/out.sh). Every record is a <DEL> passed
# through unchanged, so the output's lines are the input's:
#   lines.vcf   records of 65279, 65280, 65281, 130560 and 200000 bytes (LF
#               included), between short ones: lines that just fit a block,
#               fill it, or span several;
#   crlf.vcf    every line ending in CR LF;
#   rand.vcf    incompressible records (random bytes, no tab, CR or LF): one
#               of 60000 bytes and one of 300000;
#   nolf.vcf    a last line without LF;
#   hdronly.vcf a header and no records;
#   hdrbig.vcf  a header of 3000 contig lines (longer than a block);
#   hdrwin.vcf  a header padded by PAD bytes, hdrwin2.vcf by PAD2 (test/out.sh
#               picks them so that the output's header ends exactly at the
#               first block boundary, and at the second);
#   tailwin.vcf a header of about 40000 bytes padded by PAD3 (test/out.sh
#               picks it so that the whole output is exactly one window: its
#               records are carried past the header's cut to the end, and
#               written as bgzip writes its last bytes). It runs the writer's
#               uncut end (wend) but cannot tell it from cutting again: the
#               machine ends every text with LF, and then both give the same
#               block. They differ only for a text without a final LF.
import os
import random
import sys

d = sys.argv[1]
pad = int(sys.argv[2]) if len(sys.argv) > 2 else 0
pad2 = int(sys.argv[3]) if len(sys.argv) > 3 else 0
pad3 = int(sys.argv[4]) if len(sys.argv) > 4 else 0
os.makedirs(d, exist_ok=True)
rnd = random.Random(20261029)
HEAD = '##fileformat=VCFv4.2\n'
COLS = '#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n'


def rec(pos, length, nl='\n'):
    pre = 't1\t%d\t.\tA\t<DEL>\t.\t.\tX=' % pos
    return pre + 'a' * (length - len(pre) - len(nl)) + nl


def short(pos, nl='\n'):
    return 't1\t%d\t.\tA\t<DEL>\t.\t.\t.%s' % (pos, nl)


def write(name, text):
    with open(os.path.join(d, name), 'wb') as f:
        f.write(text.encode('latin-1') if isinstance(text, str) else text)


body = []
pos = 1
for length in [65279, 65280, 65281, 130560, 200000]:
    for _ in range(3):
        body.append(short(pos)); pos += 1
    body.append(rec(pos, length)); pos += 1
for _ in range(2000):
    body.append(short(pos)); pos += 1
write('lines.vcf', HEAD + COLS + ''.join(body))

write('crlf.vcf', (HEAD + COLS).replace('\n', '\r\n') + ''.join(short(p, '\r\n') for p in range(1, 3000)))

alphabet = bytes(c for c in range(32, 256) if c not in (9, 10, 13))
rb = []
for p, n in [(1, 60000), (2, 300000)]:
    rb.append(('t1\t%d\t.\tA\t<DEL>\t.\t.\tR=' % p).encode() + bytes(rnd.choice(alphabet) for _ in range(n)) + b'\n')
write('rand.vcf', (HEAD + COLS).encode() + b''.join(rb) + ''.join(short(p) for p in range(3, 500)).encode())

write('nolf.vcf', HEAD + COLS + ''.join(short(p) for p in range(1, 1000)) + short(1000)[:-1])

write('hdronly.vcf', HEAD + COLS)

write('hdrbig.vcf', HEAD + ''.join('##contig=<ID=c%06d,length=100>\n' % i for i in range(3000)) + COLS + ''.join(short(p) for p in range(1, 3000)))

for name, n in [('hdrwin.vcf', pad), ('hdrwin2.vcf', pad2)]:
    write(name, HEAD + '##pad=' + 'p' * (100 + n) + '\n' + COLS + ''.join(short(p) for p in range(1, 3000)))

write('tailwin.vcf', HEAD + '##pad=' + 'p' * (40000 + pad3) + '\n' + COLS + ''.join(short(p) for p in range(1, 600)))
