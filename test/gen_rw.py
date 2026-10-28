#!/usr/bin/env python3
# Inputs for the rewrite path (phase C): a FASTA (rw.fa) and VCFs in data/tmp/rw/in/.
import random, os
rng = random.Random(11)
D = 'data/tmp/rw'
os.makedirs(f'{D}/in', exist_ok=True)

def rnd(n, alpha='ACGT'):
    return ''.join(rng.choice(alpha) for _ in range(n))

# c1: repeats at the start, tandem repeats, lower case, IUPAC letters, N runs.
parts = ['AAAAAAAAAA', 'CACACACA', rnd(300)]
for i in range(60):
    u = rng.choice(['A', 'C', 'AT', 'CAG', 'GATA', 'TTTGT', 'CA'])
    parts.append(u * rng.randint(3, 25))
    seg = rnd(rng.randint(20, 200))
    r = rng.random()
    if r < 0.2: seg = seg.lower()
    elif r < 0.3: seg = ''.join(c if rng.random() < 0.9 else rng.choice('RYKMSWBDHVN') for c in seg)
    elif r < 0.35: seg = 'N' * len(seg)
    parts.append(seg)
c1 = ''.join(parts)
# c2: a 6 kb CA repeat (moves longer than the tiny-limit build's 4 K margin).
c2 = rnd(1000) + 'CA' * 3000 + rnd(1000)
# c3: tiny.
c3 = 'GGGTTTACGT'
contigs = [('c1', c1), ('c2', c2), ('c3', c3)]
with open(f'{D}/rw.fa', 'w') as f:
    for n, s in contigs:
        f.write('>' + n + ' test\n')
        for i in range(0, len(s), 60): f.write(s[i:i+60] + '\n')
seqs = dict(contigs)

HDR = ['##fileformat=VCFv4.2'] + [f'##contig=<ID={n},length={len(s)}>' for n, s in contigs] + \
      ['##INFO=<ID=END,Number=1,Type=Integer,Description="End">',
       '#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\tS1']
INFOS = ['DP=1', '.', 'CIGAR=1M', 'HOMLEN=2', 'AA=A', 'HOMSEQ=A', 'AAA=1', 'xAA=1', 'CIGARX=1',
         'DP=1;AA', 'AA;DP=2', 'DP=1;HOMLEN', 'DP=3;CIGAR', '', 'A=1;HOMSEQX=2;HOMLE=1', 'DP=1;;X=2;',
         'EN=1;ENDX=2', 'DP=5;AA=;Z=1', 'HOMLEN=1=2', 'platforms=2;datasets=3;callsets=4']

def case(s):
    r = rng.random()
    if r < 0.6: return s
    if r < 0.8: return s.lower()
    return ''.join(c.lower() if rng.random() < 0.5 else c for c in s)

def variant(seq, x):
    L = rng.randint(1, 8)
    ref = seq[x:x + L]
    if len(ref) == 0: return None
    def one():
        t = rng.random()
        if t < 0.4 and len(ref) >= 2:
            i = rng.randint(0, len(ref) - 1); j = rng.randint(i + 1, len(ref))
            a = ref[:i] + ref[j:]
            return a if a else ref[0] + rnd(1)
        if t < 0.8:
            i = rng.randint(0, len(ref))
            ins = ref[max(0, i - 3):i] if rng.random() < 0.5 and i > 0 else rnd(rng.randint(1, 4))
            return ref[:i] + ins + ref[i:]
        return ''.join(rng.choice('ACGT') if rng.random() < 0.4 else c for c in ref)
    nalt = 1 if rng.random() < 0.75 else rng.choice([2, 3, 4, 16, 17])
    alts = []
    for _ in range(nalt):
        a = one()
        r = rng.random()
        if r < 0.01: a = '*'
        elif r < 0.02: a = ref.lower() if ref.upper() == ref else ref.upper()
        elif r < 0.03: a = a + 'R'
        elif r < 0.04: a = 'N' + a
        alts.append(a)
    ref2 = ref
    if rng.random() < 0.02: ref2 = ''.join('ACGT'[('ACGT'.index(c) + 1) % 4] if c in 'ACGT' else c for c in ref.upper())
    if rng.random() < 0.02: ref2 = 'N' + ref2[1:]
    return ref2, alts

def rec(chrom, pos, ref, alts, info=None, cols=10, posw=None):
    f = [chrom, posw or str(pos), '.', case(ref), ','.join(case(a) for a in alts), '50', 'PASS',
         rng.choice(INFOS) if info is None else info]
    if cols >= 10: f += ['GT', '0/1']
    elif cols == 9: f += ['GT']
    return '\t'.join(f)

def body(chrom, n, lo=0, hi=None, step=None):
    s = seqs[chrom]; hi = hi or len(s) - 10
    out = []
    xs = sorted(rng.randint(lo, hi) for _ in range(n)) if step is None else list(range(lo, hi, step))
    for x in xs:
        v = variant(s, x)
        if v is None: continue
        posw = None
        if rng.random() < 0.02: posw = '0' + str(x + 1)
        cols = rng.choice([10, 10, 10, 9, 8])
        out.append(rec(chrom, x + 1, v[0], v[1], cols=cols, posw=posw))
    return out

def write(name, lines, end='\n'):
    open(f'{D}/in/{name}.vcf', 'w', newline='').write(end.join(HDR + lines) + end)

mix = body('c1', 3000) + body('c3', 6, 0, 8, 1)
write('mix', mix)
write('crlf', mix[:800], '\r\n')
write('start', body('c1', 0, 0, 40, 1))
# long moves: deletions/insertions of CA at the right end of c2's repeat, and in the middle.
far = []
e = 1000 + 6000
for k in range(20):
    x = e - 2 * k - 2
    far.append(rec('c2', x + 1, c2[x:x + 4], [c2[x:x + 2]], info='DP=1'))
    far.append(rec('c2', x + 1, c2[x:x + 2], [c2[x:x + 4]], info='DP=1'))
far.append(rec('c2', 4001, c2[4000:4004], [c2[4000:4002]], info='DP=1'))
far.sort(key=lambda l: int(l.split('\t')[1]))
write('far', far)
write('multi', [l for l in body('c1', 4000) if ',' in l.split('\t')[4]])
# A record moving before already written ones; a CHROM coming back.
write('chroms', body('c1', 50, 0, 3000) + body('c3', 4, 0, 8, 2) + body('c1', 5, 3000, 4000))
# INFO last field ending in CR (8 columns), and CR in a 10-column line.
cr = []
for l in body('c1', 300):
    f = l.split('\t')
    cr.append('\t'.join(f[:8]) + '\r' if rng.random() < 0.5 else l + '\r')
write('cr', cr)
