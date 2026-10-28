#!/usr/bin/env python3
# Inputs for the parallel machine's batch boundaries (phase E): a FASTA
# (par.fa) and VCFs in data/tmp/par/, for the builds with pieces of 300,
# 1,000 and 70,001 bytes and the normal one (3,670,016). A piece boundary of
# a build with pieces of P bytes is at every multiple of P.
#   sorted_*: sorted records on four contigs, lines of every length;
#   chrom_P: CHROM changes placed exactly at piece boundaries of P (a line
#     starting at the boundary, straddling it, or the first complete line
#     after it);
#   left_P: indels in long repeats right after boundaries of P, which
#     normalize to a POS far to the left (across the boundary);
#   back_small, back_far, revisit: POS going back within and beyond the
#     window, a CHROM coming back (UNSORTED);
#   bad_*: a REF mismatch, a malformed line, an unknown CHROM in the middle
#     of a batch, and many warnings;
#   short_*, n31/n32/n33/n64 (exactly that many pieces of 1,000 bytes, and
#     a few bytes more), a long header, no final LF, CRLF;
#   snp_*: SNPs only (no record moves left, so -w 1 runs to the end and most
#     pieces merge), sorted, with warnings, POS back, swaps, a CHROM
#     revisited, CRLF, a long header.
# Run from the repository root; then samtools faidx data/tmp/par/par.fa.
import random, os
rng = random.Random(23)
D = 'data/tmp/par'
os.makedirs(D, exist_ok=True)

def rnd(n):
    return ''.join(rng.choice('ACGT') for _ in range(n))

def contig(n):
    parts = []
    while sum(map(len, parts)) < n:
        r = rng.random()
        if r < 0.05:
            u = rng.choice(['A', 'CA', 'GAT', 'TTTG'])
            parts.append(u * rng.randint(200, 1500))
        elif r < 0.3:
            u = rng.choice(['A', 'C', 'AT', 'CAG'])
            parts.append(u * rng.randint(3, 20))
        else:
            parts.append(rnd(rng.randint(50, 400)))
    s = ''.join(parts)[:n]
    return s

contigs = [('p1', contig(300000)), ('p2', contig(300000)), ('p3', contig(100000)), ('p4', contig(5000))]
seqs = dict(contigs)
with open(f'{D}/par.fa', 'w') as f:
    for n, s in contigs:
        f.write('>' + n + '\n')
        for i in range(0, len(s), 60):
            f.write(s[i:i + 60] + '\n')

HDR = ['##fileformat=VCFv4.2'] + [f'##contig=<ID={n},length={len(s)}>' for n, s in contigs] + \
      ['##INFO=<ID=PAD,Number=1,Type=String,Description="Padding">',
       '#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\tS1']
HEAD = '\n'.join(HDR) + '\n'

def pad(n):
    return 'PAD=' + 'x' * n if n > 0 else '.'

def line(c, pos, ref, alt, padn=None):
    if padn is None:
        padn = rng.choice([0, 0, rng.randint(0, 60), rng.randint(0, 400)])
    return f'{c}\t{pos}\t.\t{ref}\t{alt}\t50\tPASS\t{pad(padn)}\tGT\t0/1\n'

def snp(c, x):
    r = seqs[c][x]
    return (x + 1, r, rng.choice([b for b in 'ACGT' if b != r]))

def indel(c, x):
    s = seqs[c]
    L = rng.randint(1, 4)
    ref = s[x:x + L + 1]
    if rng.random() < 0.5:
        return (x + 1, ref, ref[0])
    return (x + 1, ref[0], ref[0] + s[x + 1:x + 1 + L])

SNP_ONLY = False

def rec(c, x):
    r = rng.random()
    if r < 0.7 or SNP_ONLY:
        return snp(c, x)
    return indel(c, x)

def body(c, x0, x1, step):
    out = []
    x = x0
    while x < x1 - 10:
        p, ref, alt = rec(c, x)
        out.append(line(c, p, ref, alt))
        x += rng.randint(1, step)
    return out

def write(name, text):
    with open(f'{D}/{name}.vcf', 'w', newline='') as f:
        f.write(text)

# Sorted files of several sizes and densities.
for name, step in [('sorted_s', 4000), ('sorted_m', 400), ('sorted_l', 60)]:
    ls = []
    for c, s in contigs:
        ls += body(c, 0, len(s), step)
    write(name, HEAD + ''.join(ls))

# Repeats: (contig, start, end) of runs of one unit at least 300 long.
def repeats(c):
    s = seqs[c]
    out = []
    for u in ['A', 'CA', 'GAT', 'TTTG']:
        i = s.find(u * 100)
        while i >= 0:
            j = i
            while s[j:j + len(u)] == u:
                j += len(u)
            if j - i >= 300:
                out.append((i, j, u))
            i = s.find(u * 100, j)
    return sorted(out)

# A file built line by line (fill_to lays lines out to end at an offset).
class File:
    def __init__(self):
        self.text = HEAD
    def add(self, l):
        self.text += l

def exact(c, x, n):
    # A line of contig c at x of exactly n bytes (n >= 44), or None.
    p, ref, alt = snp(c, x)
    base = len(line(c, p, ref, alt, 0))
    if n == base:
        return line(c, p, ref, alt, 0)
    if n >= base + 4:
        return line(c, p, ref, alt, n - base - 3)
    return None

def fill_to(f, at, c, x):
    # SNP lines of contig c from x on, the last one ending exactly at `at`.
    while True:
        left = at - len(f.text)
        if left <= 0:
            raise ValueError('passed')
        if left <= 450:
            l = exact(c, x, left)
            if l is not None:
                f.add(l)
                return x + rng.randint(1, 5)
            # too short for one line: take a longer one now and aim again
        p, ref, alt = snp(c, x)
        f.add(line(c, p, ref, alt, rng.randint(0, 100)))
        x += rng.randint(1, max(1, min(200, (len(seqs[c]) - x - 300) // max(1, left // 40))))

# CHROM changes at piece boundaries of P: the new CHROM's first line starts
# exactly at the boundary, starts 20 bytes before it (straddles), or is the
# first complete line after a line that straddles it.
for P in [300, 1000, 70001]:
    f = File()
    order = ['p1', 'p2', 'p3', 'p4']
    ci, x = 0, 0
    b = 1
    for kind in ['at', 'straddle', 'after', 'at', 'after', 'straddle']:
        if ci + 1 >= len(order):
            break
        while b * P < len(f.text) + 600:
            b += 1
        c = order[ci]
        target = b * P
        if kind == 'at':
            x = fill_to(f, target, c, x)
        elif kind == 'straddle':
            x = fill_to(f, target - 20, c, x)
        else:
            x = fill_to(f, target - 30, c, x)
            p, ref, alt = snp(c, x)
            f.add(line(c, p, ref, alt, 40))
        ci += 1
        c = order[ci]
        x = rng.randint(0, 1000)
        for i in range(rng.randint(3, 8)):
            p, ref, alt = snp(c, x)
            f.add(line(c, p, ref, alt))
            x += rng.randint(5, 200)
        b += 2
    write(f'chrom_{P}', f.text)

# Indels in repeats right after boundaries of P: the record normalizes to the
# repeat's start, left of the records before the boundary.
for P in [300, 1000, 70001]:
    f = File()
    c = 'p1'
    reps = [r for r in repeats(c) if r[1] - r[0] >= 300]
    x = 0
    b = 1
    for (i, j, u) in reps[:12]:
        if i < x + 50:
            continue
        x = i + 1
        while b * P < len(f.text) + 600:
            b += 1
        # records inside the repeat (SNP-free: refs from the repeat) up to
        # the boundary, then the indel near the repeat's end
        try:
            x = fill_to(f, b * P - rng.choice([0, 10, 30]), c, x)
        except ValueError:
            b += 1
            continue
        y = max(x, j - 3 * len(u))
        if y >= j:
            y = j - len(u)
        ref = seqs[c][y - 1:y + len(u)]
        f.add(line(c, y, ref, ref[0], 10))
        x = j + 5
        b += 1
    for z in body(c, x, x + 20000, 300):
        f.add(z)
    write(f'left_{P}', f.text)

# POS going back (within the window, and beyond it), a CHROM revisited.
ls = body('p1', 0, 300000, 200)
k = len(ls) // 2
q = ls[k].split('\t')
ls.insert(k + 1, line('p1', int(q[1]) - 50, seqs['p1'][int(q[1]) - 51], 'G' if seqs['p1'][int(q[1]) - 51] != 'G' else 'T'))
write('back_small', HEAD + ''.join(ls))
ls2 = list(ls)
q = ls2[k + 40].split('\t')
x = int(q[1]) - 150000
ls2.insert(k + 41, line('p1', x + 1, seqs['p1'][x], 'G' if seqs['p1'][x] != 'G' else 'T'))
write('back_far', HEAD + ''.join(ls2))
ls3 = body('p1', 0, 150000, 200) + body('p2', 0, 100000, 200) + body('p1', 150000, 300000, 200)
write('revisit', HEAD + ''.join(ls3))
# Unsorted all through: small swaps everywhere.
ls4 = body('p2', 0, 300000, 150)
for i in range(0, len(ls4) - 1, 7):
    ls4[i], ls4[i + 1] = ls4[i + 1], ls4[i]
write('swaps', HEAD + ''.join(ls4))

# Problems in the middle of a batch.
ls = body('p1', 0, 300000, 150)
k = len(ls) * 3 // 5
q = ls[k].split('\t')
q[3] = ('C' if seqs['p1'][int(q[1]) - 1] != 'C' else 'G')
bad = list(ls); bad[k] = '\t'.join(q)
write('bad_ref', HEAD + ''.join(bad))
bad = list(ls); bad[k] = 'p1\t' + q[1] + '\tmalformed\n'
write('bad_malformed', HEAD + ''.join(bad))
bad = list(ls); bad[k] = bad[k].replace('p1\t', 'zz\t', 1)
write('bad_chrom', HEAD + ''.join(bad))
many = list(ls)
for i in range(5, len(many), 37):
    q = many[i].split('\t')
    q[3] = 'C' if seqs['p1'][int(q[1]) - 1] != 'C' else 'G'
    many[i] = '\t'.join(q)
write('bad_many', HEAD + ''.join(many))
# A stale-looking record (non-ACGTN ALT) now and then.
odd = list(ls)
for i in range(3, len(odd), 53):
    q = odd[i].split('\t')
    q[4] = 'R'
    odd[i] = '\t'.join(q)
write('bad_alt', HEAD + ''.join(odd))

# Short files and exact piece counts (P = 1,000).
write('short_head', HEAD)
write('short_one', HEAD + line('p1', 100, seqs['p1'][99], 'T' if seqs['p1'][99] != 'T' else 'A'))
write('short_few', HEAD + ''.join(body('p3', 0, 5000, 300)))
write('short_nolf', (HEAD + ''.join(body('p3', 0, 30000, 300)))[:-1])
write('short_crlf', (HEAD + ''.join(body('p3', 0, 60000, 300))).replace('\n', '\r\n'))
for n in [31, 32, 33, 64]:
    f = File()
    c, x = 'p2', 0
    x = fill_to(f, n * 1000, c, x)
    write(f'n{n}', f.text)
    write(f'n{n}x', f.text + line(c, x + 1, seqs[c][x], 'A' if seqs[c][x] != 'A' else 'C')[:30])
longh = HEAD.replace('##fileformat=VCFv4.2\n', '##fileformat=VCFv4.2\n' + ''.join(f'##note{i}=' + 'y' * 90 + '\n' for i in range(900)))
write('long_head', longh + ''.join(body('p1', 0, 300000, 100)))

# SNP-only variants.
SNP_ONLY = True
ls = []
for c, s in contigs:
    ls += body(c, 0, len(s), 120)
write('snp_sorted', HEAD + ''.join(ls))
many = list(ls)
for i in range(5, len(many), 37):
    q = many[i].split('\t')
    q[3] = 'C' if seqs[q[0]][int(q[1]) - 1] != 'C' else 'G'
    many[i] = '\t'.join(q)
write('snp_warn', HEAD + ''.join(many))
back = list(ls)
for i in range(50, len(back), 400):
    q = back[i].split('\t')
    x = max(0, int(q[1]) - 30)
    back.insert(i + 1, line(q[0], x + 1, seqs[q[0]][x], 'G' if seqs[q[0]][x] != 'G' else 'T'))
write('snp_back', HEAD + ''.join(back))
sw = list(ls)
for i in range(0, len(sw) - 1, 97):
    sw[i], sw[i + 1] = sw[i + 1], sw[i]
write('snp_swaps', HEAD + ''.join(sw))
write('snp_revisit', HEAD + ''.join(body('p1', 0, 150000, 120) + body('p2', 0, 100000, 120) + body('p3', 0, 100000, 120) + body('p2', 100000, 300000, 120)))
write('snp_crlf', (HEAD + ''.join(ls)).replace('\n', '\r\n'))
write('snp_head', longh + ''.join(ls))
