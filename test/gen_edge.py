#!/usr/bin/env python3
# Edge-case VCFs for the byte path, on chr22 (data/chr22.fa): written to data/tmp/edge2/.
import random, os
rng = random.Random(7)
seq = ''.join(l.strip() for l in open('data/chr22.fa') if not l.startswith('>'))
head = open('data/hg002.chr22.vcf').read().split('\n')
hdr = [l for l in head if l.startswith('#')]
body = [l for l in head if l and not l.startswith('#')]
out = 'data/tmp/edge2'
def w(name, lines, end='\n', last=True):
    s = end.join(lines) + (end if last else '')
    open(f'{out}/{name}.vcf', 'w', newline='').write(s)
def rec(pos, ref, alt, info='DP=1', chrom='chr22', extra='GT\t0/1', posw=None):
    return '\t'.join([chrom, posw or str(pos), '.', ref, alt, '50', 'PASS', info] + ([extra] if extra else []))
base = lambda p: seq[p-1]
recs = []
p = 20000000
def nxt():
    global p
    p += rng.randint(200, 2000)
    while base(p).upper() not in 'ACGT': p += 1
    return p
def snp(q, low=False):
    r = base(q).upper(); a = 'ACGT'.replace(r, '')[0]
    return (r.lower(), a.lower()) if low else (r, a)
cases = []
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='END=%d' % q))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='END=%d' % (q + 5)))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='END'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='ENDX=3;XEND=4;E=1;EN=2;END_=1'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='DP=1;END=%d;AA=2' % q))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='DP=1;END;X=1'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='DP=E;Q=EEND;R=END'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info=''))
q = nxt(); r, a = snp(q, low=True); cases.append(rec(q, r, a))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, posw='00' + str(q)))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a + ',' + a))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, r))
q = nxt(); r, a = snp(q); o = 'ACGT'.replace(r, '').replace(a, '')
cases.append(rec(q, r, a + ',' + o[0] + ',' + o[1]))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a + ',*'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, '<DEL>'))
q = nxt(); r, a = snp(q); cases.append(rec(q, 'N', a))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, 'N'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r + base(q+1).upper(), r))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, r + 'ACGTAC'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, r + 'ACG,' + r + 'TT'))
q = nxt(); cases.append(rec(q, base(q).upper() + base(q+1).upper(), base(q).upper() + 'T' if base(q+1).upper() != 'T' else base(q).upper() + 'A'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, extra=None))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, info='DP=1\tGT'))
q = nxt(); r, a = snp(q); cases.append(rec(q, 'R', a))
q = nxt(); r, a = snp(q); cases.append(rec(q, r, a, extra='GT\t0/1\t1/1\t./.'))
q = nxt(); r, a = snp(q); cases.append(rec(q, r + r, r))
q = nxt(); r, a = snp(q); cases.append(rec(q, 'A' if r != 'A' else 'C', a))
q = nxt(); cases.append(rec(q, base(q).upper(), 'ACGT'[(('ACGT'.index(base(q).upper()))+1) % 4], info='CIGAR=1M'))
good = hdr + cases
w('mix', good)
w('mix_crlf', good, end='\r\n')
w('mix_nolf', good, last=False)
w('mix_crlf_nolf', good, end='\r\n', last=False)
# lines that end with CR only on some lines, and an 8-field line ending in CR
lines = hdr + [c + ('\r' if i % 3 == 0 else '') for i, c in enumerate(cases)]
w('mix_somecr', lines)
q = nxt(); r, a = snp(q)
w('cr8', hdr + [rec(q, r, a, extra=None) + '\r'])
# errors (each stops the run under both -c e and -c w)
q = nxt(); r, a = snp(q)
w('pos0', hdr + [rec(q, r, a), rec(0, r, a, posw='0')])
w('posbig', hdr + [rec(q, r, a), rec(0, r, a, posw='99999999999')])
w('short', hdr + [rec(q, r, a), 'chr22\t%d\t.\t%s' % (q + 10, r)])
w('blank', hdr + [rec(q, r, a), ''])
w('nochrom', hdr + [rec(q, r, a), rec(q + 5, r, a, chrom='chrZZ')])
w('emptychrom', hdr + [rec(q, r, a), rec(q + 5, r, a, chrom='')])
w('back', hdr + [rec(q, r, a), rec(10000000, base(10000000).upper(), 'N' , chrom='chr22')])
w('unsorted_far', hdr + [rec(q, r, a), rec(q - 200000, base(q-200000).upper(), snp(q-200000)[1])])
w('headonly', hdr)
w('noheader', ['##x=1', rec(q, r, a)])
w('empty', [], last=False)
# real records, then CHROM changes away and back (chr22 only in this reference)
w('chromchange', hdr + body[:50] + [rec(q, r, a, chrom='chr21')])
# a line longer than a 3.5 MB piece
q = nxt(); r, a = snp(q)
big = rec(q, r, a, info='DP=1;X=' + 'x' * 4_000_000)
w('longline', hdr + body[:20] + [big] + body[20:40])
# many pieces' worth of real records with a few odd ones inside
mid = body[:20000]
w('bodycr', hdr + mid, end='\r\n')
