#!/usr/bin/env python3
"""Rewrite each biallelic record of a VCF in random equivalent forms (test data).

Each output record makes the same change to the reference as its input record,
but at a random place along the repeat it sits in, with random extra shared
bases on either side, and sometimes in lower case. Used to compare
`framebender norm` with `bcftools norm` on records that need normalizing.

usage: scramble.py ref.fa in.vcf copies seed > out.vcf
"""
import random, sys

def read_fasta(path):
    seqs, name, buf = {}, None, []
    with open(path) as f:
        for line in f:
            if line.startswith('>'):
                if name: seqs[name] = ''.join(buf)
                name, buf = line[1:].split()[0], []
            else:
                buf.append(line.strip())
    if name: seqs[name] = ''.join(buf)
    return seqs

def main():
    ref, vcf, copies, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed)
    seqs = read_fasta(ref)
    out = []
    for line in open(vcf):
        if line.startswith('#'):
            sys.stdout.write(line); continue
        f = line.rstrip('\n').split('\t')
        chrom, pos, r, a = f[0], int(f[1]), f[3].upper(), f[4].upper()
        if ',' in a or not set(r + a) <= set('ACGTN') or chrom not in seqs:
            continue
        s = seqs[chrom].upper()
        if s[pos-1:pos-1+len(r)] != r:
            continue
        lo = max(0, pos - 1 - 300); hi = min(len(s), pos - 1 + len(r) + 300)
        old = s[lo:hi]
        new = s[lo:pos-1] + a + s[pos-1+len(r):hi]
        d = len(new) - len(old)
        L = 0
        while L < min(len(old), len(new)) and old[L] == new[L]: L += 1
        R = 0
        while R < min(len(old), len(new)) - L and old[-1-R] == new[-1-R]: R += 1
        # the change lies in old[L:len(old)-R]; every window around it works
        for _ in range(copies):
            for _ in range(20):
                st = rng.randint(max(0, L - 12), L)
                en = rng.randint(len(old) - R, min(len(old), len(old) - R + 12))
                if st == 0 and lo > 0: continue
                if en == len(old) and hi < len(s): continue
                R2, A2 = old[st:en], new[st:en + d]
                if R2 and A2 and R2 != A2: break
            else:
                continue
            if rng.random() < 0.2: R2, A2 = R2.lower(), A2.lower()
            g = list(f); g[1] = str(lo + st + 1); g[3] = R2; g[4] = A2
            out.append((lo + st + 1, '\t'.join(g)))
    out.sort(key=lambda x: x[0])
    for _, l in out: print(l)

main()
