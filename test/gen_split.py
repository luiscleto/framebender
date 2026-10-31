#!/usr/bin/env python3
# test/gen_split.py DIR SEED [LINES]: a random reference DIR/s<SEED>.fa and a
# VCF DIR/s<SEED>.vcf of well-formed multiallelic records for -m -any against
# bcftools 1.24 (test/split.sh): two to five ALTs (SNVs, MNVs, deletions and
# insertions, some in repeats so they move left, some far into the contig),
# INFO of every Number (A, R, G, 1, ., and a flag), FORMAT GT, AD (R), PL (G),
# FA (A) and DP (1) with haploid, diploid, phased, partly missing and missing
# genotypes and missing values. REF always matches the reference.
import os, random, sys

d, seed = sys.argv[1], int(sys.argv[2])
nlines = int(sys.argv[3]) if len(sys.argv) > 3 else 300
rng = random.Random(seed)
os.makedirs(d, exist_ok=True)

# The reference: random bases with stretches of repeats.
parts = []
while sum(map(len, parts)) < 6000:
    if rng.random() < 0.3:
        unit = "".join(rng.choice("ACGT") for _ in range(rng.randint(1, 4)))
        parts.append(unit * rng.randint(2, 12))
    else:
        parts.append("".join(rng.choice("ACGT") for _ in range(rng.randint(5, 60))))
ref = "".join(parts)[:6000]
with open(os.path.join(d, "s%d.fa" % seed), "w") as f:
    f.write(">c1\n")
    for i in range(0, len(ref), 60):
        f.write(ref[i:i + 60] + "\n")

def alt_for(pos, r):
    k = rng.random()
    base = ref[pos - 1]
    if k < 0.35:                      # SNV or MNV, same length
        a = list(r)
        i = rng.randrange(len(a))
        a[i] = rng.choice([c for c in "ACGT" if c != a[i]])
        return "".join(a)
    if k < 0.65 and len(r) > 1:       # deletion keeping the first base
        return r[0] + r[1 + rng.randint(1, len(r) - 1):] if len(r) > 2 else r[0]
    if k < 0.85:                      # insertion: a repeat of what follows, or random
        nxt = ref[pos:pos + rng.randint(1, 4)] or "A"
        return r + (nxt if rng.random() < 0.6 else "".join(rng.choice("ACGT") for _ in range(rng.randint(1, 5))))
    return "".join(rng.choice("ACGT") for _ in range(rng.randint(1, 4)))

def ints(n):
    return ",".join("." if rng.random() < 0.08 else str(rng.randint(0, 99)) for _ in range(n))

def gt(nal, ploidy):
    if rng.random() < 0.06:
        return "."
    sep = "|" if rng.random() < 0.3 else "/"
    al = ["." if rng.random() < 0.05 else str(rng.randint(0, nal)) for _ in range(ploidy)]
    return sep.join(al)

samples = ["S%d" % i for i in range(rng.randint(1, 4))]
ploidy = [rng.choice([1, 2, 2, 2]) for _ in samples]
out = ["##fileformat=VCFv4.2", "##contig=<ID=c1,length=%d>" % len(ref),
       '##FILTER=<ID=q10,Description="q">',
       '##INFO=<ID=IA,Number=A,Type=Integer,Description="a">',
       '##INFO=<ID=IR,Number=R,Type=Integer,Description="r">',
       '##INFO=<ID=IG,Number=G,Type=Integer,Description="g">',
       '##INFO=<ID=I1,Number=1,Type=Integer,Description="one">',
       '##INFO=<ID=IX,Number=.,Type=String,Description="any">',
       '##INFO=<ID=SA,Number=A,Type=String,Description="sa">',
       '##INFO=<ID=FL,Number=0,Type=Flag,Description="flag">',
       '##FORMAT=<ID=GT,Number=1,Type=String,Description="gt">',
       '##FORMAT=<ID=AD,Number=R,Type=Integer,Description="ad">',
       '##FORMAT=<ID=PL,Number=G,Type=Integer,Description="pl">',
       '##FORMAT=<ID=FA,Number=A,Type=Float,Description="fa">',
       '##FORMAT=<ID=DP,Number=1,Type=Integer,Description="dp">',
       "\t".join(["#CHROM", "POS", "ID", "REF", "ALT", "QUAL", "FILTER", "INFO", "FORMAT"] + samples)]
pos = 20
for n in range(nlines):
    pos += rng.randint(0, 25)
    if pos > len(ref) - 40:
        break
    r = ref[pos - 1:pos - 1 + rng.randint(1, 4)]
    alts = []
    for _ in range(rng.randint(2, 5) * 3):
        a = alt_for(pos, r)
        if a and a != r and a not in alts:
            alts.append(a)
        if len(alts) >= rng.randint(2, 5):
            break
    if len(alts) < 2:
        continue
    na = len(alts)
    info = []
    if rng.random() < 0.7: info.append("IA=" + ints(na))
    if rng.random() < 0.6: info.append("IR=" + ints(na + 1))
    if rng.random() < 0.4: info.append("IG=" + ints((na + 1) * (na + 2) // 2))
    if rng.random() < 0.5: info.append("I1=" + str(rng.randint(0, 9)))
    if rng.random() < 0.3: info.append("IX=" + ",".join(rng.choice(["u", "v", "w"]) for _ in range(rng.randint(1, 3))))
    if rng.random() < 0.3: info.append("SA=" + ",".join(rng.choice(["p", "q", "."]) for _ in range(na)))
    if rng.random() < 0.2: info.append("FL")
    fmt = ["GT"] + [k for k in ("AD", "PL", "FA", "DP") if rng.random() < 0.6]
    cols = []
    for p in ploidy:
        vals = []
        for k in fmt:
            if k == "GT": vals.append(gt(na, p))
            elif k == "AD": vals.append(ints(na + 1))
            elif k == "PL": vals.append(ints((na + 1) * (na + 2) // 2 if p == 2 else na + 1))
            elif k == "FA": vals.append(",".join("." if rng.random() < 0.1 else "%g" % round(rng.random(), 2) for _ in range(na)))
            else: vals.append(str(rng.randint(0, 60)))
        if rng.random() < 0.05:
            vals = vals[:1]
        cols.append(":".join(vals))
    qual = rng.choice([".", "30", "4.5"])
    out.append("\t".join(["c1", str(pos), rng.choice([".", "id%d" % n]), r, ",".join(alts), qual,
                          rng.choice([".", "PASS", "q10"]), ";".join(info) or ".", ":".join(fmt)] + cols))
with open(os.path.join(d, "s%d.vcf" % seed), "w") as f:
    f.write("\n".join(out) + "\n")
