#!/usr/bin/env python3
# test/gen_index.py DIR: VCFs (for test/edge/ref.fa) for the index writer
# (-W; test/index.sh), beside test/gen_out.py's block-cut cases. Most records
# are symbolic (<DEL>, <*>), passed through unchanged (out of scope), so the
# output keeps their text, as tabix then reads it:
#   nul.vcf       a NUL byte inside a record's INFO;
#   hdr0.vcf      a header without ##contig lines and no records (the empty
#                 index: no length, the first CSI settings);
#   nolen.vcf     records, and no ##contig lines (CSI levels from min_shift);
#   len32.vcf     a ##contig length past 2^32 (more CSI levels);
#   len41.vcf     a ##contig length past 2^41 (CSI's min_shift moves);
#   many.vcf      300 contigs, one record each, in an order unlike the
#                 header's;
#   hashbody.vcf  body lines that start with '#' between records;
#   ends.vcf      ends tabix reads from INFO/END, SVLEN (<DEL>) and
#                 FORMAT/LEN (<*>), and INFO/END below POS, and POS 0;
#   endall.vcf    END= on every record (the lock around tbx_parse1);
#   lz.vcf        a POS with a leading zero (octal to tabix: refused);
#   tbipos.vcf    a POS past 2^29 (TBI refuses, CSI holds it);
#   tbiend.vcf    an INFO/END past 2^29 (the same);
#   csi38.vcf     no ##contig length and a POS past 2^38 (both refuse);
#   csi32.vcf     a short ##contig length and a POS past 2^32 (both refuse);
#   noff.vcf      no ##fileformat line (bcftools index refuses: it reads the
#                 format from the first 16 bytes; tabix holds it);
#   cfirst.vcf    a '#' line before ##fileformat (the same);
#   biglen.vcf    ##contig lines longer than a block, a length past 2^32
#                 before and after 70000 bytes (the lengths set CSI's levels).
import os
import sys

d = sys.argv[1]
os.makedirs(d, exist_ok=True)
H = "##fileformat=VCFv4.2\n"
INFO = '##INFO=<ID=END,Number=1,Type=Integer,Description="End">\n##INFO=<ID=SVLEN,Number=A,Type=Integer,Description="Length">\n##FORMAT=<ID=LEN,Number=1,Type=Integer,Description="Length">\n##FORMAT=<ID=GT,Number=1,Type=String,Description="Genotype">\n'
CTG = "##contig=<ID=t1,length=40>\n##contig=<ID=t2,length=3>\n"
COLS = "#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n"
COLS9 = "#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\ts1\n"


def rec(c, pos, info=".", alt="<DEL>", ref="A", rid="."):
    return "%s\t%s\t%s\t%s\t%s\t.\t.\t%s\n" % (c, pos, rid, ref, alt, info)


def put(name, text):
    with open(os.path.join(d, name), "wb") as f:
        f.write(text.encode("latin-1"))


put("nul.vcf", H + CTG + INFO + COLS + rec("t1", 5, "SVLEN=-3") + rec("t1", 9, "X=a\0b;SVLEN=-2") + rec("t1", 20, "SVLEN=-4"))
put("hdr0.vcf", H + INFO + COLS)
put("nolen.vcf", H + INFO + COLS + "".join(rec("t1", p, "SVLEN=-2") for p in (3, 7, 30)))
put("len32.vcf", H + "##contig=<ID=t1,length=5000000000>\n" + INFO + COLS + rec("t1", 4, "SVLEN=-2") + rec("t1", 4500000000, "SVLEN=-2"))
put("len41.vcf", H + "##contig=<ID=t1,length=3000000000000>\n" + INFO + COLS + rec("t1", 4, "SVLEN=-2") + rec("t1", 2900000000000, "SVLEN=-2"))
names = ["c%03d" % i for i in range(300)]
put("many.vcf", H + "".join("##contig=<ID=%s,length=1000>\n" % n for n in names) + INFO + COLS
    + "".join(rec(n, 10 + i % 50, "SVLEN=-2") for i, n in enumerate(reversed(names))))
put("hashbody.vcf", H + CTG + INFO + COLS + rec("t1", 5, "SVLEN=-2") + "#a body line\n" + rec("t1", 9, "SVLEN=-2") + "##another\n" + rec("t1", 20, "SVLEN=-2"))
put("ends.vcf", H + CTG + INFO + COLS9
    + "t1\t2\t.\tA\t<DEL>\t.\t.\tEND=30;SVLEN=-28\tGT\t0/1\n"
    + "t1\t3\t.\tA\t<DEL>\t.\t.\tSVLEN=-25\tGT\t0/1\n"
    + "t1\t4\t.\tA\t<*>\t.\t.\t.\tGT:LEN\t0/0:33\n"
    + "t1\t6\t.\tA\t<DEL>\t.\t.\tEND=2;SVLEN=-3\tGT\t0/1\n"
    + "t1\t7\t.\tA\t<NON_REF>\t.\t.\tEND=12\tGT:LEN\t0/0:5\n"
    + "t2\t0\t.\tG\t<DEL>\t.\t.\tSVLEN=-1\tGT\t0/1\n")
put("endall.vcf", H + CTG + INFO + COLS + "".join(rec("t1", p, "END=%d;SVLEN=-2" % (p + 2 if p % 5 else 1)) for p in range(1, 38)))
put("lz.vcf", H + CTG + INFO + COLS + rec("t1", 9, "SVLEN=-2") + rec("t1", "010", "SVLEN=-2") + rec("t1", 30, "SVLEN=-2"))
put("tbipos.vcf", H + CTG + INFO + COLS + rec("t1", 5, "SVLEN=-2") + rec("t1", 600000000, "SVLEN=-2"))
put("tbiend.vcf", H + CTG + INFO + COLS + rec("t1", 5, "SVLEN=-2") + rec("t1", 10, "END=600000000;SVLEN=-2"))
put("csi38.vcf", H + INFO + COLS + rec("t1", 5, "SVLEN=-2") + rec("t1", 300000000000, "SVLEN=-2"))
put("csi32.vcf", H + "##contig=<ID=t1,length=1000>\n" + INFO + COLS + rec("t1", 5, "SVLEN=-2") + rec("t1", 5000000000, "SVLEN=-2"))
put("noff.vcf", INFO + COLS + rec("t1", 5, "SVLEN=-2") + rec("t1", 9, "SVLEN=-2"))
put("cfirst.vcf", "#a comment first\n" + H + CTG + INFO + COLS + rec("t1", 5, "SVLEN=-2") + rec("t1", 9, "SVLEN=-2"))
pad = "x" * 70000
put("biglen.vcf", H + '##contig=<ID=t1,Description="%s",length=5000000000>\n' % pad + '##contig=<ID=t2,length=6000000000,Description="%s">\n' % pad
    + INFO + COLS + rec("t1", 4, "SVLEN=-2") + rec("t1", 4500000000, "SVLEN=-2") + rec("t2", 5900000000, "SVLEN=-2"))
