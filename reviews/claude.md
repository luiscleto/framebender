(Claude reviewer: fresh general-purpose agent, same prompt. Full report kept in the session; summary of findings by number.)
1 blocker: no top-level law wires parts together (contig choice by CHROM, FASTA parsing, unknown CHROM, header/body split, Entry construction, retry loop). of_fasta comment says "letter" but maps any char.
2 blocker: small_moves forbids right moves, but left-trimming moves POS right (TC/TG at 2 -> C/G at 3), so in_order premise fails on most real files.
3 should fix: in_order allows reordering CHROM blocks and unstable ties; require stable sort within CHROM runs, CHROM order kept.
4 should fix: multiallelic pass-through misses Tan's main case (37.2% of multiallelic indels need normalization); bcftools norm -f normalizes them.
5 should fix: VCF 4.3 1.6.1 says IUPAC in reference -> alphabetically first base (R->A); types.bend reads N.
6 should fix/minor: N==N lets records slide through N gaps (chr1 9000 NN N -> pos 1).
7 should fix: kept_normal keeps lowercase/leading zeros while rewritten upper-cases: same variant, two texts. Merge into one law via Rec.rebuild.
8 should fix: moves >= w give unsorted output; sort whole CHROM or fail.
9 minor: "header lines never parse" false (#x\t1\t.\tA\tG...). Return None for '#' lines.
10 minor: INFO/END records with base alleles never normalized; stale position-dependent fields not documented.
11 minor: header law: no non-## line -> appended at end; cmd with \n/\t; CRLF.
12 minor: CRLF unspecified.
13 minor: Tan quotes in comments not verbatim; position-1 departure from Tan's "alleles end differently" should be documented.
14 should fix: bcftools compatibility not checkable; keep differential corpus and documented differences.
15 minor: high mismatch rate silently passes input through; summary/exit code unspecified.
Verdict on (d): no law false; normalized form unique and shortest.
