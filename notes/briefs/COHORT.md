# Cohort VCFs: brief for the cohort agent (phase G)

Goal: find why framebender loses its speed lead on multi-sample cohort VCFs, the files where
`bcftools norm` takes longest in real pipelines, and propose how to win it back. Speed first;
memory second (under 1 GB is acceptable to the owner, but 1 GB at one thread is a symptom).

## What the lead measured (main, c58d38c, `./build.sh`; machine otherwise idle)

Input: 1000 Genomes high-coverage phased panel, chr22, GRCh38: `data/kg/chr22.vcf.gz` (425 MiB),
`data/kg/chr22.vcf` (14.8 GB plain); 1,066,557 records, 3,202 samples (GT only), about 13.9 KB per
line, already normalized (framebender: 0 changed, 1462 out of scope: symbolic SVs). A first
800 MB slice: `data/kg/sub.vcf` (57,534 records). Reference `data/hg38.fa`.

| run | wall | user | peak RSS |
|---|---|---|---|
| whole chr22 `.vcf.gz` to a file, framebender | 64.4-64.8 s | | 1006-1015 MB |
| the same, bcftools 1.24 | 70.2 s | | 19 MB |
| whole chr22 plain to a file, framebender | 65.4 s | | 1008 MB |
| `sub.vcf` to /dev/null, default | 3.01 s | 3.65 s | 983 MB |
| `sub.vcf`, `--threads 1` / 4 / 32 | 3.35 / 3.18 / 3.10 s | 3.14 / 3.32 / 3.65 s | 783 / 830 / 1179 MB |
| `sub.vcf`, bcftools | 3.23 s | 3.13 s | 12 MB |
| GIAB HG002 whole genome (single sample, 2.8 GB), default | 1.25 s | 10.64 s | 334 MB |

So on cohort lines: (1) almost no parallelism (user time about equal to wall at every N; the
single-sample genome runs at about 8.5x); (2) per byte on one core no faster than bcftools
(about 270 MB/s, against 1.5 GB/s wall on the single-sample genome); (3) about 800 MB even at
one thread (44 MB on the single-sample genome). Outputs are correct (body identical to the input;
bcftools' records the same apart from the 236 symbolic alleles it shifts).

Suspects, unverified: the batch machine's pieces (3.5 MiB, so about 250 records each) going dirty
or failing `merge.ok` and falling back to the sequential machine; the fast path
(`norm_fast.bend`) refusing these lines (many INFO keys, long lines, `FORMAT`/samples), so every
line is decoded to `String` and judged by `norm_line.bend`; the line across a piece boundary;
the `bend` runtime's cost per byte on long lines; the reference windows. Find out, do not guess.

## Steps

1. **Find where the time and memory go.** Count, on `sub.vcf`: how many lines take the fast
   path and how many are decoded; how many batch tasks merge and how many fall back; time per
   stage. Instrument scratch copies of the generated C or of the Bend sources (never the tracked
   files), as the memory agent did (`notes/memory.md`, "Step 1"). Compare with a slice of the
   single-sample genome of the same size. Report a breakdown that adds up to the measured time.
2. **Options**, each with the measured gain and what it costs to make: driver only (trusted,
   driver review, no proofs); machine changes (outputs identical; which proofs must be redone,
   roughly how much); law changes are out of scope (the laws are approved; say so if one would
   be needed, and stop).
3. **Report and stop** with the breakdown and a recommended order. Do not implement beyond
   scratch prototypes until the lead answers.

## Rules

- Work in your own worktree (`../framebender-cohort`, branch `cohort`); `data` there links to the
  main checkout's `data`. Scratch in `data/tmp/cohort/`; do not write other files under `data/`.
- Fixed: the science layer, the contract (`MACHINE.bend`, `protocol.bend`, `bytes_enc.bend`), and
  `../lawful-*`.
- Every `bend` check through `test/bcheck.sh` (4 GB, at most two at once).
- **Timing and memory runs one at a time:** `flock data/tmp/bench.lock ...`, `nice -n 19`, a
  `timeout`, pinned (`taskset -c 0-15`), interleaved, ranges. Delete each output file before the
  next timed run; note that `cat` to a file on this btrfs disk is a reflink copy (0.3 s for
  14.8 GB), not a write. Wall, user, sys and peak RSS from Python's `resource.getrusage` (`time`
  is not installed). Prefer `sub.vcf` and smaller slices; the whole chr22 takes over a minute per
  run and writes 14.8 GB. Keep at least 8 GB of RAM free.
- `BEND_NO_TELEMETRY=1`. No commits, pushes or branch switches; the lead commits.
- Notes in `notes/cohort.md`.
