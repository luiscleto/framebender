# Benchmark: framebender against bcftools norm

The README's figures, with the method and the full tables. Measured on 2026-11-01.

## Setup

- **Machine:** a laptop with an Intel i9-13950HX (8 performance cores with 2 threads each, and 16
  efficiency cores), 30 GB of RAM and an NVMe SSD. Linux 7.2, power profile "balanced", on AC
  power: checked before every round.
- **Software:** bcftools 1.24 (htslib 1.24, with libdeflate), framebender from main at 6fb32c5 (the code of 4adf4a7),
  built with `./build.sh` (Bend 2.0.39, clang).
- **How each run was made** (`test/bench.sh`):
  - both tools with `-c w`, writing to a file on the SSD (deleted before each run, then a sync and
    2 s of rest);
  - pinned to the 16 hardware threads of the performance cores (`taskset -c 0-15`), under
    `nice -n 19`, a 600 s timeout and a 12 GB memory cap (`systemd-run --scope -p MemoryMax=12G
    -p MemorySwapMax=0`);
  - interleaved: each round runs every way once, and there are 3 rounds. The input and the
    reference are read once first, so no run starts with a cold cache. Nothing else was timed on
    the machine meanwhile.
- **Measures:** wall time; CPU time (user + system); peak resident memory (for one process, its
  own; for the per-chromosome pipeline, the largest sum over its processes, sampled every 10 ms).
  Every figure is the range over the 3 rounds.

### The ways compared

| way | what runs |
|---|---|
| bcftools, 1 core | `bcftools norm -c w -f REF -o OUT IN` (bcftools normalizes on one thread) |
| framebender, 1 core | `framebender norm -c w --threads 1 -f REF -o OUT IN` |
| bcftools per chromosome, 16 jobs | `test/bcfsplit.sh`: `bcftools norm -r CHROM` for each chromosome on the indexed `.vcf.gz`, 16 jobs at a time, then joined in order |
| framebender, 16 | `framebender norm -c w -f REF -o OUT IN` (default: 16 pieces at a time) |

The per-chromosome pipeline is the usual way to run bcftools on more cores. Its time counts
the whole pipeline: the jobs (22 on HG002, 16 at a time) and the join. The jobs write plain VCF, joined by
plain concatenation (the first job's header, then every job's records). For `.vcf.gz` output,
the jobs write `-Oz`, joined by `bcftools concat --naive` (no recompression), then indexed by
`bcftools index`.
- It needs a bgzipped, indexed input. An index usually comes with published files. Building one
  took 1.7–1.8 s for HG002 (`bcftools index --threads 16`; 2.2 s on one thread) and 9.1–9.6 s
  for the 1000 Genomes file. A plain `.vcf` must be compressed first:
  `bgzip -@16` took 2.1–2.6 s on HG002.
- Its output has exactly the records of a single bcftools run on every input here (same md5 of
  the record lines); only the header's command line differs.
- On a file with one chromosome it gives nothing. On the 1000 Genomes chr22 file it split the
  chromosome instead into 16 equal stretches, from the first record to the chromosome's end
  (`-r chr22:A-B --regions-overlap pos`, so each record is in the stretch holding its POS). This
  also gave exactly the single run's records. Where a record moved left across a stretch's
  start, it could come out of order; none did here.

### Inputs

| input | records | size |
|---|---|---|
| GIAB HG002 v4.2.1 (hg38), chr22 | 50,284 | 35 MB |
| HG002, 20,739 chr22 indels moved to random equivalent positions (`test/scramble.py`) | 20,739 | 14 MB |
| HG002, whole genome (chr1–22) | 4,048,342 | 2.8 GB; `.vcf.gz` 156 MB |
| 1000 Genomes high-coverage panel (3,202 samples), chr22 `.vcf.gz` | 1,066,557 | 446 MB; 14.8 GB of text |

The reference is UCSC hg38 (`chr22.fa` alone for the chr22 inputs).

## Results

Wall time / peak memory. `—`: one chromosome, nothing to split.

| input | bcftools, 1 core | framebender, 1 core | bcftools per chromosome, 16 jobs | framebender, 16 |
|---|---|---|---|---|
| HG002 chr22 | 0.13 s / 12 MB | 0.11–0.12 s / 40–42 MB | — | 0.07–0.09 s / 134–136 MB |
| scrambled indels | 0.09–0.10 s / 12 MB | 0.11–0.13 s / 62 MB | — | 0.08 s / 112–116 MB |
| HG002 whole genome `.vcf` | 8.1–8.3 s / 12–13 MB | 6.5–7.0 s / 62 MB | 8.5–9.1 s: `bgzip -@16` 2.1–2.6 s, `bcftools index` 1.7–1.8 s, then as below | 1.8–2.2 s / 335–342 MB |
| HG002 whole genome `.vcf.gz` | 8.3–8.4 s / 19–22 MB | 6.5–6.6 s / 62–65 MB | 4.6 s / 471–487 MB | 1.8–1.9 s / 340–343 MB |
| same, `-Oz -W` (compressed output and its index) | 14.6–15.2 s / 29 MB | 16.9–17.4 s / 80 MB | 4.6–4.7 s / 480–485 MB | 3.4–3.5 s / 366–371 MB |
| same, `-m -any` | 8.5–8.7 s / 19–22 MB | 9.1 s / 66 MB | 4.6–4.7 s / 479–484 MB | 2.4–2.5 s / 409–410 MB |
| 1000 Genomes chr22 `.vcf.gz` | 71.2–73.0 s / 21 MB | 12.0–12.6 s / 104–105 MB | 33.1–34.0 s / 235–236 MB (16 stretches) | 7.4–7.5 s / 312–316 MB |

CPU time, which shows how much of the machine each way used:

| input | bcftools, 1 core | framebender, 1 core | bcftools per chromosome | framebender, 16 |
|---|---|---|---|---|
| HG002 whole genome `.vcf.gz` | 8.2 s | 6.8–7.0 s | 30.9–31.4 s | 13.8 s |
| same, `-Oz -W` | 14.5–15.2 s | 18.0–18.5 s | 40.8–41.0 s | 38.2–38.5 s |
| same, `-m -any` | 8.3–8.4 s | 9.5 s | 31.7–31.9 s | 21.0–21.2 s |
| 1000 Genomes chr22 `.vcf.gz` | 70.0–71.7 s | 17.5–18.1 s | 214–220 s | 28.6–29.1 s |

### Where the per-chromosome pipeline's time goes

| input | jobs | join |
|---|---|---|
| HG002 whole genome, plain output | 2.1–2.2 s | 2.4 s (2.8 GB of text) |
| same, `-Oz -W` | 2.8 s | 1.8 s (block copy, then the index) |
| 1000 Genomes chr22, plain output | 15.1–15.9 s | 17.9–18.0 s (14.8 GB of text) |
| same, `-Oz -W` | 22.9–23.4 s | 9.3–9.6 s (block copy, then the index) |

### Other measurements

- **One CPU.** framebender `--threads 1` uses one core on plain input. On a `.vcf.gz` the input is
  decompressed alongside, so on the 1000 Genomes file it used 1.5 cores (17.5–18.1 s of CPU in
  12.0–12.6 s). Pinned to a single hardware thread (`taskset -c 2`), it took 15.7–15.8 s and
  103–104 MB there. On HG002 whole genome `.vcf` it took 6.5–6.8 s, with bcftools at 8.4–8.6 s.
- **bcftools `--threads 16`** compresses the output on more threads (it does not normalize on
  them). HG002 whole genome `-Oz -W`: 6.6–7.0 s, 44 MB.
- **1000 Genomes chr22, `-Oz -W`:** framebender 15.8–16.2 s / 333–335 MB; bcftools per stretch,
  16 jobs, 32.2–33.0 s / 241–242 MB; bcftools `--threads 16`
  63.9–66.2 s / 36 MB.
- **Known weak cases** (`docs/USAGE.md`), default threads, then `--threads 1`:
  - the scrambled indels with an INFO/END on every record (and its `##INFO` line): framebender
    3.6–3.8 s / 102–104 MB, `--threads 1` 6.9–7.1 s; bcftools 0.09–0.10 s / 12 MB. Without the
    header line bcftools stops at once ("Invalid BCF").
  - `-m -any` on one line with 325 ALTs and 10,000 samples (`GT:AD`): framebender 7.7 s /
    259–260 MB, `--threads 1` the same; bcftools 0.50–0.56 s / 89–91 MB.

## Repeating it

```
samtools faidx hg38.fa
bcftools index in.vcf.gz                      # for the per-chromosome pipeline
CPUS=0-15 MEMMAX=12G test/bench.sh hg38.fa in.vcf.gz 3
CPUS=0-15 MEMMAX=12G test/bench.sh hg38.fa in.vcf.gz 3 -- -Oz -W
REGIONS=16 CPUS=0-15 test/bench.sh chr22.fa cohort.chr22.vcf.gz 3
```

Each line of output is one run: way, wall time, CPU time, peak memory, exit code and the md5 of
the record lines. The output is written to `data/tmp/bench` in the checkout (`OUTDIR` to
change). Keep it off `/tmp` where that is a tmpfs (memory): there the small, write-heavy inputs
come out differently. `test/bcfsplit.sh` is the per-chromosome pipeline on its own.
