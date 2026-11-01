# framebender

A VCF normalizer written in [Bend 2](https://bend-lang.com), with a machine-checked proof that it
does what its specification says. It rewrites each variant in a VCF file into its one standard
form (left-aligned and as short as possible, as defined by Tan et al. 2015), the job
`bcftools norm -f` does, and gives the same records as bcftools on the whole GIAB HG002 genome.

It is a proof of concept for *law-driven development*: the behaviour is written down as laws that
an expert can review, and the Bend proof checker verifies that the program obeys every one. The
implementation can then be rewritten freely: a change that breaks a law fails the proof check.

## Install

You need [Bend 2](https://bend-lang.com) (2.0.39), clang,
[libdeflate](https://github.com/ebiggers/libdeflate) and [samtools](https://www.htslib.org/).
Writing an index (`-W`) also needs [htslib](https://www.htslib.org/) 1.24, which
`tools/build_htslib.sh` builds for you. Details are in
[`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md).

```
git clone https://github.com/luiscleto/framebender
cd framebender
tools/build_htslib.sh      # once: htslib 1.24, for -W
./build.sh
```

## Run

```
samtools faidx ref.fa                                    # once: indexes the reference
./framebender norm -f ref.fa in.vcf > out.vcf            # plain VCF to stdout
./framebender norm -f ref.fa -o out.vcf.gz in.vcf.gz     # compressed in and out
./framebender norm -f ref.fa -o out.vcf.gz -W in.vcf     # and an index, out.vcf.gz.csi
```

| option | what it does |
|---|---|
| `-f FILE` | the reference genome (FASTA), indexed with `samtools faidx` |
| `-c e` / `-c w` | on a REF that does not match the reference: stop (default) or warn and pass the record through |
| `-w N` | how far, in bases, a record may move left (default 1000, as bcftools) |
| `-m -any` | split records with two or more ALTs into one record per ALT, as bcftools; lines it cannot split safely are refused (see [USAGE](docs/USAGE.md)) |
| `--threads N` | how much runs in parallel (1 to 128, default 16); trades memory for speed, never changes the output |
| `-o FILE` | write to a file; a `.vcf.gz` or `.vcf.bgz` name is compressed |
| `-Oz`, `-Oz0`..`-Oz9`, `-Ov` | compress the output (default level 6, byte for byte as bgzip), or not |
| `-W`, `-W=tbi` | also write the output's index (`.csi`, or `.tbi`), as `bcftools index` / `tabix` |

The full reference, with every option's details and the differences from bcftools, is in
[`docs/USAGE.md`](docs/USAGE.md).

## What is guaranteed

Proven for every input, not tested on examples:

- Every rewritten variant makes the same change to the genome as before, still matches the
  reference, and is in the standard form.
- The standard form is unique: two records that describe the same change always come out
  identical, and no equivalent record is shorter.
- Records already in standard form are left alone, and running the tool on its own output changes
  nothing.
- Each line gets exactly one outcome (normalized, passed through, or a named error), in a fixed
  order of checks.
- The output is grouped by chromosome and sorted by position.
- However the input arrives, the program writes exactly what the specification defines.

The laws are in [`LAWS.bend`](LAWS.bend); [`docs/LAWS.md`](docs/LAWS.md) walks through them in
plain terms and says what they do not cover.

## Results against bcftools norm 1.24

Same records as bcftools on GIAB HG002 v4.2.1 (hg38; chr22 and the whole genome), on 20,739 of
its indels moved to random equivalent positions, and on the edge cases in `test/edge`. The
intentional differences: symbolic alleles such as `<DEL>` are passed through (bcftools realigns
them), some problems bcftools warns about stop the run, and the others listed in
[`docs/USAGE.md`](docs/USAGE.md#differences-from-bcftools-norm).

Speed, on a laptop (Intel i9-13950HX, runs pinned to its 8 performance cores, 16 hardware
threads; 30 GB of RAM, NVMe SSD; Linux, on AC power) with bcftools 1.24 and Bend 2.0.39: both
tools with `-c w`, writing to a file, interleaved, 3 rounds. bcftools normalizes on one core; the
usual way to use more is one job per chromosome, here 16 at a time on an indexed `.vcf.gz`, then
joined in order (`test/bcfsplit.sh`). It gave the same records as one run on every input.
Method and full tables: [`docs/BENCHMARK.md`](docs/BENCHMARK.md); `test/bench.sh` repeats it.

Wall time:

| input | bcftools, 1 core | framebender, 1 core | bcftools, per chromosome, 16 jobs | framebender, 16 |
|---|---|---|---|---|
| HG002 chr22 (35 MB) | 0.13 s | 0.11–0.12 s | — (one chromosome) | 0.07–0.09 s |
| HG002 chr22, 20,739 indels moved (14 MB) | 0.09–0.10 s | 0.11–0.13 s | — (one chromosome) | 0.08 s |
| HG002 whole genome, `.vcf` (2.8 GB) | 8.1–8.3 s | 6.5–7.0 s | 8.5–9.1 s (with `bgzip` and index first) | 1.8–2.2 s |
| HG002 whole genome, `.vcf.gz` (156 MB) | 8.3–8.4 s | 6.5–6.6 s | 4.6 s | 1.8–1.9 s |
| same, `-Oz -W` (compressed output and its index) | 14.6–15.2 s | 16.9–17.4 s | 4.6–4.7 s | 3.4–3.5 s |
| same, `-m -any` | 8.5–8.7 s | 9.1 s | 4.6–4.7 s | 2.4–2.5 s |
| 1000 Genomes chr22, `.vcf.gz` (3,202 samples, 14.8 GB of text) | 71–73 s | 12.0–12.6 s (1.5 cores; on one, 15.7–15.8 s) | 33–34 s (16 stretches of the chromosome) | 7.4–7.5 s |

Peak memory:

| input | bcftools, 1 core | framebender, 1 core | bcftools, per chromosome, 16 jobs | framebender, 16 |
|---|---|---|---|---|
| HG002 whole genome, `.vcf.gz` | 19–22 MB | 62–65 MB | 471–487 MB | 340–343 MB |
| same, `-Oz -W` | 29 MB | 80 MB | 480–485 MB | 366–371 MB |
| same, `-m -any` | 19–22 MB | 66 MB | 479–484 MB | 409–410 MB |
| 1000 Genomes chr22, `.vcf.gz` | 21 MB | 104–105 MB | 235–236 MB | 312–316 MB |

- On all cores framebender was the fastest on the large files: on the whole genome 4.5 times one
  bcftools run and 2.5 times the per-chromosome jobs, on the cohort file about 10 and 4.5 times.
  It needs no index and no join. It normalizes pieces of the file in parallel, and the proofs
  cover this parallel version: the output is the same at every `--threads`.
- On one core it was faster than bcftools on plain normalization (6.5 against 8.2 s on the whole
  genome, 16 against 72 s on the cohort file), and slower when writing compressed output (17
  against 15 s) or with `-m -any` (9.1 against 8.6 s). On the small files the two are within a
  few hundredths of a second.
- It uses more memory: 40–105 MB on one core and up to 410 MB at the default, against bcftools'
  12–30 MB a job. `--threads` trades memory for speed.
- Two kinds of input are much slower than in bcftools: records that need rewriting and carry an
  INFO/END (3.6 s against 0.1 s on the moved indels, each given an END), and `-m` on lines with
  many samples and many ALTs (7.7 s against 0.5 s on one line with 10,000 samples and 325 ALTs).
  See [`docs/USAGE.md`](docs/USAGE.md#speed-and-memory).

## What the proofs and reviews caught

Every real bug in framebender was found by the reviewers in the small trusted layer that reads
files, never inside the laws. The proofs found two that tests missed: the word-at-a-time byte
search could report a wrong position, and the parallel version's rule for joining pieces had a
case, unreachable on real files, where it would have named a record's chromosome wrongly.
[`NOTES.md`](NOTES.md) is the full record: decisions, who caught what, where the proofs got hard,
and the measurements.

## Documentation

- [`docs/USAGE.md`](docs/USAGE.md): every option in detail, and the differences from bcftools.
- [`docs/LAWS.md`](docs/LAWS.md): the laws in plain terms, and the trust boundary.
- [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md): building, checking the proofs, comparing with
  bcftools, and the file layout.

## License

MIT (see [`LICENSE`](LICENSE)).
