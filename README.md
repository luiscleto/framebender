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
| `-m -any` | split records with two or more ALTs into one record per ALT, as bcftools; a line it cannot split safely is refused (it stops the run under `-c e`); memory grows with the records a line makes and with the file; `--multi-overlaps .` marks the other ALTs' copies unknown |
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

Same records on GIAB HG002 v4.2.1 (hg38): chr22 (50,284 records), the whole genome (4,048,342
records), 20,739 indels moved to random equivalent positions, and the edge cases in `test/edge`.
The main intentional differences: symbolic alleles such as `<DEL>` are passed through
(bcftools realigns them), and some problems that bcftools warns about stop the run. The full list
is in [`docs/USAGE.md`](docs/USAGE.md#differences-from-bcftools-norm).

Speed, on one sample (GIAB HG002) and on a cohort of 3,202 (the 1000 Genomes high-coverage
panel, chr22: 1,066,557 records of about 14 KB each, 14.8 GB uncompressed):

| input | bcftools | framebender |
|---|---|---|
| HG002 chr22 | 0.11–0.12 s | 0.06 s |
| HG002 whole genome (2.8 GB) | 8.0–8.1 s | 1.8 s |
| HG002 whole genome, `.vcf.gz` | 7.9–8.0 s | 1.8 s |
| HG002, 20,739 indels moved to random positions | 0.07–0.08 s | 0.12–0.13 s |
| 1000 Genomes chr22, first 800 MB | 3.5–3.7 s | 0.29–0.30 s |
| 1000 Genomes chr22, `.vcf.gz` (425 MiB) | 69.8 s | 6.9 s |
| HG002 chr22, `-Oz -W` (with its index) | 0.13–0.14 s | 0.09–0.10 s |
| HG002 whole genome, `-Oz -W` (with its index) | 6.5–6.6 s | 3.4–3.6 s |
| HG002 whole genome, `-m -any` (47,781 records split) | 8.1–8.2 s | 2.4–2.5 s |

framebender reads the file in pieces and normalizes 16 at a time in parallel; the proof covers
the parallel version, which gives byte-for-byte the output of the sequential one. The `-W` rows write a
compressed file and its CSI index (bcftools with `--threads 16`, both on 16 CPUs; framebender's
index is byte for byte bcftools index's of the same file, both with libdeflate). A file where
nearly every record needs rewriting is still slower than bcftools. framebender uses more memory,
which `--threads` trades against speed (HG002 whole genome; the output is identical at every
setting):

| | time | peak memory |
|---|---|---|
| bcftools | 8.0–8.2 s | 11–12 MB |
| framebender (default: 16 pieces at a time) | 1.8 s | 330 MB |
| `--threads 8` | 2.1 s | 205 MB |
| `--threads 4` | 2.7 s | 130 MB |
| `--threads 1` | 6.0 s | 44–48 MB |

On the 1000 Genomes file: bcftools 18 MB, framebender 310 MB (`--threads 1`: 100 MB, 11.4–12.1 s).

Writing compressed `.vcf.gz` (HG002 whole genome; the same 150 MB file from both tools):

| | time | peak memory |
|---|---|---|
| `bcftools norm -Oz` | 14.2–14.3 s | 11 MB |
| `bcftools norm -Oz --threads 16` | 6.2–6.3 s | 17 MB |
| framebender `-Oz` | 2.9 s | 345 MB |
| framebender `-Oz1` (a 253 MB file) | 2.1 s | 345 MB |
| framebender `--threads 1 -Oz` | 14.4–14.7 s | 46 MB |

On the 1000 Genomes file, `.vcf.gz` in and out: bcftools `-Oz --threads 16` 65 s, framebender
`-Oz` 14 s.

How it was measured: a laptop with an Intel i9-13950HX (8 performance cores with 2 threads each,
16 efficiency cores), 30 GB of RAM and an NVMe SSD, on Linux; bcftools 1.24, Bend 2.0.39. Both
tools ran with `-c w`, writing to a file deleted before each run, pinned to the performance cores
(`taskset -c 0-15`, which removes about 3 s of run-to-run noise on the whole genome), one at a
time and interleaved, three rounds (two on the whole 1000 Genomes file and for compressed output,
bcftools once on the 1000 Genomes file). Times are wall clock, memory is peak resident size.
framebender's output was the same in every run.
`test/bench.sh ref.fa in.vcf` repeats the comparison on any file.

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
