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
[libdeflate](https://github.com/ebiggers/libdeflate) (to read `.vcf.gz`),
[samtools](https://www.htslib.org/) to index the reference, and for `-W` (the output's index)
[htslib](https://www.htslib.org/) 1.24 built without libcurl: `tools/build_htslib.sh` builds it
into `~/.local/opt/htslib-1.24-nocurl`, where `build.sh` looks for it (or set
`PKG_CONFIG_PATH`; `FB_NO_HTSLIB=1 ./build.sh` builds without `-W`).

framebender builds on five proven utility packages, which Bend fetches from
[BendHub](https://hub.bend-lang.com) on the first build:

```
git clone https://github.com/luiscleto/framebender
cd framebender
tools/build_htslib.sh      # once: htslib 1.24 for -W
./build.sh
```

## Run

```
samtools faidx ref.fa                                # once: writes ref.fa.fai
./framebender norm -f ref.fa -o out.vcf.gz in.vcf.gz  # or a plain in.vcf
./framebender norm -f ref.fa -o out.vcf.gz -W in.vcf  # and its index, out.vcf.gz.csi
./framebender norm -f ref.fa in.vcf > out.vcf         # plain VCF to stdout
```

- `-c w`: pass records whose REF does not match the reference through with a warning
  (default `-c e`: stop at the first one).
- `-w N`: how far (in bases) a record may move left; default 1000, the same window as
  `bcftools norm --site-win`. A record that moves further stops the run with UNSORTED, naming
  both lines; re-run with a larger `-w`. (bcftools writes such a record out of order and exits
  successfully.) Larger windows hold more records in memory, which slows down files with many
  samples per line.
- `--threads N` (1 to 128): how much work runs at once, to fit the machine: N pieces of the VCF
  normalized in parallel by at most N of Bend's worker threads, N pieces read ahead, N reference
  reads in flight. It changes only speed and memory, never the output (law `threads`; the header
  does not record it). Without it: 16 pieces, one worker per CPU. A larger N needs more memory.
- `-o FILE`: write to FILE instead of stdout. A name ending in `.vcf.gz` gets bgzip-compressed
  VCF (BGZF, ready for `tabix`), as in bcftools.
- `-O z` (or `-Oz`, `-Oz0` to `-Oz9`): compress, also on stdout; default level 6, as bcftools and
  bgzip; `-Oz1` is faster for a larger file. The file is byte for byte what `bgzip` makes of the
  plain output, at every `--threads` (law `output`: these options never change the text).
- A `.vcf.gz` ends with BGZF's end-of-file block only when the run succeeded, so a run that stops
  never leaves a file that looks complete. `-o` refuses to overwrite an input, and a run that
  cannot read its inputs leaves an existing file as it was.
- `-W` (or `--write-index`): also write the output's index, `FILE.csi`; `-W=tbi` (or `-Wtbi`,
  `--write-index=tbi`) writes `FILE.tbi` instead. It is what `bcftools index` (or `tabix -p vcf`)
  writes for the same file under a `.vcf.gz` name, built while the file is written; byte for byte
  when their htslib compresses with libdeflate, as framebender's does. It needs a BGZF `-o`
  file (`error: -W needs a BGZF -o file` otherwise, before anything is read), and it never
  changes the output (laws `index` and `index_sink`). The index is written only when the run
  succeeds, after the file is complete; a file `bcftools index` or `tabix` would refuse (such as
  a passed-through POS with a leading zero, a position past 2^29 with `-W=tbi`, or, for CSI, an
  input that does not begin with `##fileformat=VCF`) ends the run with `error: cannot index
  FILE` and no index. `-W` first removes an old `FILE.csi` and `FILE.tbi`: htslib reads `.csi`
  before `.tbi`, so a stale one would silently answer region queries for the new file. For
  `out.vcf.gz`, htslib also reads `out.vcf.csi` before `out.vcf.gz.tbi`; `-W=tbi` does not remove
  that file (it may index `out.vcf`) and refuses to run while it exists (`error: cannot write
  out.vcf.gz.tbi (htslib would read out.vcf.csi first)`). A run without `-W` leaves an old index
  as it is, and htslib warns about it only when it is a second or more older than the file:
  remove it, or use `-W`.
- Input is plain VCF or bgzip-compressed `.vcf.gz` (a file that is cut short is refused).

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
The intentional differences:

- Symbolic alleles such as `<DEL>` are passed through; bcftools realigns them.
- Unsorted input, duplicate ALTs, inconsistent INFO/END and empty alleles stop the run; bcftools
  warns or carries on. A record framebender does not normalize passes through even on an unknown
  chromosome, where bcftools stops.
- Normalized records are written canonically: alleles in upper case, POS without leading zeros.
  Everything else on a line is kept byte for byte, including sample columns that bcftools pads
  (`1/0:1,1` for `GT:AD:PS` stays as is).
- The header gets two added lines with no date, so the output is reproducible. Its command line
  leaves out `--threads`, `-o`, `-O` and `-W`, which do not change the records.
- No BCF output, and no long forms of `-o`/`-O` (details in `docs/LAWS.md`).
- `-W` takes the eight documented forms (no abbreviated `--write`, no `##idx##` in the path), is
  refused for stdout or plain output before anything is read (bcftools leaves a header-only
  file), writes the index after the end-of-file block and only on success, and removes old
  indexes; bcftools saves it first and leaves stale ones.

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

The first proven version stored text as linked lists of characters, as Bend 2's `String` does,
and took 590 s on the whole genome. The current one works on bytes packed four to a word, using
five packages written for it, each with its own proven laws (`lawful-words`, `lawful-arrays`,
`lawful-bytes`, `lawful-fields`, and `lawful-halves` for the parallel map). The laws did not
change through any of the rewrites; only the proofs were redone.

## How it was made

An AI agent drafted the laws. Three reviewers from different model families (Claude, GPT and
Gemini, with Grok standing in once) reviewed them independently until all three agreed. Agents then
wrote the code and the proofs. Nobody with a bioinformatics background has reviewed the laws yet:
if you have one, the science files (`LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`) are the
place to start, and issues are welcome.

Every real bug in framebender was found by the reviewers in the small trusted layer that reads
files, never inside the laws. The proofs found two that tests missed: the word-at-a-time byte
search could report a wrong position, and the parallel version's rule for joining pieces had a
case, unreachable on real files, where it would have named a record's chromosome wrongly.
[`NOTES.md`](NOTES.md) is the full record: decisions, who caught what, where the proofs got hard,
and the measurements.

## Documentation

- [`docs/LAWS.md`](docs/LAWS.md): the laws in plain terms, and the trust boundary.
- [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md): building, checking the proofs, comparing with
  bcftools, and the file layout.

## License

MIT (see [`LICENSE`](LICENSE)).
