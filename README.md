# framebender

A VCF normalizer written in [Bend 2](https://bend-lang.com), with a machine-checked proof that it
does what its specification says. It rewrites each variant in a VCF file into its one standard
form (left-aligned and as short as possible, as defined by Tan et al. 2015), the job
`bcftools norm -f` does, and gives the same records as bcftools on the whole GIAB HG002 genome.

It is a proof of concept for *law-driven development*: the behaviour is written down as laws that
an expert can review, and the Bend proof checker verifies that the program obeys every one. The
implementation can then be rewritten freely: a change that breaks a law fails the proof check.

## Install

You need [Bend 2](https://bend-lang.com) (2.0.39), clang, and
[samtools](https://www.htslib.org/) to index the reference.

framebender builds on four proven utility packages, which must sit next to it:

```
for r in framebender lawful-words lawful-arrays lawful-bytes lawful-fields; do
  git clone https://github.com/luiscleto/$r
done
cd framebender
bend main.bend -o framebender
```

## Run

```
samtools faidx ref.fa                      # once: writes ref.fa.fai
./framebender norm -f ref.fa in.vcf > out.vcf
```

- `-c w`: pass records whose REF does not match the reference through with a warning
  (default `-c e`: stop at the first one).
- `-w N`: how far (in bases) a record may move left; default 100000.
- Input and output are plain VCF. For `.vcf.gz`: `bgzip -dc in.vcf.gz | ./framebender norm -f ref.fa /dev/stdin`.

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
- The header gets two added lines with no date, so the output is reproducible.

Speed (wall clock, writing to a file, interleaved runs on the same machine):

| GIAB HG002 | bcftools | framebender |
|---|---|---|
| chr22 | 0.12–0.14 s | 0.12–0.16 s |
| whole genome (2.8 GB) | 8.5–8.6 s | 9.1–9.7 s |
| 20,739 indels moved to random positions | 0.08–0.09 s | 0.14–0.17 s |

On real data framebender keeps pace with bcftools. The first proven version stored text as
linked lists of characters, as Bend 2's `String` does, and took 590 s on the whole genome. The
current one works on bytes packed four to a word, using four packages written for it, each with
its own proven laws (`lawful-words`, `lawful-arrays`, `lawful-bytes`, `lawful-fields`). The laws
did not change in the rewrite; the proof was redone and the output is byte-identical. Records that
need rewriting are about twice as slow as in bcftools, because a few rare cases still take a slow
path through `String`.

## How it was made

An AI agent drafted the laws. Three reviewers from different model families (Claude, GPT and
Gemini, with Grok standing in once) reviewed them independently until all three agreed. Agents then
wrote the code and the proofs. Nobody with a bioinformatics background has reviewed the laws yet:
if you have one, the science files (`LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`) are the
place to start, and issues are welcome.

Every real bug in framebender was found by the reviewers in the small trusted layer that reads
files, never inside the laws. Proving the packages did find one: the word-at-a-time byte search
could report a wrong position in a case no test or genome comparison reached.
[`NOTES.md`](NOTES.md) is the full record: decisions, who caught what, where the proofs got hard,
and the measurements.

## Documentation

- [`docs/LAWS.md`](docs/LAWS.md): the laws in plain terms, and the trust boundary.
- [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md): building, checking the proofs, comparing with
  bcftools, and the file layout.

## License

MIT (see [`LICENSE`](LICENSE)).
