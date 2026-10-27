# framebender

A VCF normalizer, `framebender norm`, written in [Bend 2](https://bend-lang.com) as a trial of
law-driven development: the behaviour is stated as laws, and a proof checker verifies that the
program obeys every one of them. It does what `bcftools norm -f` does for sequence-resolved records:
left-align and trim indels and complex variants against a reference, so that the same variant always
has the same representation.

```
framebender norm -f ref.fa [-c e|w] [-w N] in.vcf > out.vcf
```

- `-f ref.fa`: the reference, with a `ref.fa.fai` index built by `samtools faidx` (1.24).
- `-c e` (default): stop at the first record whose REF does not match the reference (or with letters
  outside ACGTN, a duplicate allele, POS 0, or an inconsistent INFO/END). `-c w`: pass such records
  through unchanged with a warning on stderr.
- `-w N` (default 100000): how far back (in bases) the output buffer waits before writing a record;
  a record that moves left by `N` or more stops the run with UNSORTED.
- Plain VCF in and out (`bgzip -dc in.vcf.gz | framebender norm -f ref.fa /dev/stdin`).

## What is guaranteed

The laws come in two layers. The **science layer** (`LAWS.bend`, `types.bend`, `run.bend`,
`tan.bend`) mentions no code and is what an expert reviews; the **implementation layer**
(`protocol.bend`, `MACHINE.bend`) says that the program writes exactly what the science says.
In plain words:

- **Normal form** (Tan, Abecasis and Kang, *Bioinformatics* 2015): every record the tool rewrites
  makes the same change as before (same haplotypes, same alleles in the same order), is valid against
  the reference, is left-aligned and parsimonious, and is the unique such representation: two
  records making the same change always come out identical, and no representation is shorter.
  Multiallelic records are normalized as a whole.
- **Each line gets exactly one outcome**, in this order: MALFORMED (stops), out of scope (symbolic
  `<...>` including `<*>`, `*`, `.`, breakends: passed through), UNKNOWN_CHROM (stops), BAD_END,
  NON_ACGTN, BAD_POS, ALT_DUP, REF_MISMATCH (stop under `-c e`, warning under `-c w`), normalized.
- **Normalized records are written canonically** (POS without leading zeros, REF/ALT upper case,
  INFO/END updated when POS or the REF length changes); every other byte is kept, including CRLF
  line endings.
- **Sorted output**: a successful run writes the body grouped by CHROM (in input order) and sorted by
  position within each CHROM, ties in input order; sorted input with moves smaller than `-w` never
  stops with UNSORTED.
- **Idempotent**: running the tool on its own output changes no record.
- **The program**: for every way the input arrives (any split into pieces), the program's stdout,
  stderr messages and exit code are exactly those of the whole-file definition `run`.

What the laws do not cover (the trusted driver, `main.bend` and `io64.c`): reading and writing the
bytes, reading the reference through the `.fai` index, and the driver's own errors (exit code 2). The
law covers FASTA files that samtools faidx 1.24 indexes and serves exactly as the spec reads them
(`P.Fasta.plain` in `protocol.bend`; `test/plain_cases.bend`): in practice, any FASTA file with
uniform line lengths, no spaces or control characters in sequence lines, and no letterless contigs.

## Differences from bcftools norm 1.24

Records: identical on the GIAB HG002 whole-genome benchmark calls (4,048,342 records, hg38), on
20,739 scrambled indels, and on the edge cases in `test/edge`, except where noted here
(`test/compare.sh ref.fa in.vcf` runs both).
- Symbolic `<DEL>`/`<DUP>` records are passed through (bcftools realigns them).
- Already-normal records with lower-case alleles or leading zeros in POS are written canonically
  (bcftools keeps them); bases taken from a soft-masked reference are written in upper case.
- framebender stops (exit 1) on unsorted input, a CHROM that comes back, moves of `-w` or more,
  inconsistent INFO/END, duplicate ALTs and empty alleles; bcftools warns or continues.
- An out-of-scope record on an unknown contig passes; bcftools stops.
- Sample columns are kept as written; htslib pads one with fewer values than FORMAT lists
  (`GT:AD:PS` with `1/0:1,1` becomes `1/0:1,1:.`).
- The two added header lines carry no date, so the output is reproducible; bcftools also re-serializes
  the header through htslib (e.g. adds `##FILTER=<ID=PASS,...>`).

## Performance

GIAB HG002, `-c w`, 32 threads (details and history in `NOTES.md`, Q5):

| input | bcftools norm 1.24 | framebender |
|---|---|---|
| chr22 (50,284 records, 35 MB) | 0.08 s | 4.7 s |
| whole genome (4,048,342 records, 2.8 GB), to a file | 7.4 s | 595 s |

framebender is far slower: text is processed as linked lists of characters. The implementation is
free to change as long as every law stays proven, which is how it went from 31.7 s to 4.7 s on chr22
with byte-identical output.

## Building and checking

Needs Bend 2 (`bend`) and clang. `bend main.bend -o framebender` builds the binary.
`./check.sh` checks the examples, then every proof twice: with `bend` and with Bend's Lean-proven
kernel (`--verdict`).

## Files

- `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`: the science layer (definitions and laws).
- `protocol.bend`, `MACHINE.bend`: the implementation contract.
- `norm.bend`, `norm_line.bend`: the program (a state machine); `main.bend`, `io64.c`: the driver.
- `PROOF.bend`, `proof_*.bend`: the proofs. `examples.bend`: concrete cases checked by evaluation.
- `reviews/`: the law reviews by three independent models (Claude, GPT, Gemini; Grok stood in once).
- `NOTES.md`: decisions, review history, where proofs got hard, measurements.

## License

MIT (see `LICENSE`).
