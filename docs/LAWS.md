# The laws

framebender's behaviour is specified by laws: statements in Bend that the proof checker verifies
for every possible input. This page explains them in plain terms. The Bend text is the
authority; each law below is named as it appears there.

## Two layers

- **Science layer**: `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`. What normalization means
  and what the tool writes for a whole file. These files mention no implementation, and they are
  what a domain expert reviews.
- **Implementation layer**: `protocol.bend`, `MACHINE.bend`, `bytes_enc.bend`. These say that
  the actual program writes exactly what the science layer defines. The code (`norm*.bend`) can be
  rewritten freely as long as this stays proven.

## Terms

- **Variant**: at position POS, the reference letters REF are replaced by one or more
  alternatives ALT. The same variant can often be written in several ways. In a repeat such as
  `TATATA`, deleting one `TA` gives the same sequence wherever the deletion is placed.
- **Change** (`haps`): the sequences you get by applying each alternative to the reference.
- **Valid** (`valid`): the record's REF really is the reference's letters at POS.
- **Normalized** (`normalized`, after Tan, Abecasis and Kang, *Bioinformatics* 2015):
  - left-aligned: moved as far left as possible while making the same change;
  - parsimonious: no letter can be dropped from the start or from the end of every allele.
- **`Tan.normal`**: the reference normalizer the laws are about (`tan.bend`).

## One variant

Each law assumes a valid input variant `v` on contig `seq`.

| law | in plain terms |
|---|---|
| `same_change` | The output makes exactly the same change as the input, with the alternatives in the same order. |
| `stays_valid` | The output still matches the reference. |
| `standard_form` | The output is left-aligned and parsimonious. |
| `unique` | Two valid, normalized variants that make the same change are identical. |
| `one_form` | Two inputs that make the same change give the same output. |
| `shortest` | No valid variant making the same change has fewer letters. |
| `normal_unchanged` | A variant already in standard form is returned unchanged. |
| `twice` | Normalizing twice gives the same result as normalizing once. |

`unique`, together with the first three, pins down the output completely: a reviewer does not need
to read `tan.bend`'s algorithm to know what it returns. For example:

```
law same_change:
  for seq: List<&2, B.Base>
  for v: B.Var
  for hv: {valid(seq, v) == True{} : Bool}
  {haps(seq, Tan.normal(seq, v)) == haps(seq, v) : List<&2, List<&2, B.Base>>}
```

## One line

`judge` gives each body line exactly one outcome. The checks run in this order:

1. MALFORMED: the line cannot be parsed as a record. Stops the run.
2. Out of scope: symbolic alleles (`<DEL>`, `<*>`), `*`, `.`, breakends. Passed through unchanged.
3. UNKNOWN_CHROM: the chromosome is not in the reference. Stops the run.
4. BAD_END, NON_ACGTN, BAD_POS, ALT_DUP, REF_MISMATCH. These stop under `-c e`; under `-c w` the
   line passes through with a warning:
   - BAD_END: INFO/END is inconsistent with POS and REF;
   - NON_ACGTN: an allele has letters outside ACGTN;
   - BAD_POS: POS 0;
   - ALT_DUP: a duplicate ALT;
   - REF_MISMATCH: REF does not match the reference.
5. Normalized: the record is rewritten as `Tan.normal` says.

`normalized_valid`: a record that gets the outcome "normalized" really is a valid variant, so the
laws above apply to it. Normalized records are written canonically:
- POS without leading zeros;
- REF and ALT in upper case;
- INFO/END updated when POS or the REF length changes.

Every other byte of the line is kept as it came.

## The whole file

`run` is the whole-file definition: a fold over the lines that writes the header (with two added
lines) and then the records through a sorting buffer.

| law | in plain terms |
|---|---|
| `sorted` | A successful run writes the header, then the records grouped by chromosome (in input order) and sorted by position within each; equal positions keep input order. |
| `grouped_in` | A successful run had each chromosome's records together in the input. |
| `no_unsorted` | Sorted input, where no record moves left by `-w` bases or more, never stops with UNSORTED. |
| `twice_run` | Running the tool on its own output succeeds and gives the same records. |

## The program

`machine` (in `MACHINE.bend`): the program is a state machine that receives the input in chunks and
asks for reference letters. However the VCF is split into chunks, the program's output, messages
and exit code equal `run` on the whole file. The law assumes the arguments parse and the reference
is a plain FASTA file (`P.Fasta.plain`). `usage` covers arguments that do not parse.

The program works on bytes, while the science layer reads text. `bytes_enc.bend` connects them:
each character is one byte, and the law assumes every character the driver passes is below 256,
which holds for anything read from a file. Each piece is at most 2^31 bytes (2 GiB). The driver
reads larger files in pieces.

## What the laws do not cover

The trusted driver (`main.bend`, `io64.c`) reads and writes the bytes, reads the reference through
the `.fai` index, and reports its own errors with exit code 2. For a VCF compressed with BGZF
(`bgzip`, the usual `.vcf.gz`), the VCF the law speaks of is the text its blocks decompress to:
the driver decompresses them with libdeflate and checks each block's CRC32 and length. Other gzip
files are refused.

The law `machine` assumes the driver hands the program the reference as `P.Fasta.plain` describes
it. That premise names exactly the FASTA files that `samtools faidx` 1.24 indexes and serves the way
the spec reads them: uniform line lengths, no spaces or control characters in sequence lines, and no
contig without letters. The 23 cases behind it, checked against samtools, are in
`test/plain_cases.bend`.

All the real bugs found in this project were in the driver, and three independent reviews of it
found them. See `NOTES.md`, "Driver review".
