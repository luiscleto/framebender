# Drafter's responses, round 2

Round-2 answers: `reviews/claude-r2.md`, `reviews/gpt-r2.md`, `reviews/gemini-r2.md`. Items not listed
here were agreed by all three and stand as written in `responses-1.md`. Each item below replaces the
round-1 text of the same number. Facts about bcftools 1.24 marked [run] were checked by running it.

## Corrections to claims about bcftools

- bcftools does not flag duplicate ALTs: `CG  C,c` passes unchanged with exit 0 [run]; `realign`
  compares each ALT only with REF.
- bcftools does not correct END on a record it does not move: `GT  G  END=99` stays [run]. It rewrites
  END only when POS or the REF length changed.
- bcftools leaves records with a `<*>` allele unnormalized (gVCF): `AA  A,<*>` at a position where the
  deletion could move left stays put [run] (`realign` returns ERR_SYMBOLIC for symbolic alleles other
  than `<DEL...>`/`<DUP...>`).
- bcftools stops on a CHROM missing from the FASTA for every record, including symbolic ones [run].

## Classification (replaces R7, R12, R13, S1's scope sentence; answers Claude S1/R12, GPT R7/R12, Gemini R7/R12/R13)

The header is every line up to and including the column-header line: the first line whose first
tab-separated field is exactly `#CHROM`. No such line: exit 1. Every later line is a body line,
including lines starting with `#` (a contig name may start with `#`, VCF 4.3 §1.4.7). Each body line
gets the FIRST outcome that applies:

1. MALFORMED (problem): fewer than 8 tab-separated fields; empty CHROM; POS not a non-empty string of
   decimal digits; empty REF; empty ALT field; an empty allele in the ALT list (`A,,G`). A blank line
   is MALFORMED.
2. OUT OF SCOPE (passed through byte-identical, counted, whatever its CHROM): REF or any ALT is not made
   only of letters `[A-Za-z]+` (so `.`, `*`, `<...>` including `<*>`/`<NON_REF>`, breakends, telomeric
   breakends with POS 0). DOCUMENT: like bcftools, gVCF records with `<*>` are not normalized;
   unlike bcftools, an out-of-scope record on an unknown contig does not stop the run.
3. UNKNOWN_CHROM: CHROM not in the FASTA. Always stops the run, whatever `-c` says (bcftools too).
4. BAD_END (problem): INFO contains the key `END` (exact key) and it is not exactly one `END=<digits>`
   entry, or its value is not `POS + len(REF) - 1`.
5. NON_ACGTN (problem): REF or an ALT has a letter outside ACGTN (either case), e.g. IUPAC `R` in the VCF.
6. BAD_POS (problem): POS is 0.
7. ALT_DUP (problem): two alleles among REF and the ALTs are equal ignoring case (REF=ALT, or `G,g`).
   DOCUMENT: bcftools flags only ALT=REF.
8. REF_MISMATCH (problem): REF differs (ignoring case) from the reference at POS, including a REF that
   runs past the contig end.
9. NORMALIZED: everything else.

Problems: under `-c e` (default) the first one stops the run; under `-c w` the line is passed through
byte-identical with one stderr event. POS above 2^31-1 is accepted (DOCUMENT as the htslib/bcftools
64-bit extension of VCF 4.3's 32-bit Integer; answers GPT R19).

## S1 (multiallelic): answers GPT 25/26, Gemini S1, Claude S1

Laws compare ALT lists of equal length index by index; ALT count and order never change. The informal
algorithm description gets the guard: right-trimming stops when it would empty an allele at POS 1.
The laws themselves are declarative (`left_aligned && parsimonious` over all alleles) and already
cover POS 1: on reference `A`, `(1, A, CA,GA)` is normal. DOCUMENT (Claude N2): normalizing a
multiallelic record can give a different representation from splitting it first; recommend
`bcftools norm -m-` first when comparing call sets.

## S2 (END): answers all three

Only NORMALIZED records reach this point, so END, if present, is a single consistent integer (rule 4).
END is rewritten, as `newPOS + len(newREF) - 1` in decimal, exactly when POS or len(REF) changes, as
bcftools does; only the digits of that entry change. Since input END is validated, an already-normal
record's END is already consistent, so END correctness never depends on spelling (GPT 27). The
precise/imprecise distinction does not arise: an explicit-allele record whose END disagrees with its
REF is BAD_END.

## R1 (end-to-end law): answers Claude R1, Gemini R1

The top law holds for every split of the VCF bytes into chunks (empty chunks, a split between CR and
LF, inside a field). A truthful reference answer is: for a known contig, its length and the bases in
[a, b) clipped to the contig; for an unknown contig, "unknown". FASTA rules in `run`: text before the
first `>` is ignored; the name is the text after `>` up to the first space or tab; an empty name or a
repeated name is ignored after the first (as `samtools faidx`); spaces, tabs, CR and LF inside sequence
lines are removed; letters mapped by R5.

## R3/R4 (ordering): answers all three

Each body line except MALFORMED gets a key: its output POS if NORMALIZED, else its input POS. Lines go
through one buffer with this rule, which is part of `run`:
- When a line arrives on a different CHROM than the buffered lines, flush the whole buffer first. If
  that CHROM already had a run earlier in the file, stop: UNSORTED (exit 1, whatever `-c` says).
- Insert the line stably by key. Then flush, in order, every buffered line b with
  `key(b) + w <= inpos(current)`.
- A MALFORMED line passed through under `-c w` flushes the whole buffer and is written at its place; it
  does not end the CHROM run (the next line on the same CHROM must still not go before what was written).
- Whenever a line about to be written has a smaller key than the last line written on this CHROM, stop:
  UNSORTED.
- At end of input, flush everything.
`w >= 1` (`-w 0` is a usage error), default 100000. Law: success implies the body is grouped by CHROM
and sorted by key within each CHROM; and if the input is grouped and sorted by POS and no record moves
left by w or more, the run never stops with UNSORTED. DOCUMENT: bcftools does not stop on unsorted
input or on long moves; it writes unsorted output.

## R8 (line endings): answers GPT, Gemini, Claude N6

A body line's terminator is LF or CR LF; a line with no LF at end of file is given LF (a CR at end of
file with no LF becomes CR LF). This repair is the one exception to byte preservation (DOCUMENT; VCF
requires the final separator). The added header lines use the `#CHROM` line's terminator, LF if it has none.

## R9 (canonical text): answers Gemini R9, Claude R9

Applies only to NORMALIZED records. Idempotence is stated for the body only: running the tool on its
own output gives the same body; the header gains another pair of framebender lines (Claude N4, GPT 28).

## R10 (stale annotations): GPT disagrees

Kept as DOCUMENT, with the claim narrowed: fields other than POS, REF, ALT and END are copied byte for
byte, and the tool claims nothing about whether they remain true after a rewrite. INFO/CIGAR is the one
VCF-reserved INFO key defined relative to REF/ALT; a rewritten record carrying it gets a
`STALE_CIGAR` stderr event (not a problem, never stops the run). The genotype sentence is corrected:
GT and allele-indexed (Number=A/R/G) fields keep their meaning because ALT count and order are
kept; other FORMAT fields (DP, PS, ...) do not depend on representation. Not adopted: removing or
recomputing CIGAR (silently drops user data, and bcftools keeps it), or refusing to normalize records
with CIGAR (normalization would then depend on an annotation). If GPT still disagrees, this goes to the
project owner as an open decision.

## R12 (stdout/stderr on failure): answers all three

On a stop, stdout is exactly the whole lines the buffer rule had written before the stopping line,
and stderr ends with one error event. `run` returns stderr as a list of structured events (kind,
CHROM, POS, input line number) and the summary counts; one fixed rendering function turns them into
bytes. The summary is printed on success only.

## R14 (window sufficiency): Gemini and GPT showed the round-1 range was wrong

Accepted. Claude agreed with the round-1 range; Gemini and GPT gave counterexamples where a record
moves right: `(1,ACG,ACT)` on `ACG` vs `TCG`. New range: the window must contain the whole input REF
interval [POS, POS+len(REF)-1] and every base from one before the final POS (or the first base of the
contig) to the end of the input REF, clipped to the contig. Retries double the window and end with the
whole contig.

## R17 (wording): answers GPT R17, Claude

"An insertion or deletion is written with one unchanged neighbouring base. It is the base before the
event, unless there is none because the event starts at the first base of the contig; then it is the
base after. Substitutions need no neighbouring base." Tan et al.'s conditions are quoted verbatim.

## R21 (comparison): answers Claude R21

The differential corpus compares exit codes and the stopping line as well as bytes. A named class
"htslib re-serialization" covers bytes bcftools rewrites on every record (to be listed once observed).
