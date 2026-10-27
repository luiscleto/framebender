# Drafter's responses, round 3

Round-3 answers: `reviews/claude-r3.md`, `reviews/gpt-r3.md`, `reviews/gemini-r3.md`. Items not listed
were agreed by all three. Each item below amends `responses-2.md`.

New bcftools 1.24 facts [run]: a blank body line stops it ("VCF parse error", exit 255), and so does
a non-numeric POS (`c  x  .  C  T ...`), regardless of `-c`.

## M1. MALFORMED always stops (answers the MALFORMED-flush blocker raised by all three)

MALFORMED becomes like UNKNOWN_CHROM: it always stops the run, whatever `-c` says, as bcftools does
(it cannot parse such a line). So a MALFORMED line is never passed through, never enters the buffer and
never flushes it. The ordering law keeps its premises ("the input is grouped and sorted by POS and no
record moves left by w or more" implies no UNSORTED stop), and every body line written has a key.
A blank line, including a stray blank line at the end of the file, is MALFORMED (Claude N2; bcftools
also stops). Rejected alternative: Claude's "MALFORMED gets the key of the previous keyed line"; not
needed once such lines never reach the output.

MALFORMED now also includes a REF that is not `[A-Za-z]+` (`.`, `*`, `A1`): VCF requires REF to be bases
even when the ALTs are symbolic (Claude N4, Gemini). Rule 2 (OUT OF SCOPE) then reads: REF is letters
and at least one ALT is not `[A-Za-z]+`.

## M2. Ordering state (Gemini, GPT 19, Claude)

The buffer rule keeps three state variables independent of the buffer contents: the current CHROM
(none before the first body line), the set of CHROMs whose run has ended, and the last key written in
the current run. A body line whose CHROM differs from the current CHROM flushes the whole buffer; if its
CHROM is in the ended set, the run stops with UNSORTED; otherwise the old CHROM goes into the ended set
and the line's CHROM becomes current. An UNSORTED event names both lines involved: the one that would
come out of order and the one whose arrival caused the flush (Claude R12). The law is stated as
"success implies the body is the stable sort by key within each CHROM run, runs in input order".

## M3. FASTA parsing (Gemini R1)

A header line is a line starting with `>` (at the start of the file or right after LF). The name is
the text after `>` up to the first space, tab, CR or LF. The sequence is every following line up to the
next header line, with spaces, tabs, CR and LF removed. A header with an empty name, or a name already
seen, is skipped together with its whole sequence block. Text before the first header line is ignored.

## M4. Line endings at end of file (Gemini R8, Claude R8)

The end-of-file repair applies to the last line of the input, whatever it is, before the header/body
split and field splitting: no LF gives LF; a trailing CR with no LF gives CR LF. A CR before LF is
never part of the last field, in the header (`#CHROM ... INFO\r`) as in the body.

## M5. Stdout and stderr on a stop (GPT R12, Gemini R12)

Stdout on a stop is the concatenation of every stdout write made before the stop. The header (with
the two added lines) is written as soon as the `#CHROM` line has been read, before any body line;
body lines are written when the buffer rule flushes them. Event fields are optional where they do not
exist: the missing-`#CHROM` stop has no CHROM, POS or line; a MALFORMED event carries the line number
and the raw CHROM and POS text when present.

## M6. Annotations (GPT R10, Claude N5, Gemini, GPT 18)

The guarantee is narrowed to what is true: every field other than POS, REF, ALT and END is copied byte
for byte, and the ALT count and order are kept, so allele and genotype indices keep pointing at the same
alleles. No claim is made that any annotation stays true; the blanket sentences about Number=A/R/G and
other FORMAT fields are removed. A `POSSIBLY_STALE` event (never stops the run) is emitted when a
record's representation changes, meaning its POS or its allele sequences ignoring case (not a
case-only or leading-zero change), and its INFO has one of the reserved keys that describe the
alleles' sequence or breakpoints: CIGAR, HOMLEN, HOMSEQ, AA. The README lists them and says the list
is not exhaustive.

## M7. Integer range (GPT 17)

POS and END are unbounded natural numbers in framebender (Bend `Nat`): no overflow, no upper limit, and
a computed END is written in decimal whatever its size. DOCUMENT: VCF 4.3 Integer is signed 32-bit;
like htslib/bcftools (64-bit positions), framebender accepts and writes larger positions, which
strictly 32-bit readers may reject.

## M8. Wording (Claude R17)

Adopted: "When some allele would otherwise be empty, every allele gets one unchanged neighbouring base.
That base is the one before the event or, when there is no base before it (the event starts at the
first base of the contig), the one after it. Otherwise no neighbouring base is added."

## M9. Windows per outcome (Claude N6, Gemini)

The sufficiency law is per outcome: NORMALIZED needs the range in responses-2 R14; REF_MISMATCH needs
the input REF interval clipped to the contig; UNKNOWN_CHROM needs only the "unknown" answer; the other
outcomes need no reference.

## M10. Differences from bcftools to document (Gemini, Claude N3)

Added to the DOCUMENT list: BAD_END stops under `-c e` where bcftools exits 0; any ALT that is not
letters and is not valid VCF syntax (e.g. `123`) is OUT OF SCOPE here, while htslib may reject it.
