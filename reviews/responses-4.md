# Drafter's responses, round 4

Round-4 answers: `reviews/claude-r4.md`, `reviews/gpt-r4.md`, `reviews/gemini-r4.md`. All other items
(M1, M3, M5-M8, M10) were agreed by all three. Each change below is the one the reviewer named.

New bcftools 1.24 facts [run]: a line with 7 or 5 fields stops it ("VCF parse error", exit 255),
matching M1. An empty allele (`C  T,,A`) is reported as "Non-ACGTN alternate allele ... '.'", which
stops under `-c e` but would only warn under `-c w`; framebender always stops (MALFORMED). DOCUMENT.

## P1. Window answers per outcome (amends M9; GPT and Gemini, blocker)

Adopted as asked. MALFORMED and OUT OF SCOPE need no reference answer. UNKNOWN_CHROM needs the
"unknown" answer. BAD_END, NON_ACGTN, BAD_POS and ALT_DUP need a "known contig" answer (contig length,
zero bases). REF_MISMATCH needs the input REF interval clipped to the contig. NORMALIZED needs the range
of responses-2 R14.

## P2. Ordering law and UNSORTED events (amends M2; Gemini)

The law's conclusion: success implies the body is grouped by CHROM (each CHROM in one run), CHROMs in
input order, and within each CHROM the stable sort by key. An UNSORTED event carries the line that would
come out of order and, optionally, the line whose arrival caused the flush: none for the end-of-input
flush. A repeated-CHROM stop carries the arriving line only.

## P3. What a line is (amends M4; Claude)

Adopted as asked: a line ends just after each LF. If the input does not end with LF, the remaining
bytes form the last line and get the repair (LF added; a trailing CR becomes CR LF). An empty remainder
is not a line, so a file ending in LF has no blank last line, and a 0-byte input has no lines and stops
on the missing `#CHROM`.

## P4. Order of steps for each body line (new; Claude N1)

Adopted as asked: (a) classify the line; (b) if the outcome stops the run (MALFORMED, UNKNOWN_CHROM, or
a problem under `-c e`), stop without flushing; (c) otherwise, if the CHROM changed, flush the whole
buffer, and stop with UNSORTED if this CHROM's run already ended; (d) insert the line and apply the
flush rule. At end of input, flush everything.
