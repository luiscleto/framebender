# Gemini, round 4

  ### Verdicts on M1–M10 (responses-3.md)
  • M1: AGREE — Making MALFORMED (including non-[A-Za-z]+ REF and blank
  lines) always stop eliminates unkeyed buffer flushes, preserves the non-
  stop ordering law's premises, and protects REF validation.
  • M2: DISAGREE
      • Reason: (1) Restating the ordering law's conclusion as "success
      implies the body is the stable sort by key within each CHROM run, runs
      in input order" drops grouped (at most one run per CHROM) from
      responses-2.md:87-88: an implementation that omits the ended-set check
      satisfies "within each CHROM run" while emitting split CHROM blocks
      violating VCFv4.3.txt` §1.6.1. (2) Requiring an UNSORTED event to name
      both lines ("the one that would come out of order and the one whose
      arrival caused the flush") fails on an end-of-input flush (no arriving
      line exists) and on a repeated-CHROM stop (no separate buffered out-of-
      order line exists).
      • Example: (1) Output [chr1:100, chr2:10, chr1:50] has three CHROM runs,
      each stably sorted by key and in input run order, satisfying M2's
      stated law while violating grouped. (2) With w = 100000, chr1:100,
      chr1:110000 (flushes 100), chr1:50 (buffered), then EOF: EOF flushes
      chr1:50 < 100, stopping with UNSORTED with no arriving trigger line.
      • Change to agree: Include grouped(body) in the law conclusion
      ("success implies the body is grouped by CHROM and is the stable sort
      by key within each CHROM, with CHROMs in input order"), and make the
      trigger/second line in UNSORTED events optional (None on an EOF flush;
      on a repeated-CHROM stop, carry the arriving repeated-CHROM line with
      None for the second line).
  • M3: AGREE — Line-initial >, contig name up to space/tab/CR/LF,
  whitespace-stripped sequence blocks, and skipping empty or duplicate names
  with their sequence blocks make FASTA parsing unambiguous.
  • M4: AGREE — Repairing missing LF or trailing lone CR on the final line
  before header/body and field splitting cleanly handles header-only and CRLF
  edge cases (treating LF as a line terminator so a normal trailing LF does
  not create a phantom blank line).
  • M5: AGREE — Defining stop stdout as all writes made prior to stopping,
  emitting the header immediately upon #CHROM, and making missing event
  fields optional resolves the failure-output conflicts.
  • M6: AGREE — Narrowing the preservation claim to byte-copying plus
  preserved allele/genotype indices and emitting POSSIBLY_STALE on
  CIGAR/HOMLEN/HOMSEQ/AA only when POS or allele bases change is accurate and
  sound.
  • M7: AGREE — Using unbounded Nat for POS and END without silent overflow
  and documenting the extension beyond VCF 4.3's 32-bit Integer is clean.
  • M8: AGREE — Framing padding around alleles that would otherwise be empty
  accurately covers simple indels, delins, multiallelics, and contig-start
  events.
  • M9: DISAGREE
      • Reason: Grouping outcomes 4–7 (BAD_END, NON_ACGTN, BAD_POS, ALT_DUP)
      with outcomes 1–2 (MALFORMED, OUT OF SCOPE) under "the other outcomes
      ￹need no reference" makes the sufficiency + soundness laws jointly false
       (unsatisfiable). Inresponses-2.md:25-388, Step 3 (UNKNOWN_CHROM, which
       always stops even under -c w) precedes Steps 4–7; therefore outcomes
       4–7 cannot be determined without a "known" contig answer from the
       reference.
       • Example: On chrX    0    .    A    G    .    PASS    ., the outcome is
UNKNOWN_CHROM (exit
      1 under -c w) if chrX is absent from the FASTA, and BAD_POS (passed
      through with exit 0 under -c w) if chrX is present. With no reference
      answer, the classifier cannot distinguish the two.
      • Change to agree: Split the zero-base cases: outcomes 1–2 (MALFORMED,
      OUT OF SCOPE) need no reference answer at all; outcome 3
      (UNKNOWN_CHROM) needs the "unknown" answer; outcomes 4–7 (BAD_END,
      NON_ACGTN, BAD_POS, ALT_DUP) need a "known" contig answer with 0 bases
      required (any window on that contig).
  • M10: AGREE — Documenting BAD_END under -c e and non-letter invalid ALT
  tokens as OUT OF SCOPE keeps the bcftools 1.24 differential contract
  accurate.
  ──────
  ### NEW Problems Introduced by responses-3.md

  1. M9 window sufficiency law is unsatisfiable for outcomes 4–7 (BAD_END,
  NON_ACGTN, BAD_POS, ALT_DUP) — Severity: blocker
      • Stating that outcomes other than NORMALIZED, REF_MISMATCH, and
      UNKNOWN_CHROM "need no reference" overlooks that Steps 4–7 come after
      Step 3 (UNKNOWN_CHROM) and therefore require confirming the contig
      exists in the FASTA (0 bases needed, "known" answer required), whereas
      only Steps 1–2 need no reference query (see M9 example).
  2. M2 weakens the ordering theorem by dropping grouped and over-constrains
  UNSORTED event fields — Severity: should fix
      • Replacing "grouped by CHROM" in the ordering law's conclusion with
      "within each CHROM run, runs in input order" permits repeated CHROM
      blocks (chr1, chr2, chr1) to satisfy the law, and requiring two lines
      in every UNSORTED event fails on EOF-triggered flushes and repeated-
      CHROM stops where no second line exists (see M2 examples).

