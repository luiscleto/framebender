# Gemini, round 3 (same session; 5 min)

  ### Verdicts on Items in responses-2.md
  • Classification (replaces R7, R12, R13, S1 scope): DISAGREE
      • Reason: Step 2 (OUT OF SCOPE: REF or any ALT is not made only of
      letters [A-Za-z]+) tests REF as well as ALT. In VCFv4.3.txt` §1.6.1,
      REF must always be base letters (symbolic <...>, *, ., and breakends
      are valid only in ALT; even POS = 0 telomere breakends have REF = N),
      and bcftools-norm.txt:38 defines -c e|w to catch missing/bad REF (REF =
      .). Matching non-letter REF in Step 2 silently passes corrupt records
      (REF = ., REF = *, REF = 123) through with exit 0 under -c e (even on
      unknown contigs). Also, Step 4 (BAD_END) stops under -c e whereas
      bcftools 1.24 exits 0 ([run], line 11), which needs DOCUMENT for R21.
      • Example: chr1    10    .    .    A    .    PASS    . (missing REF) or
no_such_chr    10    .    .    A    .
      PASS    . hits Step 2 (OUT OF SCOPE) and passes through with exit 0 under
      -c e.
      • Change to agree: Require REF to be [A-Za-z]+ in Step 2 (so any non-
      [A-Za-z]+ REF is a problem rather than OUT OF SCOPE, e.g., move non-[A-
      Za-z]+ REF to MALFORMED or let Step 2 check REF is [A-Za-z]+ and some
      ALT is not [A-Za-z]+), and DOCUMENT both BAD_END and any non-VCF ALT
      punctuation (e.g. ALT = 123) that Step 2 treats as OUT OF SCOPE vs
      bcftools 1.24.
  • S1 (multiallelic): AGREE — Equal-length index-wise ALT laws, the POS = 1
  right-trim guard, and documenting bcftools norm -m- resolve all
  multiallelic issues.
  • S2 (END): AGREE — Validating END via BAD_END first and rewriting END iff
  POS or len(REF) changes makes END independent of allele casing and matches
  bcftools on valid END.
  • R1 (end-to-end law): DISAGREE
      • Reason: Narrowing FASTA contig-name parsing from "first whitespace"
      (responses-1.md) to "up to the first space or tab" breaks headers with
      no description (CR/LF is no longer a delimiter, so \n and sequence
      lines get swallowed into the contig name). Also, > must only start a
      header at start-of-file or immediately after LF (not mid-header
      description), an empty contig name > must be ignored on its first
      occurrence too (not "after the first"), and ignoring an empty/repeated
      header must skip its entire sequence block.
      • Example: On >chr1\nACGT\n (no spaces or tabs), text after > up to
      space/tab is "chr1\nACGT\n" with empty sequence; on >chr1 sub
      A>G\nACGT\n, splitting on mid-line > creates contig "G" with sequence
      ACGT.
      • Change to agree: Define a FASTA header line as > at byte 0 or
      immediately after LF; take the contig name up to the first space, tab,
      CR, or LF; take sequence lines up to the next line-initial > (stripping
      space, tab, CR, LF); and skip both header and sequence block whenever
      the contig name is empty or already seen.
  • R3/R4 (ordering): DISAGREE
      • Reason: (1) The law "if the input is grouped and sorted by POS and no
      record moves left by w or more, the run never stops with UNSORTED" is
      false under -c w when a MALFORMED line flushes a right-shifted record
      early. (2) Bullet 1 ("on a different CHROM than the buffered lines") is
      ill-defined when the buffer is empty mid-run—which occurs after a
      MALFORMED flush under -c w or after an immediate flush when key(b) + w
      <= inpos(current) (e.g., -w 1 on a 1-bp left shift)—either falsely
      tripping "already had a run earlier" on the same CHROM or missing chr1
      -> chr2 -> chr1.
      • Example: (1) Contig ACGT with -c w: chr1    1    .    ACG    AGG    .
PASS    . (inpos
      ￹= 1, right-trims to key = 3), then a blank MALFORMED line (flushes key
      = 1, right-trims to key = 3), then a blank MALFORMED line (flushes key
      ￹= 3), then chr1    2    .    C    T    .    PASS    . (inpos = 2, key =
      = 3), then chr1    2    .    C    T    .    PASS    . (inpos = 2, key =
2): input POS is
      sorted (1 <= 2) and left-moves are 0 < w, yet key = 2 < 3 stops with
      UNSORTED. (2) With -w 1, chr1    2    .    CA    A    .    PASS    .
(inpos = 2, key = 1)
      flushes immediately (1 + 1 <= 2), leaving the buffer empty before chr1
      ￺5    .    A    G    .    PASS    . arrives.
      5    .    A    G    .    PASS    . arrives.
      • Change to agree: Track current_chrom: Maybe<String> and seen_chroms
      explicitly as state variables rather than reading CHROM from the
      the hypothesis of the non-stop law.
      explicitly as state variables rather than reading CHROM from the
      (possibly empty) buffer, and add "and contains no MALFORMED lines" to
      the hypothesis of the non-stop law.
  • R8 (line endings): DISAGREE
      • Reason: Defining the EOF missing-LF / lone-CR repair only for "A body
      ￹line's terminator" leaves a header-only VCF whose #CHROM line is at EOF
      line's terminator" leaves a header-only VCF whose #CHROM line is at EOF
      with no LF (or ending in a lone CR) without a final LF, and leaves a
      trailing \r attached to #CHROM's last column header.
      • Example: Header-only file ##fileformat=VCFv4.
      ￺3\r\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\r (no trailing \n):
      3\r\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\r (no trailing \n):
      added header lines get \n, while #CHROM keeps \r in field 7 and has no
      final LF.
      • Change to agree: Apply the EOF terminator repair (no LF -> LF;
      trailing CR without LF -> CR LF) to the final line of the input before
      header/body classification and field splitting.
  • R9 (canonical text): AGREE — Restricting canonical rewriting to
  NORMALIZED records and scoping idempotence to the body resolves both the -c
  ￹w contradiction and header line growth.
  w contradiction and header line growth.
  • R10 (stale annotations): AGREE — Copying other fields byte-for-byte,
  documenting stale fields, and emitting non-fatal STALE_CIGAR (preferably
  only when POS or allele sequences change, not on case-only R9 edits) is
  clean.
  • R12 (stdout/stderr on failure): DISAGREE
      • Reason: (1) "stdout is exactly the whole lines the buffer rule had
      ￹written before the stopping line" contradicts R3/R4 bullet 1 on a
      written before the stopping line" contradicts R3/R4 bullet 1 on a
      repeated-CHROM stop ("flush the whole buffer first. If that CHROM
      already had a run earlier in the file, stop: UNSORTED"), where the
      previous CHROM's buffer is flushed upon reading the stopping line, not
      before it. (2) Stderr event fields (kind, CHROM, POS, input line
      number) are missing or non-numeric on missing-#CHROM stops and
      MALFORMED lines (blank line, < 2 fields, POS = abc).
      • Example: Input chr1:10, chr2:10 (buffered), chr1:20 (stopping line):
      R3/R4 flushes chr2:10 when chr1:20 arrives, whereas R12 says chr2:10 is
      not in stdout. And a blank MALFORMED line has no CHROM or POS.
      • Change to agree: State "stdout is exactly the whole lines the buffer
      rule writes prior to stopping", specify which record's coordinates
      populate an UNSORTED event (the buffered record with key < last_written,
      vs the arriving record on repeated CHROM), and make CHROM, POS, and
      line_number optional (or raw strings where applicable) for missing-
      #CHROM and MALFORMED events.
  • R14 (window sufficiency): AGREE — Requiring [POS, POS+len(REF)-1] union
  [max(1, final_POS - 1), POS+len(REF)-1] clipped to the contig fixes the
  right-trimming soundness bug (note final_POS applies only to NORMALIZED
  records).
  • R17 (wording): AGREE — Restricting the neighbouring-base prose to
  insertions/deletions and quoting tan2015.txt verbatim resolves the
  ambiguity.
  • R21 (comparison): AGREE — Checking exit codes, stopping lines, and bytes
  modulo named "htslib re-serialization" rules makes bcftools 1.24
  compatibility testable.
  ──────
  ### NEW Problems Introduced by responses-2.md

  1. R3/R4 non-stop law is false (unprovable) in the presence of MALFORMED
  lines under -c w — Severity: blocker
      • Flushing the buffer on a MALFORMED line under -c w (newly added in
      responses-2.md line 82) can write a right-trimmed record (inpos = 1 ->
      ￹key = 3) before an already-sorted subsequent record (inpos = 2, key =
       ￹2), causing UNSORTED even though input POS was sorted and no record
        moved left (see R3/R4 counterexample). Exclude MALFORMED lines from the
        non-stop law's premise.
  2. R1 FASTA header name delimiter narrowed to "space or tab" breaks
  standard FASTA files — Severity: blocker
      • Replacing "first whitespace" (responses-1.md) with "first space or
      ￹tab" (responses-2.md line 70) omits CR/LF, merging \n and sequence
       lines into the contig name whenever >contig has no description; mid-
       line > and first empty > also misparse (see R1 example).
  3. Classification Step 2 (not [A-Za-z]+) applied to REF masks
  corrupt/missing REF as OUT OF SCOPE — Severity: should fix
      • Newly checking REF with not [A-Za-z]+ in Step 2 causes REF = . or REF
      ￹= * to pass through with exit 0 under -c e (bypassing UNKNOWN_CHROM and
       problem checks), contrary toVCFv4.3.txt` §1.6.11 and
      bcftools-norm.txt:388.
  4. R3/R4 empty-buffer CHROM tracking and R12 repeated-CHROM flush /
  partial-event typing — Severity: should fix
      • Defining CHROM transitions relative to "the buffered lines" fails
      when the buffer empties mid-CHROM (MALFORMED flush or key + w <= inpos);
      R3/R4 bullet 1 flushing before checking repeated CHROM contradicts
      R12's "written before the stopping line"; and R12's (kind, CHROM, POS,
      ￹line) event tuple lacks optionality for missing-#CHROM and MALFORMED
       lines.
  5. Minor edge cases in R8, R10, R14, and BAD_END documentation — Severity:
  minor
      • R8: EOF missing-LF / lone-CR repair restricted to "body line" misses
      a header-only file ending in unterminated #CHROM or #CHROM...\r.
      • R10: Trigger STALE_CIGAR (exact key CIGAR) only when POS or allele
      bases change, not when R9 merely uppercases a>g or strips leading zeros
      from POS.
      • R14: State explicitly that final POS in the window formula applies
      only to NORMALIZED records (REF_MISMATCH needs only [POS, POS+len(REF)-
      ￺1] clipped to [1, clen], and outcomes 1–7 need 0 bases).
       • Classification Step 4: Mark BAD_END (exit 1 under -c e) as DOCUMENT
       sincebcftools 1.24 exits 0 on unmoved inconsistent END (line 11).

