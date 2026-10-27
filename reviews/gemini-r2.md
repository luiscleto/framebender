# Gemini, round 2 (same session; 8 min)

  ### Verdicts on S1–S3 and R1–R21 (responses-1.md)

  • S1: AGREE — Generalizing Var, apply, left_aligned, and parsimonious
  simultaneously across all alleles matches tan2015.txt:45-70 and preserves
  uniqueness and shortest (ensure the algorithm stops right-trimming at pos
  == 1 when any allele has length 1, and enforce pairwise-distinct ALTs in
  R12/R13).
  • S2: DISAGREE
      • Reason: (1) Updating INFO/END only "when a record is rewritten"
      leaves wrong or leading-zero END untouched on records whose POS/REF/ALT
      are already canonical, while updating END on records that differed only
      by lowercase alleles—breaking R9 canonicality and diverging from
      bcftools 1.24 norm -f (which recomputes END via rlen even when unmoved).
      (2) Behavior on non-integer or malformed END (e.g., END=., END=abc,
      bare END, END=1,2) is unspecified.
      • Example: Contig ACGT; chr1    1    .    ACG    A    .    PASS    END=99
keeps bogus END=99
      (or END=03), whereas chr1    1    .    acg    a    .    PASS    END=99
becomes chr1    1    .    ACG
      A    .    PASS    END=3. And chr1    2    .    CA    A    .    PASS
END=foo on ACA rewrites
      alleles while leaving invalid END=foo.
      • Change to agree: On every valid normalized record carrying INFO/END,
      set END to decimal newPOS + len(newREF) - 1 without leading zeros
      (whether or not POS/REF/ALT changed), and classify any explicit-allele
      record whose INFO/END is not a positive decimal integer as a problem in
      R12.
  • S3: AGREE — Keeping symbolic <...>, breakends, any *-containing record,
  and . out of scope (and documenting <DEL>/<DUP>) is clean once separated
  unambiguously from R12's NON_ACGTN (see R12).
  • R1: AGREE — Pure Norm.step verified against whole-file run(fasta, vcf,
  opts) closes the glue gap (ensure reference replies report missing contigs +
  contig length Maybe<(clen, bytes)>, strip spaces/tabs in FASTA sequence
  lines, and fix the typo citing R6 instead of R5).
  • R2: AGREE — Allowing arbitrary rightward moves (prefix trimming) fixes
  small_moves.
  • R3: AGREE — Stable sort by output POS within each maximal contiguous
  CHROM run, keeping CHROM runs and equal-POS ties in input order, fixes
  in_order and kept_all.
  • R4: DISAGREE
      • Reason: (1) Stopping "when a record would have to be written before
      one already written" leaves when records are written unspecified: two
      valid implementations can flush at different times and disagree on
      whether run(fasta, vcf, opts) exits 0 or non-zero on unsorted inputs or
      shifts >= w, violating R1's exact (stdout, stderr, exit) law. (2) With
      -w user-settable, -w 0 makes "no record moves left by w or more" fail
      on every unmoved SNP (0 >= 0). (3) Because R3 only sorts within each
      maximal contiguous CHROM run (dropping grouped), split blocks chr1 ...
      chr2 ... chr1 succeed while emitting ungrouped/unsorted VCF
      (VCFv4.3.txt` §1.6.1), contradicting "success implies sorted output".
      (4) Aborting on out-of-window shifts differs from bcftools 1.24 norm -f
      (which warns and continues) and needs DOCUMENT.
      • Example: With -w 0, sorted input chr1    10    .    A    G    .    PASS
. has left-move
      0 >= w, so R4 does not guarantee success. On chr1:100, chr2:10, chr1:50,
      the run exits 0 with chr1:50 after chr1:100.
      • Change to agree: Specify the exact deterministic flush rule inside
      run (e.g., maintain a min-heap per contiguous CHROM run, flushing b on
      CHROM change or when outpos(b) + w <= inpos(cur) with w >= 1, or
      outpos(b) + w < inpos(cur) allowing w >= 0 for left-moves <= w,
      stopping with exit 1 iff a newly flushed/emitted record has outpos <
      last_written_outpos on that CHROM run); qualify "sorted output" as
      sorted within each contiguous CHROM run (or fail on repeated CHROM
      runs); and DOCUMENT the non-zero exit vs bcftools.
  • R5: AGREE — Uppercasing FASTA bases and mapping R,M,W,D,H,V -> A, Y,S,B -
  > C, K -> G matches VCFv4.3.txt` §1.6.1 and bcftools replace_iupac_codes.
  • R6: AGREE — Treating N as a literal symbol matches tan2015.txt and
  bcftools, and documenting it resolves the concern.
  • R7: DISAGREE
      • Reason: (1) Matching "the first line starting with #CHROM" matches a
      meta/comment line like #CHROMOSOME_MAP=... instead of requiring the
      first tab-delimited field to equal "#CHROM". (2) Passing through body
      lines starting with # ("never a record") leaves their output position
      undefined under R3's buffered sort and can split a single CHROM run
      into two separate runs that fail to sort across the # line (and
      VCFv4.3.txt` §1.4–1.6 forbids comments after #CHROM).
      • Example: Body lines chr1    100    .    A    G    ..., #comment, chr1
102    .    CAA    CA    .
      .. (where line 3 left-aligns to POS=50): #comment has no CHROM or POS,
      either splitting chr1 so 100 precedes 50 or floating arbitrarily
      relative to buffered records.
      • Change to agree: Define the #CHROM header line by  first tab field ==
      "#CHROM" (i.e. #CHROM followed by \t or line terminator), and classify
      #... lines after #CHROM as a problem in R12 (or flush/attach them
      without breaking the current CHROM run, with an explicit rule in run).
  • R8: DISAGREE
      • Reason: Preserving an empty terminator when (a) #CHROM is the final
      line with no newline, or (b) a final body line with no newline is
      sorted before an earlier record that moved right (or before any
      buffered record), concatenates two output lines onto one physical line
      without a newline separator (and VCFv4.3.txt` §1.6 requires the last
      line to end with a line separator).
      • Example: Header-only input ##fileformat=VCFv4.
      3\n#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO (no trailing \n):
      using #CHROM's empty terminator emits ##framebender_normVersion=...
      ##framebender_normCommand=...#CHROM... on one line. Likewise, chr1    1
.
      ACG    AGG    .    PASS    .\n (moves right to POS=3) followed by
unterminated chr1
      2    .    C    T    .    PASS    . emits chr1    2    ...PASS    .chr1
3    ...PASS    .\n.
      • Change to agree: Default a missing terminator on #CHROM to \n for
      added header lines, and terminate every non-final emitted output line
      (or every emitted line, defaulting missing input EOF newline to \n).
  • R9: DISAGREE
      • Reason: (1) "Every in-scope record that passes the reference check"
      includes records that pass the reference check but fail ALT_DUP (e.g.,
      REF == ALT or duplicate ALTs), contradicting R12's rule that under -c w
      every problem line is passed through byte-identical. (2) "A record
      whose POS/REF/ALT text is already canonical and normal is byte-
      identical" conflicts with canonicalizing INFO/END under S2.
      • Example: On contig A at pos 10, chr1    010    .    a    a    .    PASS
. with -c w
      must come out 010    .    a    a under R12, but 10    .    A    A under
R9.
      • Change to agree: Restrict R9 to records classified as normalized
      (passing all validity checks, not just the reference check), and state
      that a normalized record is byte-identical iff its POS, REF, ALTs (and
      integer INFO/END, if present) are already normal and canonically
      formatted.
  • R10: AGREE — Documenting stale alignment-dependent INFO tags (CIGAR,
  HOMSEQ) while preserving allele-indexed FORMAT/genotype fields matches
  bcftools 1.24 norm -f.
  • R11: AGREE — Record-local handling of spanning * alleles matches bcftools
  1.24 norm -f and is properly marked DOCUMENT.
  • R12: DISAGREE
      • Reason:
          1. Overlap & missing precedence with S3: Every S3 ALT (<DEL>, G,*,
          G,<*>, ]13:123456]T, .A, .) has characters outside ACGTN, colliding
          with NON_ACGTN; and valid VCF 4.3 telomeric breakends (POS = 0 or
          POS = clen + 1; VCFv4.3.txt` §5.4.5) hit POS 0 / past-contig-end
          and abort under -c e.
          2. Incomplete partition: Body lines with < 8 fields, non-decimal
          POS (abc, -1), empty REF/ALT, or empty alleles in A,,G fall into
          none of the three "exhaustive" outcomes; and -c w lists no warning
          code for POS 0 (or malformed lines).
          3. Missing multiallelic ALT_DUP: Omits duplicate ALTs (ALT_i ==
          ALT_j, case-insensitive).
          4. Broken -c e stdout claim: "stdout is then a prefix of what a
          successful run would write" is undefined on inputs where no
          successful run exists, and false relative to -c w -w ∞ when a post-
          error record would have sorted before an already-flushed record.
      • Example: Valid VCF 4.3 telomere breakend 1    0    bnd_X    N    .
      13:123457[    6    PASS    SVTYPE=BND` ([`VCFv4.3.txt) or gVCF site 1
10    .    A    G,<*>    .
      PASS    .collides withPOS 0/NON_ACGTNand exits 1 under-c e`.
      • Change to agree: Define an explicit, total decision tree over body
      lines: (1) < 8 fields, empty REF/ALT/allele, or non-uint POS -> problem
      (MALFORMED_RECORD); (2) check CHROM in FASTA -> UNKNOWN_CHROM (always
      exit 1, documenting <ctg> assembly contigs); (3) if REF is ACGTN+ and
      ALT is . or any comma-separated ALT matches VCF 4.3 symbolic <...>, *,
      or breakend syntax while all remaining ALTs are ACGTN+ -> out of scope
      (skipping POS = 0/clen + 1 and REF check on breakends, or specify exact
      bcftools parity); (4) otherwise check POS == 0 (BAD_POS), non-ACGTN in
      REF/ALT (NON_ACGTN), any duplicate in REF <> ALTs case-insensitively
      (ALT_DUP), bad INFO/END, and REF vs FASTA (REF_MISMATCH); (5) drop the
      "prefix of a successful run" phrasing and define -c e stdout directly
      as the bytes flushed by the deterministic buffer prior to the stopping
      line.
  • R13: DISAGREE
      • Reason: Restricting ALT_DUP to ALT == REF misses duplicate alternate
      alleles (ALT_i == ALT_j for i != j, case-insensitive) newly introduced
      by multiallelic scope S1, which VCFv4.3.txt` §7.2 forbids and bcftools
      1.24 flags as ERR_DUP_ALLELE.
      • Example: chr1    10    .    AC    A,a    .    PASS    . passes R13 as
written and
      normalizes via R9 to invalid VCF chr1    10    .    AC    A,A.
      • Change to agree: Define ALT_DUP as any case-insensitive duplicate
      across the combined list REF <> ALTs.
  • R14: DISAGREE
      • Reason: Introduces an unsatisfiable (false) law. When left-trimming
      moves a variant right by >= 2 bases (final_POS >= initial_POS + 2), the
      window "from one base before its final POS to the end of its REF"
      ([final_POS - 1, initial_POS + len(REF) - 1]) omits the leading bases
      of REF at [initial_POS, final_POS - 2]. Without reading those bases,
      Norm.line_in cannot tell whether REF matches the reference contig, so
      no implementation can satisfy both R14's sufficiency law and window
      soundness.
      • Example: Input chr1    10    .    ACGT    ACGG    .    PASS    .. On
contig 1 (...ACGT at
      10..13), final_POS = 13, so [final_POS - 1, end_of_REF] is 1-based [12,
      13] (GT). On contig 2 (...TTGT at 10..13), 1-based [12, 13] is also GT,
      yet the record is a REF_MISMATCH. Given only Win{11n, [G{}, T{}], clen},
      Norm.line_in must return Some{normalized} by R14 (for contig 1), which
      violates soundness on contig 2.
      • Change to agree: Require the window to cover [max(1, min(initial_POS,
      final_POS - 1)), initial_POS + len(REF) - 1] for normalized records
      (and [initial_POS, min(clen, initial_POS + len(REF) - 1)] to detect
      REF_MISMATCH).
  • R15: AGREE — Adding deterministic ##framebender_normVersion= and
  ##framebender_normCommand=norm ... lines with < 0x20 and 0x7F sanitized to
  spaces guarantees valid VCF 4.3 unstructured meta lines.
  • R16: AGREE — Inserting immediately before #CHROM and exiting 1 if #CHROM
  is absent is clean and unambiguous.
  • R17: AGREE — Phrasing padding in terms of where the event begins and
  quoting tan2015.txt verbatim resolves the ambiguity.
  • R18: AGREE — Qualifying shift's comment to 1 <= k < pos on a valid
  variant matches the Bend definition.
  • R19: AGREE — Supporting 64-bit positions matches bcftools/htslib and
  bounds-checks via contig length.
  • R20: AGREE — Updating the types.bend:5 comment and wiring Base.of_fasta
  into R1 resolves the mismatch.
  • R21: AGREE — Pinning compatibility against bcftools 1.24 norm -f / -c w
  on a differential test corpus with enumerated byte-level exceptions makes
  Decision 5 verifiable.
  ──────
  ### Summary of NEW Problems Introduced by responses-1.md

  1. Window sufficiency law in R14 is false (unsatisfiable) on right-trimmed
  records — Severity: blocker
      • Covering only [final_POS - 1, end_of_REF] misses [initial_POS,
      final_POS - 2] whenever prefix trimming shifts POS right by >= 2 bases,
      making it impossible to distinguish a valid variant from a REF_MISMATCH
      on the omitted prefix (see R14 counterexample).
  2. R12 + S3 + S1 outcome classification is neither disjoint nor total, and
  breaks on multiallelics/breakends — Severity: blocker
      • Multiallelic duplicate ALTs (S1/R12/R13): ALT_DUP only checks ALT ==
      REF, letting ALT=A,a normalize into invalid VCF ALT=A,A instead of
      raising ALT_DUP.
      • S3 vs NON_ACGTN / POS 0 collision (S3/R12): Mixed multiallelic S3
      records (G,*, G,<*>) and symbolic/breakend ALTs contain non-ACGTN
      characters, and valid VCF 4.3 telomere breakends use POS = 0 or clen +
      1; without an explicit allele grammar and check precedence, default -c
      e aborts on out-of-scope S3 records.
      • Missing malformed-line cases (R12): < 8 fields, non-numeric POS, and
      ￹empty alleles (A,,G) match none of the 3 outcomes; POS 0 has no -c w
       warning tag.
       • Ill-defined -c e partial-stdout rule (R12/R1): "prefix of what a
       successful run would write" has no referent on failing inputs and can
       fail when buffered records precede an error followed by a left-shifting
       record.
  3. R8 missing-final-newline rule concatenates output lines into corrupt VCF
  — Severity: blocker
      • Reusing an empty line terminator from an unterminated #CHROM line or
      ￹an unterminated final record that sorts earlier than another record
       ￹glues two VCF lines together with no \n between them (see R8 example).
  4. Ordering & buffering underspecification in R3/R4/R7 vs R1 determinism —
  Severity: should fix
      • Underspecified flush point (R4/R1): R1 requires exact (stdout, stderr,
      exit) equality with run(fasta, vcf, opts), so R4 cannot merely say
      ￹"when a record would have to be written before one already written"—run
       must define the exact w-heap flush predicate.
       • -w 0 off-by-one (R4): "moves left by w or more" triggers on 0-move
       ￹records when -w 0.
        • Ungrouped CHROM blocks (R3/R4): Dropping grouped lets chr1 ... chr2 ..
.
chr1 exit 0 while emitting invalid ungrouped VCF, contradicting R4's
"success implies sorted output".
• Mid-body # lines (R7/R3): Allowing non-record # lines in the body
 ￹leaves their output placement and effect on CHROM runs undefined.
  • Undocumented bcftools difference (R4/R21): Exiting non-zero on shifts
  ￹exceeding -w differs from bcftools 1.24 norm -f (warns and continues)
   ￹and must be listed under DOCUMENT.
  5. Canonical-text & INFO/END contradictions in R9 + S2 — Severity: should
  fix
      • R9 vs R12 under -c w: R9 rewrites any in-scope record passing the
      ￹reference check (including ALT_DUP lines like 010    .    a    a),
contradicting
      ￹R12's byte-identical pass-through for -c w problem lines.
       • R9 vs S2 on INFO/END: Only updating INFO/END "when a record is
       ￹rewritten" leaves wrong/leading-zero END values on already-uppercase
        ￹records while fixing them on lowercase equivalents, and leaves non-
         ￺integer INFO/END behavior undefined.
  6. Minor gaps in S1 and R1/R7 — Severity: minor
      • S1 algorithm prose at POS = 1: The parenthetical (trim the right end
      while it is identical in all alleles, pad left when an allele becomes
      empty...) must guard against trimming to empty at pos == 1 (the
      ￹declarative left_aligned && parsimonious laws handle pos == 1 properly).
       • R1 FASTA/reference details: Reference-read events in Norm.step must
       ￹distinguish unknown contig from empty slice (and supply contig length
        clen), FASTA sequence parsing should strip horizontal whitespace as
        well as CR/LF, duplicate FASTA contig names need a rule, and R1 line 44
        says "mapped by R6" where R5 is meant.
        • R7 #CHROM prefix match: "starting with #CHROM" matches #CHROMOSOME...;
       ￹check first tab field == "#CHROM".`


