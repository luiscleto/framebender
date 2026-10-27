# Claude, round 2 (new session in plan mode, given its round-1 summary; 5m 23s)

  Round 2: Claude

  Verdicts

  S1: DISAGREE (should fix; the generalization itself is right). There are two
  gaps in the definition.
  - Contradiction with R12. S1 says "in scope" means REF and every ALT are
    A/C/G/T/N. R12 makes "letters outside ACGTN" a problem. So chr1 100 . A R is
    passed through under S1 but stops the run under R12.
    - Fix: define scope by shape. A record is in scope when REF and every ALT
      match ^[A-Za-z]+$, so not <…>, not a breakend, not *, not .. Inside scope,
      letters outside ACGTN are then the NON_ACGTN problem.
  - Duplicate ALTs are not covered. R12/R13 only mention ALT = REF, so A G,g is
    undefined.
    - Fix: valid requires the ALTs to be pairwise distinct and each different
      from REF, case-insensitively. Anything else is ALT_DUP.

  S2: DISAGREE (should fix). The END rule is not total.
  - Which key counts: it should be the exact key END, not SVEND or END_POS.
  - Odd END values: it does not say what happens with a repeated END, a bare END
    flag, or END=abc.
  - Inconsistent END: it does not say what happens when the input END ≠
    POS+len(REF)−1. Example: chr1 10 . CA C . . END=50 moves left, and END is
    silently rewritten to the new POS. That hides a malformed or imprecise
    record.
  - Fix, in three parts:
    - END is rewritten only when POS or len(REF) changes, and only the digits of
      that single entry are replaced.
    - A record whose END is missing a value, not decimal, repeated, or
      inconsistent on input is passed through and counted.
    - Check what vcfnorm.c does in that case. If bcftools differs, document it.

  S3: AGREE. These records cannot be normalized locally, and the behaviour
  matches bcftools, apart from the <DEL>/<DUP> difference S3 already documents.

  R1: DISAGREE (should fix; the design is right but under-specified).
  - Chunking. The top law must hold for every way of splitting the VCF bytes
    into chunks. That includes empty chunks, a split between CR and LF, and a
    split inside a field. Otherwise it holds only for the chunking the driver
    happens to use.
  - Reference answers. It must say what a "truthful answer" is when the contig
    is unknown and when b is past the contig length. The answer has to carry the
    contig length.
  - FASTA cases. run's FASTA definition needs rules for:
    - duplicate contig names (first one wins, as in .fai);
    - text before the first >;
    - an empty name;
    - spaces inside sequence lines.
  - Typo: "letters mapped by R6" should read R5.

  R2: AGREE.

  R3: DISAGREE (should fix). A "stable sort by output POS" needs a key for every
  body line, and only normalized records have an output POS.
  - Example: a body #comment line, a line with fewer than 8 fields, a blank
    line, or a <DEL> record between two chr1 records. Can a moved record cross
    it?
  - Fix: the key is the output POS for normalized records and the input POS for
    every other line that has a numeric POS. A line without a numeric POS ends
    the current CHROM run and stays where it is, so no record crosses it.

  R4: DISAGREE (should fix). "Would have to be written before one already
  written" depends on when the buffer is flushed. Unless run fixes that rule,
  the exit code is not determined by the input.
  - Example: input POS 200000, 400000, 100 with w = 100000. Whether this run
    stops depends on whether 200000 was already flushed.
  - Fix, in four parts:
    - Write the flush rule into run: flush entry b when the CHROM changes, or
      when outpos(b) + w ≤ inpos(current). With that rule, sorted input and left
      moves < w imply success, even with right moves.
    - Say that this stop ignores -c, and give its exit code and message.
    - Require w ≥ 1.
    - Document that bcftools does not stop here.

  R5: AGREE. The mapping matches VCF 4.3 §1.6.1: alphabetically first base, R→A,
  Y→C, K→G, and so on.

  R6: AGREE. Note that because of R4, a slide of more than w through a large N
  gap now ends the whole run. That is acceptable, but document it.

  R7: AGREE. The POS 0 conflict with R12 is dealt with under R12.

  R8: AGREE. Two edge cases are listed under N6 below.

  R9: AGREE. Reword "passes the reference check" to "classified as normalized"
  (R12). The idempotence claim is covered under N4.

  R10: AGREE.

  R11: AGREE.

  R12: DISAGREE (blocker for writing run). As written, the classification does
  not give exactly one outcome per line.
  - Contradictions:
    - S1 versus NON_ACGTN (see S1).
    - R7 says POS 0 is out of scope; R12 says it is a problem. VCF allows POS 0
      and POS N+1 for telomeres, but only as breakends.
    - It is unclear whether UNKNOWN_CHROM applies to out-of-scope records.
      Example: decoy1 100 . T <DEL>. Stopping there would kill
      structural-variant files that use contigs missing from the FASTA.
  - Fix: one ordered classification.
    a. A line that is not a record (body # line, fewer than 8 fields,
       non-numeric POS) is passed through.
    b. A record that is out of scope by shape (S3) is passed through, whatever
       its CHROM.
    c. UNKNOWN_CHROM stops the run.
    d. NON_ACGTN.
    e. ALT_DUP.
    f. REF_MISMATCH, which includes POS 0 and a REF running past the contig end.

    Each line takes the first outcome that applies.
  - Stdout when the run stops. "A prefix of what a successful run would write"
    is undefined when no successful run exists. This applies to stops under -c
    e, R4 and R16.
    - Fix: stdout is exactly what the flush rule had already written, with no
      partial line.
  - Stderr bytes. run returns stderr exactly, so the message texts and the
    summary format have to be fixed byte for byte. Alternatively, the law can
    compare a structured list of events (kind, CHROM, POS, line number) passed
    through a fixed rendering function.
  - Summary on failure. State whether the summary is also printed when the run
    fails.

  R13: AGREE. Extend it to duplicate ALTs (see S1).

  R14: AGREE. The sufficiency range is correct, including the padding base after
  the event at position 1. A REF running past the contig end is still covered
  by window_whole.

  R15: AGREE.

  R16: AGREE. Matching on #CHROM is covered under N7.

  R17: AGREE. Optional wording change: "when there is no base before the event".
  This also covers an insertion before base 1.

  R18: AGREE.

  R19: AGREE.

  R20: AGREE.

  R21: DISAGREE (minor). A byte-exact comparison will probably also catch
  reformatting that has nothing to do with normalization. bcftools rewrites
  every record through htslib. Likely cases are QUAL formatting, an added
  ##FILTER=<ID=PASS…> header line, and LF line endings. I could not confirm
  these from the three sources.
  - Fix:
    - Run the corpus and add "htslib re-serialization" as a named class of
      differences.
    - Compare exit codes and the line where a -c e run stops, as well as the
      bytes.

  New problems

  N1 (should fix): gVCF. Under S1/S3, any record containing <*> or <NON_REF> is
  out of scope, so no indel in a gVCF is ever normalized.
  - Check what vcfnorm.c does with these alleles. Then either:
    - normalize the explicit alleles and keep the <*>/<NON_REF> allele in place;
      or
    - document prominently that gVCF indels are left as they are.

  N2 (minor, document): multiallelic normal form. Normalizing a multiallelic
  record gives a different result from splitting it and then normalizing each
  part.
  - Example on contig TCAAAG: chr1 3 . AAA AA,AAG becomes 4 AA A,AG.
  - Split first, the deletion becomes 2 CA C and the SNP becomes 5 A G.
  - This is correct under Tan et al. and bcftools. The README should say so, and
    recommend bcftools norm -m- before comparing call sets.

  N3 (minor): duplicate ALTs. valid has no rule for them (see S1).

  N4 (should fix): idempotence. R9's "a second run changes nothing" is false for
  the whole file: R15 adds two more header lines on every run. State the
  idempotence law for the body only.

  N5 (blocker for R1): stdout and stderr on failure. See R12.

  N6 (minor): line endings. R8 does not cover:
  - a CR at the end of the file with no LF;
  - a #CHROM line with no terminator, where the added header lines need one (use
    LF).

  N7 (minor): finding #CHROM. "Starts with #CHROM" also matches #CHROMOSOME….
  Match a line equal to #CHROM, or one starting with #CHROM\t.

  N8 (minor): R3/R4 versus bcftools.
  - framebender will sort unsorted input inside the buffer and stop when it can
    no longer do so. bcftools keeps going. Document this.
  - With the proposed flush rule, a file whose positions keep going down is
    never flushed until the end. It is held in memory but still comes out
    correctly.

