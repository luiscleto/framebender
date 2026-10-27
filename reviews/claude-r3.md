# Claude, round 3 (2m 40s)

  Round 3: Claude

  Verdicts

  Corrections to claims about bcftools: AGREE. These were checked by running
  bcftools, so they override what the reviewers inferred, including Gemini's
  claim about duplicate ALTs.

  Classification (replaces R7, R12, R13 and the S1 scope sentence): AGREE. First
  match wins and NORMALIZED is the fallback, so every line gets exactly one
  outcome. Rules 2 to 8 settle the contradictions I raised in round 2. Three
  smaller points are under N2 to N4 below.

  S1 (multiallelic): AGREE. The laws are declarative, and the start-of-contig
  case is correct. I checked (1, A, CA,GA) on A, and (2, AC, C) on AAC, which
  becomes (1, AA, A).

  S2 (END): AGREE. Because END is checked on input (rule 4), rewriting it only
  when POS or len(REF) changes is enough, and the result no longer depends on
  how the record was spelled.

  R1 (end-to-end law): AGREE.

  R3/R4 (ordering): DISAGREE (blocker for the proof; easy to fix). Under -c w,
  the rule that a MALFORMED line flushes the whole buffer makes the stated law
  false: "if the input is grouped and sorted and no record moves left by w or
  more, the run never stops with UNSORTED".
  - Example (w = 100000, -c w), on a chr1 with a run of A from position 150 to
    301:
    a. Input lines in order: chr1 100 . A G, then chr1 200 . A G, then a line
       with 5 fields, then chr1 300 . AA A.
    b. The malformed line flushes 100 and 200.
    c. The deletion normalizes to POS 149. It moved left by 151, which is less
       than w.
    d. 149 is smaller than the last key written (200), so the run stops with
       UNSORTED, although the law's premises hold.
  - Change that would make me agree: a MALFORMED line should not flush.
    - Give it a key equal to the input POS of the previous keyed line on the
      current CHROM run (0 if there is none), and insert it stably.
    - With that key it counts as a line that did not move, so the proof of the
      law goes through unchanged.
    - The less good option is to add "contains no MALFORMED line" to the law's
      premises and document that a malformed line can cause UNSORTED under -c w.
  - Two wording fixes:
    - "A different CHROM than the buffered lines" should read "a different CHROM
      than the current CHROM run". The buffer can be empty right after a flush.
    - Keep the law as "stable sort by key within each CHROM run, runs in input
      order". It is true under this flush rule, and it is stronger than
      "sorted".

  R8 (line endings): AGREE. One gap: say that an unterminated #CHROM line at the
  end of the file is also given LF. As written, the rule covers only body
  lines.

  R9 (canonical text): AGREE.

  R10 (stale annotations): AGREE with the policy. The claim that CIGAR is "the
  one" representation-dependent key is too strong (see N5).

  R12 (stdout and stderr on a stop): AGREE. One detail: on UNSORTED, the error
  event should name the line that would have come out of order and the line
  whose arrival caused it, since these can differ.

  R14 (window sufficiency): AGREE. I was wrong to accept the round-1 range in
  round 2; the right-move counterexample from Gemini and GPT is correct. I
  checked the new range: the left padding is only ever added at the final POS,
  so the interval from the lower of POS and (final POS − 1) up to the end of the
  input REF is enough, for multiallelic records too. One gap is under N6.

  R17 (wording): DISAGREE (minor; it is a comment, not a law). "An insertion or
  deletion is written with one unchanged neighbouring base" is false for an
  event that changes length and also substitutes bases.
  - Example: on contig GACT, (2, AC, T) is already normal. It deletes a base and
    has no unchanged neighbouring base.
  - Change that would make me agree: "When some allele would otherwise be empty,
    every allele gets one unchanged neighbouring base. That base is the one
    before the event or, when there is no base before it (the event starts at
    the first base of the contig), the one after it. Otherwise no neighbouring
    base is added."
    - This also covers multiallelic records, such as (1, GA, G,GAA).

  R19 (POS above 2^31 − 1, inside the classification): AGREE. Accepting it and
  documenting it as an extension of VCF is honest.

  R21 (comparison): AGREE.

  New problems

  N1 (blocker, easy fix): the MALFORMED flush makes the R3/R4 law false (see
  above).

  N2 (minor): blank lines stop the default run. A blank line is MALFORMED, so
  under the default -c e a stray empty line at the end of a file exits 1.
  - Run bcftools on such a file. Then either match its behaviour or document the
    difference.

  N3 (minor): BAD_END stops where bcftools does not. bcftools leaves GT G END=99
  unchanged and exits 0 (you ran it). framebender stops on it by default. This
  difference is not in the DOCUMENT list yet.

  N4 (minor): a REF that is not letters is classed as OUT OF SCOPE. Examples are
  . or A1. VCF requires REF to be ACGTN even when the ALTs are symbolic, so
  these lines are malformed and should not be passed through silently. Move "REF
  not [A-Za-z]+" into MALFORMED.

  N5 (minor): R10 overstates its claim. Other reserved keys can also become
  wrong after a rewrite:
  - AA (ancestral allele): for indels it is usually written in the same allele
    form as REF/ALT.
  - HOMSEQ and HOMLEN (§3, microhomology at the event breakpoints).

  Drop "the one". Either emit the stale-annotation event for these keys as well,
  or rely on the general disclaimer alone.

  N6 (minor): R14 does not cover lines that are not NORMALIZED. "Final POS" does
  not exist for those lines. The law should say:
  - REF_MISMATCH needs a window covering the input REF interval, clipped to the
    contig.
  - Outcomes 1, 2 and 4 to 7 need no reference at all.
  - UNKNOWN_CHROM needs only the "unknown" answer.

