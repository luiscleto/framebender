# GPT, round 3 (11m 37s)

• I treat the four [run] corrections as reported measurements; I have not
  independently reproduced them.

  1. bcftools correction: duplicate ALTs — AGREE. The reported result supports
     documenting framebender’s stricter duplicate policy.

  2. bcftools correction: END — AGREE. The reported rewrite condition is now
     distinguished from input-END validation.

  3. bcftools correction: <*> — AGREE. The stated gVCF exclusion is explicit.

  4. bcftools correction: unknown CHROM — AGREE. The corresponding framebender
     exception for out-of-scope records is documented.

  5. Classification — AGREE. The ordered rules resolve the previous overlaps,
     missing outcomes, duplicate-ALT policy, and #-prefixed contig handling.

  6. S1 — AGREE. Equal ALT counts, preserved indices, and the chromosome-start
     trimming guard resolve the identified multiallelic gaps.

  7. S2 — AGREE. Validating END before normalization and updating it only when
     numeric POS or REF length changes removes the spelling-dependent behavior.

  8. R1 — AGREE. Chunk independence, explicit reference answers, and specified
     FASTA parsing substantially close the integration contract.

  9. R3/R4 — DISAGREE — blocker. The MALFORMED flush contradicts the
     unconditional small-move success guarantee. With reference ACG, -c w, and
     w=100000, consider:

     chr1       1       .       ACG     ACT     .       .       .
     chr1       2       .       C       T
     chr1       2       .       C       T       .       .       .

     The first record normalizes to POS 3. The malformed middle line flushes it.
     The last record stays at POS 2 and triggers UNSORTED when written. Input
     positions are nondecreasing, and nothing moves left. Ignoring the malformed
     line when checking input order does not fix the counterexample.

     Change: qualify the no-UNSORTED guarantee to inputs without MALFORMED
     barriers, and document that -c w can otherwise fail despite small moves.
     State the successful-output ordering guarantee over keyed lines, since
     malformed lines have no key. Alternatively, redesign malformed-line
     placement without forcing these flushes.

  10. R8 — AGREE. Repairing missing body-line terminators prevents concatenation
     after sorting, with the byte-preservation exception explicitly stated.

  11. R9 — AGREE. Restricting canonicalization to NORMALIZED records and
     idempotence to the body resolves the previous conflicts.

  12. R10 — DISAGREE — should fix. I accept the explicit preserve-and-warn
     policy, but the remaining semantic claims are false. Number=A/R/G specifies
     indexing and cardinality, not independence from representation. For
     example, define a FORMAT field XA, Number=A, containing the ALT sequence.
     On reference AC, (1,AC,AT) with GT:XA=0/1:AT becomes (2,C,T), but copied
     XA=AT is stale despite preserved indices. VCF also defines DP as depth at
     this position. Finally, CIGAR is not the only reserved INFO field defined
     relative to REF/ALT: SVLEN is another, although normalization preserves its
     length difference.

  Change: guarantee preserved genotype/allele index associations and copied
  bytes, without claiming general annotation truth. Remove the blanket claims
  about indexed fields and other FORMAT fields, and correct the “one reserved
  INFO key” statement. That would resolve my objection without requiring
  annotation removal.

  13. R12 — DISAGREE — should fix. “Stdout is exactly the whole lines the buffer
     rule had written” omits header output. For example, with w=1, reference AC,
     two valid SNP records at positions 1 and 2 cause the first record to be
     flushed; a subsequent REF mismatch stops the run. Stdout necessarily
     includes the header preceding that flushed record, although header lines
     never entered the body buffer.

  Change: define failure stdout as the concatenation of all stdout-write actions
  before termination, including header output and repaired terminators. Specify
  when the header is emitted. The structured stderr events and success-only
  summary are otherwise acceptable.

  14. R14 — AGREE. Including the complete original REF interval fixes the
     indistinguishable-reference counterexample; the chromosome-clipped context
     and whole-contig fallback are appropriate.

  15. R17 — AGREE. The revised wording distinguishes indel padding from
     substitutions and handles the absence of a preceding base.

  16. R21 — AGREE. Comparing exits and stopping lines is useful; each permitted
     reserialization difference should remain individually enumerated.

  Additional new problems:

  17. Integer extension — should fix. The new policy names a 64-bit POS
     extension but does not specify its upper bound or whether END receives the
     same extension. For example, POS 2147483647 with a two-base REF requires
     END 2147483648, beyond VCF’s original Integer range. Fix: define the exact
     supported ranges for POS and END, including computed END, and classify
     overflow explicitly. Arbitrary-precision Bend arithmetic should not
     silently become an undocumented format extension.

  18. STALE_CIGAR trigger versus canonicalization — minor. “A rewritten record
     carrying it” includes spelling-only changes. On reference A, (01,a,c) with
     CIGAR=1M becomes (1,A,C) without invalidating the alignment, yet receives
     STALE_CIGAR. Fix: trigger the warning on changes to the parsed variant
     representation, excluding case and decimal-format changes; name it
     POSSIBLY_STALE_CIGAR if validity is not actually checked.

  19. Empty-buffer chromosome tracking — should fix. The new transition rule
     compares CHROM with “the buffered lines,” but the buffer can be empty after
     a malformed-line flush or a sufficiently large left shift. Fix: explicitly
     retain the active CHROM, completed CHROMs, and last emitted key
     independently of buffer contents. Otherwise repeated-contig detection and
     transition flushing remain undefined in precisely those cases.

