# GPT, round 2 (resumed codex session; 10m 45s)

• These verdicts assess the proposed rewrite. The additional bcftools source-
  code claims remain unverified under the permitted-source restriction. Examples
  use (POS, REF, ALT).

  1. S1 — AGREE. Joint normalization with preserved ALT order is the appropriate
     multiallelic extension; additional proof obligations are listed below.

  2. S2 — DISAGREE. END handling is incomplete: bare END, END=., malformed
     values, duplicate keys, and inconsistent integer values have no stated
     policy. VCF §3 also distinguishes precise from imprecise END semantics.
     Change: define these cases explicitly, restrict the formula to precise
     explicit-allele records, and classify unsupported imprecise cases or
     specify their semantics separately. Resolve the interaction with R9
     described below.

  3. S3 — AGREE. The explicit exclusions and record-local limitation are
     acceptable scope choices.

  4. R1 — AGREE. The end-to-end state-machine law, truthful-reference premise,
     explicit trusted driver, and termination obligation address the original
     gap.

  5. R2 — AGREE. Allowing rightward moves fixes the incorrect hypothesis.

  6. R3 — DISAGREE. Sorting each maximal CHROM run permits successful output
     containing chr1, chr2, chr1. Each run can be sorted while the file violates
     VCF’s contiguous-CHROM requirement. Change: reject a contig that reappears
     after its run ends, or globally regroup contigs. With the proposed
     preservation of run order, rejection is the consistent choice.

  7. R4 — AGREE. Detecting an actual ordering violation, failing explicitly, and
     leaving normalization unbounded is a sound policy; the failure-output
     contract needs the R12 correction below.

  8. R5 — AGREE. The IUPAC mapping matches the supplied VCF rule; the other-
     character-to-N policy is an explicit deviation.

  9. R6 — AGREE. Literal-symbol equality for N is coherent when its biological
     limitation is documented.

  10. R7 — DISAGREE. A legal VCF contig name can start with # (§1.4.7). After
     the real header, #ctg\t1\t.\tAC\tAT\t.\t.\t. can therefore be a data
     record, not a comment. Also, starts_with("#CHROM") accepts #CHROMjunk as
     the column header. Change: recognize the actual column-header fields,
     validate the header/body transition, and parse body records without blanket
     rejection of #-prefixed CHROM names.

  11. R8 — DISAGREE. Preserving an absent terminator becomes unsafe after
     sorting. On AAAA, an LF-terminated (2,A,C) followed by an unterminated
     (3,AA,A) becomes (1,AA,A) before (2,A,C); their text is concatenated into
     one malformed line. VCF also requires the final data-line separator.
     Change: reject unterminated input, or explicitly add a separator when
     necessary and exempt that repair from byte preservation.

  12. R9 — AGREE. Canonical POS and allele spelling is a coherent record-level
     policy; its interactions with END and whole-file idempotence need
     clarification below.

  13. R10 — DISAGREE. Documentation does not repair an annotation the rewrite
     makes false. (1,AC,AT) with CIGAR=2M still becomes a one-base substitution
     carrying a two-base alignment. Also, genotype fields are not universally
     allele-indexed: DP, PS, and custom fields invalidate that blanket
     justification. Change: on structural representation changes, remove/
     recompute invalidated annotations or exclude affected records explicitly;
     narrow the preservation claim to fields whose semantics are actually
     preserved.

  14. R11 — AGREE. Explicitly limiting the guarantee to individual records
     resolves the scope question, although dependent * annotations can remain
     inconsistent.

  15. R12 — DISAGREE. Classification is neither exhaustive nor unambiguous.
     Symbolic ALT contains non-ACGTN characters; a valid telomeric breakend can
     have POS 0; mixed ALT C,* is expressly excluded. These overlap the
     “problem” category. Too few fields, empty alleles, nonnumeric POS, and
     malformed END lack outcomes; POS 0 lacks a diagnostic code.

     The failure-prefix promise is also unsuitable for streaming ordering
     failures: after POS 2 has been emitted, a later record may normalize to POS
     1, so existing stdout cannot be a prefix of the fully sorted output.

     Change: provide an exhaustive, precedence-ordered classification table and
     diagnostic codes, preserving the intended exclusions. Define failure stdout
     as a prefix of the output for records accepted before the offending record,
     with deterministic flushing; alternatively, buffer output atomically until
     success.

  16. R13 — AGREE. Detecting any ALT equal to REF after case folding makes that
     policy explicit.

  17. R14 — DISAGREE. The proposed sufficient window can omit the original REF
     prefix when normalization moves right. For input (1,ACG,ACT), final POS is
     3; the proposed window can contain only positions 2–3, CG. Contigs ACG and
     TCG have identical windows and lengths, but one requires normalization and
     the other a REF-mismatch outcome. A window-only function cannot distinguish
     them.

     Change: require coverage of the complete original REF interval plus all
     reference context needed for joint normalization, with chromosome-boundary
     clamping. Specify window expansion so it actually reaches that union and
     eventually the whole contig.

  18. R15 — AGREE. Sanitizing control bytes and prefixing the command value
     prevents the identified header-line injection.

  19. R16 — AGREE. Inserting immediately before the validated column header and
     rejecting its absence is appropriate.

  20. R17 — DISAGREE. The replacement wording requires padding for every event.
     A position-1 SNP A→C needs no padding, nor do general complex
     substitutions. Change: restrict the rule to simple insertions/deletions
     requiring an otherwise empty allele, and retain explicit chromosome-start
     exceptions when quoting Tan’s normalization conditions.

  21. R18 — AGREE. The domain qualification fixes the misleading shift comment.

  22. R19 — DISAGREE. A 64-bit bcftools implementation does not override the
     supplied VCF specification’s signed-32-bit Integer definition. Checking
     contig bounds permits POS 2147483648 on a sufficiently long contig;
     computed END can also exceed the limit. Change: enforce the VCF range for
     POS and END, or explicitly document larger coordinates as a format
     extension rather than claiming no additional rule is needed.

  23. R20 — AGREE. Correcting the comment and connecting FASTA conversion to the
     end-to-end law addresses the finding.

  24. R21 — AGREE. Pinning the comparison version and maintaining a differential
     corpus with narrowly named byte-level exceptions is appropriate.

  Additional new problems:

  25. S1: multiallelic chromosome-start algorithm — blocker. On reference A,
     (1,A,CA,GA) is already normalized. All alleles end in A, but blindly
     applying the stated algorithm empties REF and requests nonexistent left
     padding. Fix: explicitly stop suffix trimming at POS 1 when it would empty
     any allele; retain nonempty alleles and bounded left alignment.

  26. S1: ALT cardinality and duplicate policy — should fix. Index-wise equality
     must explicitly require equal ALT counts; comparing only paired indices
     could incorrectly equate A→C and A→C,G. The new scope also leaves duplicate
     ALTs such as c,C unspecified. Fix: preserve ALT count and order in the
     laws, compare all indices over an equal-length list, and define duplicate
     handling after case folding. Do not deduplicate without remapping GT and
     allele/genotype-indexed arrays.

  27. S2/R9: END correctness depends on spelling — should fix. An already-normal
     (1,A,AT) with END=9 is byte-identical under R9, while the same record
     spelled a,aT is rewritten and gets END=1 under S2. Thus a casing change
     decides whether inconsistent metadata is repaired. Fix: validate or repair
     END independently of textual canonicalization, and restrict the byte-
     identical promise accordingly.

  28. R9/R15: whole-file idempotence — minor. A second invocation adds another
     pair of metadata lines, so “a second run changes nothing” cannot describe
     the complete file. Fix: state that idempotence concerns body records, or
     define replacement/deduplication of the tool’s metadata.

  29. R3/R7/R12: placement of unkeyed body lines — should fix. Passed-through
     blank or malformed lines may have no CHROM/POS, so the stable-sort rule
     does not determine their placement. Treating them as run boundaries could
     also defeat ordering across them. Fix: specify their output placement and
     ensure they cannot split an otherwise continuous chromosome run.

