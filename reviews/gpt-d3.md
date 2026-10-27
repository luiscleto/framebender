# GPT, draft-3 review

• 1. T1 — AGREE. dstep adds the number of requests in each batch; result
     requires both termination and reads <= limit. A huge duplicate-read batch
     can no longer pass merely by consuming one transition.

  2. T2 — AGREE. The science files import neither Norm nor the protocol.
     MACHINE.bend and protocol.bend contain the implementation contract.

  3. T3 — AGREE. Reusing frozen definitions is compatible with independent
     optimization: faster implementations can prove equality. draft/run.bend now
     matches the working-tree function bodies.

  4. T4 — AGREE, as an explicit scope restriction. machine now requires
     Fasta.plain, which checks every non-header line for spaces and tabs. For
     excluded files, success versus “unsupported FASTA” remains unspecified;
     this change does not establish deterministic rejection for them.

  5. T5 — AGREE. unique states algorithm-independent uniqueness, and
     normalized_valid establishes validity of the input variant for every
     normalized outcome. Together with preservation, validity and normality,
     these justify reviewing Tan.normal through its laws.

  6. T6 — AGREE. P.Ans contains only Unknown and Known; NoAns is removed.

  7. T7 — AGREE. The cited comment errors and obsolete Norm.judge_in reference
     are corrected.

  8. T8 — AGREE as an adoption condition. The final proof gate must cover both
     layers, including unique, normalized_valid, MACHINE.machine and
     MACHINE.usage. The current root check.sh/PROOF.bend still targets the old
     specification, so passing it unchanged would not validate this draft. The
     revised trusted driver also requires review.

  I approve the draft statements for the explicitly restricted FASTA domain,
  subject to T8’s final proof and driver checks. No remaining blocker or should-
  fix item in the statements.

