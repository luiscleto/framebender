# Claude, draft-3 review

  answers are reviews/*-d2.md). Read-only. For each item T1-T8 answer AGREE or
  DISAGREE (reason, example, the change that would make you agree), checking
  the draft files. Then say whether you approve the two-layer draft, or list
  any remaining blocker or should-fix item. Be brief; final answer.

● Bash(cat reviews/responses-6.md; ls -la draft reviews/*-d2.md; git status
      --short)

     Reviews: `reviews/gpt-d2.md`, `reviews/claude-d2.md`, `reviews/gemini-
     … +75 lines (ctrl+o to expand)

● Bash(cat draft/MACHINE.bend draft/protocol.bend draft/norm.bend; head -30
      draft/tan.bend; diff run.bend draft/run.bend; head -5
      draft/machine_part.txt)
     import ./types.bend as B
     import ./protocol.bend as P
     … +283 lines (ctrl+o to expand)

● Bash(cd /home/luisc/Work/framebender/draft && grep -n "^import\|^law
      \|NoAns\|R\.has\b\|R\.added\b\|R\.stop\b\|judge_in" LAWS.bend types.bend
      run.bend tan.bend proto…)
     run.bend:2:import ./types.bend as B
     LAWS.bend:1:import Base
     … +91 lines (ctrl+o to expand)

● Bash(cd /home/luisc/Work/framebender && sed -n 258,275p draft/LAWS.bend; diff
      types.bend draft/types.bend | head -60; diff norm_var.bend draft/tan.bend
      | grep '^[<>]…)
       for hs: {haps(seq, v) == haps(seq, w) : List<&2, List<&2, B.Base>>}
       {Nat.is_le(size(Tan.normal(seq, v)), size(w)) == True{} : Bool}
     … +60 lines (ctrl+o to expand)

● Bash(git diff HEAD -- LAWS.bend | grep '^[-+]' | head -40)
     +++ w/LAWS.bend
     -# Every allele R.has at least two bases.
     … +27 lines (ctrl+o to expand)

● I approve the two-layer draft (draft 3), on the condition in T8. I agree with
  all eight items. The only reservation is T4: the law is now right, but a
  residue of my original concern stays as a minor point. I checked the claims
  against the draft files by reading them; I did not run ./check.sh.

  - T1 (reads not bounded): AGREE. dstep now adds each Ask's list length to
    reads, and result(d, limit) checks it against the same bound used for steps.
    Every read is cut off at the contig's length, so the total bytes read are
    bounded too. The bound comment is accurate and no longer talks about the
    code.
  - T2 (layers share files): AGREE. LAWS.bend imports only types.bend, tan.bend
    and run.bend. types.bend no longer holds Ans, In or Next; they live in
    protocol.bend. The driver, bound, machine and usage live in MACHINE.bend.
  - T3 (code calls spec definitions): AGREE. The rule "science files are frozen;
    code may call them or use its own copies proven equal" fixes the problem I
    raised. draft/run.bend is the working-tree version with the lazy
    take_ready/drop_ready, so what gets frozen is current. Only its header
    differs.
  - T4 (unsupported FASTA): AGREE.
    - The P.Fasta.plain premise loses nothing. run sees the FASTA only through
      Fasta.parse, which drops spaces and tabs. So for any non-plain file F
      there is a plain file F′ with the same parse, and F′ is shorter, so its
      bound is smaller. Once the driver stops, its state doesn't change, so the
      law for F′ implies the law for F.
    - Residual (minor): the thing a user sees for a non-plain FASTA still
      depends on the read pattern, and it can change between versions. For
      example, a tab in a contig the VCF never mentions gives exit 0 today, and
      exit 2 after a prefetching optimization.
    - Change that would close it: have main.bend check Fasta.plain once at
      startup, which is one byte pass. Failing that, say in the user
      documentation that such files are unsupported and that the result may
      differ between versions.
  - T5 (expert need not read the normalizer): AGREE.
    - unique is stated without mentioning any algorithm.
    - normalized_valid, through line_valid, rebuilds exactly the variant
      judge.bases hands to Tan.normal: Rec.pos, Allele.read and Alleles.read on
      Bases.of_fasta(raw).
    - Together with same_change, stays_valid and standard_form, these fix
      Tan.normal's result wherever run uses it. Keeping tan.bend as it is
      (identical to norm_var.bend apart from the rename) is fine.
    - Nit: the tan.bend header should say the laws fix the result "for valid
      variants".
  - T6 (dead NoAns): AGREE. It is gone from P.Ans.
  - T7 (comment typos and drift): AGREE. No R.has/R.added/R.stop slips are left
    in the comments, and nothing mentions judge_in any more. The root LAWS.bend
    working-tree change contains only these comment fixes.
  - T8 (approval conditional on proofs): AGREE. Adoption should wait until
    ./check.sh (both bend and --verdict) passes on the final files, including
    the reworked machine proof. The new list-answering code in main.bend also
    needs a second review as trusted code.

  There are no remaining blockers or should-fix items. Two minors are left: the
  T4 residual and the T5 header nit.

