# Gemini, draft-2 review

  ### Findings

  1. dstep / bound: total reference reads (Req) are no longer bounded —
  should fix
      • Problem: In the old protocol, one Ask performed one read, so bound
      bounded both machine steps and total reference reads. In
      LAWS.bend:663-664, B.Ask{rs} costs 1 fuel in drive for any rs: List<&2,
      B.Req>.
      • Concrete example: For fasta = ">c\nA\n" (len 5), vcf =
      "#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\n" (len 39), cs = [vcf],
      bound = 324. Under the old laws, a conforming machine could request at
      most 324 reads. Under the draft, a machine whose first step returns B.
      Ask{rs} with 10⁹ copies of B.Req{"c", 0n, 1n}, ignores the answers on
      step 2, and emits the header + summary + B.Finish{0n} finishes at fuel
      step 4 (≤ 324), satisfying machine while forcing the driver to execute
      10⁹ pread calls.
      • Fix: Add reqs: Nat to DSt, increment it by List.length(&2, B.Req, rs)
      in the B.Ask{rs} arm of dstep, and require Nat.is_le(reqs, bound(fasta,
      vcf, cs)) in launch (preserving structural recursion on fuel in drive).
      Any batched machine doing ≤ len(fasta) + 3 reads per line still
      satisfies both steps <= bound and reqs <= bound.
  2. **Science and implementation layers still share LAWS.bend and
  types.bend** — should fix
      • Problem: LAWS.bend:4 still has import ./norm.bend as Norm and
      machine/usage, and types.bend:616-620 still holds Ans, Req, In, and
      Next. Thus the "mentions no code" rule is enforced only by comment,
      every edit to norm.bend forces Bend to re-elaborate LAWS.bend and re-
      check science proofs importing it, and any future protocol change
      touches the expert-approved files.
      • Concrete example: Replacing Chunk{s: String} with raw byte slices
      Chunk{bs: List<&2, U32>} (to avoid the ~4 s Char-list
      conversion/splitting floor noted in NOTES.md:248-252) or changing Norm.
      ￺St requires editing/re-checking types.bend and LAWS.bend.
       • Fix: Keep LAWS.bend (lines 1–604, without import ./norm.bend) and
       types.bend (without Ans/Req/In/Next) strictly code-free, and move lines
       606–746 plus Ans/Req/In/Next into MACHINE.bend (importing ./LAWS.bend
       and ./norm.bend).
  3. Implicit precondition that judge calls Tan.normal only on valid variants
  — minor
      • Problem: Every variant law assumes valid(seq, v) == True{}, while
      Tan.normal has an unconstrained fallback Maybe.default(..., v) via
      windowed var_in. To treat tan.bend as a black box, a reviewer must
      manually trace Rec.malformed, Allele.read, Alleles.read, and checks to
      see that problem never calls Tan.normal with valid(seq, v) == False{}.
      • Concrete example: checks does not check len(ref) >= 1 or
      all_nonempty(alts), relying on Rec.malformed(fs) == False{} upstream;
      if a hypothetical edit broke that upstream guard, Tan.normal(seq, B.
      ￺Var{1n, Nil{}, Nil{}}) would not be constrained by same_change–shortest.
       • Fix: Add a bridge law in the science layer stating that for any fs
       with Rec.malformed(fs) == False{}, if Allele.read/Alleles.read yield
       Some{ref}/Some{alts} and checks(end_ok, seq, v) == None{}, then
       valid(seq, v) == True{} (and optionally move var_in/Win.get back to
       code, since one_form + normal_unchanged already let any implementation
       normalizer prove equality with Tan.normal).
  4. **Dead NoAns{} constructor in Ans** — minor
      • Problem: NoAns{} ("nothing was read (the line needs no reference)")
      is a leftover from the removed Norm.judge_in window laws; truth.of
      produces only Unknown{} or Known{...}, so Ref{ans} in the protocol
      never carries NoAns{}.
      • Fix: Remove NoAns{} from Ans (an implementation that wants an
      "unread" state internally can use Maybe<&2, B.Ans>).
  5. Working-tree drift in run.bend and LAWS.bend comments — minor
      • Problem: draft/ was branched from HEAD, so: (i) run.bend:103-124
      (omitted from draft2.diff) still has the eager take_ready/drop_ready
      rather than the working-tree lazy take_ready.go/drop_ready.go used by
      proof_run_sort.bend, and its header comment (line 9) still mentions
      Norm.judge_in; (ii) LAWS.bend:166 retains 13 R.has/R.added/R.stop
      search-and-replace typos in English comments (e.g. line 719: when the .
      ￺fai R.has no such contig) that were already fixed in working-tree
       LAWS.bend.
       • Fix: Keep working-tree run.bend (updating its line 9 comment to drop
       Norm.judge_in) and carry over the comment typo fixes in LAWS.bend.


