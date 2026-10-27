# Claude, draft-2 review

● I agree with the restructuring. None of the issues below blocks the draft from
  pinning down the same observable behaviour. Items 1 and 2 should be fixed
  before approval, because each one undermines the stated goal of letting the
  code change without touching the approved laws. I only read files; I didn't
  run Bend on the draft.

  (a) Same observable behaviour? Yes, for everything the laws cover.
  - judge only ever hands Tan.normal a valid variant. MALFORMED rules out an
    empty REF or ALT, out-of-scope rules out non-letter ALTs, and BAD_POS,
    ALT_DUP and REF_MISMATCH rule out the rest.
  - On valid variants the current laws already force Norm.var to be the one
    normalized form: normal_unchanged plus one_form give uniqueness. So Norm.var
    and Tan.normal agree wherever run uses them.
  - window and window_enough only constrained the code's internals.

  The one user-visible difference sits outside the laws, at the trust boundary.
  That is item 2.

  (b) Is the science layer reviewable? Tan.normal is an acceptable reference:
  because of the uniqueness above, an expert doesn't even need to read its code.
  Items 3 and 4 are about making that obvious to them.

  (c) Is the protocol sound? Logically, yes. The answers are truths in order,
  defined entirely by the spec, and an empty Ask{Nil} costs one step and is
  harmless. Items 2 and 5 are the soft spots.

  Findings

  1. Should fix (arguably a blocker for the goal): the code calls spec
     definitions directly, so optimizing the code means editing approved files.
     - norm.bend:90,109 calls R.body_line and R.head_line; norm_line.bend:58
       calls B.Rec.rebuild and B.Rec.stale.
     - This is already happening: commit 0810b08 changed Rec.stale purely for
       speed. The uncommitted run.bend change (lazy take_ready) is the same kind
       of edit. draft/run.bend is the HEAD version, so it is already out of
       date.
     - Fix: freeze the spec definitions, give the implementation its own copies,
       and prove them equal inside the machine proof.
  2. Should fix: when "unsupported FASTA" fires depends on which reads the code
     makes.
     - Example: chr2 has a tab in a sequence line and the VCF only has chr1
       records. Today's code exits 0. A version that prefetches or caches whole
       contigs exits 2. Both satisfy the draft (and the current laws), and the
       draft explicitly invites this kind of read freedom.
     - Fix: make the outcome depend only on the files. Either the driver rejects
       any FASTA with a blank in a sequence line at startup, or run itself
       specifies that error so it becomes part of the laws.
  3. Should fix: tan.bend still carries implementation leftovers.
     - Window machinery: Win.get, off, ANeed, var_in.
     - A fuel cut-off, and Maybe.default(…, v), a silent fallback to the input
       variant.
     - An expert would have to trust the proofs that neither is ever reached.
       The draft's own header says the science layer mentions no code.
     - Fix: write normal directly over seq with no window and no Maybe. Move
       var_in into the implementation, with a lemma that var_in(off, w, v) ==
       Some{x} implies x == Tan.normal(seq, v).
  4. Minor: state the two facts that make Tan.normal not need reviewing.
     - Add a law unique: two valid, normalized variants that make the same
       change are equal. It mentions no algorithm.
     - Add a law (or at least a comment) that a Normalized outcome implies the
       input variant is valid.
     - With both stated, the expert approves valid, haps and normalized, and
       Tan.normal is then forced. twice and shortest become corollaries.
  5. Should fix: the step bound no longer limits how much reference the program
     reads.
     - Termination still holds, since each list is finite. But one Ask can now
       carry any number of reads, so the bound limits steps, not reads.
     - The comment "a line may read the reference at most FASTA length + 3 times
       … (it doubles its windows)" is now stale and also describes the code.
     - Fix: charge one fuel per Req in drive, or bound total reads, and drop the
       remark about the code.
  6. Minor: the layer split exists in comments but not in files.
     - The protocol types (In, Next, Req) live in types.bend, and DSt, bound and
       machine live in LAWS.bend next to the science.
     - Evidence: this very draft had to edit types.bend, a science file, to
       change the protocol.
     - Fix: move the protocol and machine into their own file (e.g.
       MACHINE.bend) so the science files don't import Norm at all.
  7. Minor/process: the draft laws aren't proven yet, and main.bend needs
     changes.
     - The variant proofs should carry over mechanically: tan.bend matches
       norm_var.bend except for the rename and comments.
     - The machine proof has to be redone for the new protocol, with the window
       laws turned into lemmas.
     - main.bend must now answer a list of reads in order. That grows the
       trusted code, so it needs a careful look.
     - Approve the statements on condition that bend --verdict passes on the
       final files.

