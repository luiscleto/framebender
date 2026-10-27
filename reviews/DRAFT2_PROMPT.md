Review of a restructuring of the framebender specification (read-only: do not modify, create or
delete any files).

framebender is a VCF normalizer (`framebender norm -f ref.fa in.vcf > out.vcf`) written in Bend 2.
Its laws (`LAWS.bend`, with `types.bend` and `run.bend`) were reviewed by three independent
reviewers over eight rounds (`reviews/responses-1.md` .. `responses-5.md` hold the agreed decisions)
and are all proven. The project owner now wants the laws split into two layers, so that experts
review and approve the science once and the implementation can then be changed and optimized
freely (batches, parallel threads, caches) without touching the approved laws:

- Science layer: definitions and laws that mention no code.
- Implementation layer: one law (`machine`, plus `usage`): the program writes exactly what the
  whole-file definition `run` says.

The draft is in `draft/` (`draft/LAWS.bend`, `draft/types.bend`, `draft/tan.bend`, `draft/run.bend`;
`draft/norm.bend` is a stub of the code interface so that the draft type-checks). The full diff
against the current approved files is `reviews/draft2.diff`. In short:
1. The variant laws (`same_change`, `stays_valid`, `standard_form`, `normal_unchanged`, `twice`,
   `one_form`, `shortest`) are stated about a reference normalizer `Tan.normal` in the spec
   (`draft/tan.bend`, Tan et al.'s Algorithm 1, the same algorithm as the current code) instead of
   about the code's `Norm.var`. `judge`, and so `run`, use `Tan.normal`.
2. The two window laws (`window`, `window_enough`), which were about the code's `Norm.judge_in`,
   are removed as laws; they remain lemmas inside the current implementation's proof.
3. The machine protocol is generalized: an `Ask` carries a list of reference reads (`B.Req`) and
   the next input gives all their truthful answers in order (`B.Ref{ans}`), so an implementation can
   batch reads. Everything else in the `machine` law (pieces of the VCF in any split, end of file
   once, the step bound, exact stdout/stderr/exit equality with `run`, the trust boundary) is
   unchanged.

Sources as before: `refs/VCFv4.3.txt`, `refs/tan2015.txt`, `refs/bcftools-norm.txt`. Bend notes:
`refs/REVIEW_PROMPT.md`.

Answer:
(a) Does the restructured set still pin down the tool's observable behaviour exactly as before
    (could any program satisfy the draft's laws but not the current ones, in a way a user would
    notice)? Concrete counterexample if so.
(b) Is the science layer complete and reviewable by a bioinformatics expert: is anything that an
    expert would want stated missing, or stated in a way that would be hard to check? Is
    `Tan.normal` an acceptable reference definition, given that the laws prove its result is the
    unique left-aligned, parsimonious representation?
(c) Is the generalized protocol sound (the trust boundary, the step bound with batched reads)?
(d) Anything else that blocks approval.
Report a numbered list (blocker / should fix / minor, concrete example, fix). If you agree with the
restructuring, say so. Be brief. Give the answer as your final answer.
