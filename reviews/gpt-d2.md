# GPT, draft-2 review

• I agree with the restructuring. I found no blocker or user-visible
  counterexample within the agreed trusted-driver boundary. machine still fixes
  paths, stdout, stderr and exit status; removing requirements on internal
  helpers does not weaken those guarantees.

  The science layer covers the agreed scope. Tan.normal is an acceptable
  reference definition: preservation, validity, normality, uniqueness and
  shortestness constrain its result independently of the implementation.

  The batched protocol is sound: truths supplies exactly one truthful answer per
  request, in order; EOF remains single-delivery; empty batches cannot evade the
  termination bound.

  1. Minor — step-bound documentation. draft/LAWS.bend:685 (draft/LAWS.bend:685)
     still explains the bound in terms of individual reference reads. One Ask
     containing 10,000 requests consumes one driver transition. Fix: describe
     the bound as counting driver transitions, including reference-answer
     batches. It does not bound total reads, bytes fetched or elapsed time.

  2. Minor — the supplied diff is incomplete. reviews/draft2.diff omits an
     actual difference between run.bend and draft/run.bend:95 (draft/
     run.bend:95): the draft uses recursive take_ready.put/drop_ready.put,
     whereas the current file uses helpers that stop traversing at the first
     unready item. These produce the same results on finite buffers, so this
     adds no observable discrepancy, but contradicts the claimed complete diff.
     Fix: regenerate the diff against a fixed baseline and include this
     difference or synchronize the draft copy.

