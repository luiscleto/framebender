Round 6: review of the rewritten laws (read-only: do not modify, create or delete any files).

The drafter has rewritten `LAWS.bend` and `types.bend` to implement the plan all three reviewers agreed
to in `reviews/responses-1.md` .. `reviews/responses-4.md` (later responses amend earlier ones).
`norm.bend` is the code (judge the laws, not the code; `Norm.step` is still a stub).
`examples.bend` has concrete cases that the checker evaluates; they all pass.
Sources as before: `refs/VCFv4.3.txt`, `refs/tan2015.txt`, `refs/bcftools-norm.txt`. Bend notes are in
`refs/REVIEW_PROMPT.md`; in addition, `Bool.pick(T, c, a, b)` is "if c then a else b", and a law's
`for h: {x == y : T}` lines are hypotheses.

Check:
(a) Does each definition and law say what its comment says, and does it implement the agreed plan
    (classification order, END, canonical text, ordering and flush rule, step order per line,
    line endings, FASTA parsing, header lines, messages and exit codes, windows per outcome,
    multiallelic definitions, the machine law and its trust boundary)?
(b) Is any law false (no implementation could satisfy it), or too weak (a wrong implementation
    could satisfy every law)? Give a concrete counterexample.
(c) Anything the plan agreed on that is missing.

Report a numbered list: the definition or law, severity (blocker / should fix / minor), the problem,
a concrete example, and the fix. Do not repeat points already settled in responses-1..4 unless the
rewrite gets them wrong. Be brief. Give the answer as your final answer.
