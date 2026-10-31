Law review of one change to a proposed feature of framebender (read-only: do not modify, create
or delete files in the repository, and do not switch branches).

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws, and whose program is
proven to obey them. The laws are meant to be approved by geneticists who do not read code, so
each law needs a plain statement that is true and complete. `docs/LAWS.md` explains them.

Phase I adds splitting of multiallelic records (`-m -any`, as `bcftools norm -m -any`). Its laws
passed review (`reviews/*-split-law*.md` and `reviews/responses-split-law.md` in
/home/luisc/Work/bend-projects/framebender). While proving law `machine` (MACHINE.bend) under
`-m`, the author found that the proof's per-line read allowance does not cover a split line's
records, and proposes to enlarge the step and read bound (`bound` in MACHINE.bend) with `-m`
only, by (VCF length + 1)^2. The owner consents to enlarging it; this review checks the
wording and the arithmetic.

The change, its reason, the arithmetic of the fit and the alternative are in the section
"Law change: the step bound with -m" at the top of `notes/split.md` in the worktree
/home/luisc/Work/bend-projects/framebender-split (branch `split`, uncommitted work in progress;
MACHINE.bend there has the current bound and its comment; the budget proofs are
`proof_b_budget_*`, `proof_b_bud_*`, `proof_e_bud_*`).

Questions:
1. Is the fit argument right: does (VCF length + 1)^2 cover charging each split record a full
   line's allowance (LA = 2 RW + 2 ZW), plus the extra output steps, for every input? Check the
   inequalities (the field count, the record size bound, sum of L^2 <= V^2), including lines
   without LF, CRLF, `*` and symbolic ALTs, a line split under `-c w` that passes through, and
   pieces that cut a line.
2. Is `splits(argv)` right: does it agree with when the machine actually splits (every spelling
   of `-m` the parser accepts, repeated options, `-m` with a usage error)? Is it better to state the
   extra term without `-m`'s condition (always), and why?
3. Is the comment's new sentence true and plain, and is it right that the plain statement in
   docs/LAWS.md need not change? Does the change weaken anything beyond the bound under `-m`
   (output, messages, exit codes, runs without `-m` must be untouched)?
4. Is there a smaller term that fits as simply (a constant factor, a per-line maximum)?

Use only the repository's files. You may run `bend` checks on copies under `/tmp` only.

Report a numbered list: severity (blocker / should fix / minor), the exact place, why, and the
fix. Or say ACCEPT. Be brief. End with the full report as your final message.
