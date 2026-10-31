Law review of one change to a proposed feature of framebender (read-only: do not modify, create
or delete files in the repository, and do not switch branches).

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws, and whose program is
proven to obey them. The laws are meant to be approved by geneticists who do not read code, so
each law needs a plain statement that is true and complete. `docs/LAWS.md` explains them.

Phase I adds splitting of multiallelic records (`-m -any`, as `bcftools norm -m -any`). Its laws
passed three review rounds (`reviews/*-split-law*.md` and `reviews/responses-split-law.md` in
/home/luisc/Work/bend-projects/framebender). While proving them, the author found that the
approved law `twice_run` (running framebender on its own output changes nothing) is false under
`-m`: a stray carriage return inside a comma list (`END=5\r,6`) can end a split record in a bare
CR, which reads back as a CRLF line ending, so the second run sees a different line. The lead
chose to keep `twice_run` whole and change the split rule instead.

The change, its counterexample, bcftools 1.24's behaviour on the same files and the narrower
alternatives are in the section "Law change: CR" at the top of `notes/split.md` in the worktree
/home/luisc/Work/bend-projects/framebender-split (branch `split`). The drafted spec is in
`data/tmp/split/draft_cr/` (it type-checks; examples in `ex_cr.bend`), the counterexample in
`data/tmp/split/cr/`.

Questions:
1. Does the change make `twice_run` true again under `-m`, for every input? Is there another way
   a split record can read back differently (other control bytes, a NUL, a lone `\r` at the end of
   the last field without CR elsewhere, an empty value, a tab inside a value)?
2. Is the new refusal (`BAD_CR`) stated plainly and correctly in `split_when`, `split_problem`,
   `B.Rec.parts`, the plain statement and the differences table? Its order relative to the other
   split refusals and to decision 7 (a whole-line outcome that stops the run comes first)?
3. Is any other approved law weakened (it must not be), and do the laws without `-m`
   (`items_without_m`, `biallelic_run`) still hold?
4. The simple rule (any CR in the body of a line to split) against the narrower ones: which would
   you choose?

Use only the repository's files and `data/tmp/split/`. You may run `bend` checks and `bcftools`
on copies under `/tmp` only.

Report a numbered list: severity (blocker / should fix / minor), the exact place, why, and the
fix. Or say ACCEPT. Be brief. End with the full report as your final message.
