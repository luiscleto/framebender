# Brief: the sequential budget under -m (fb-budget)

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws and proven
(`docs/LAWS.md`). Phase I (`-m -any`) is on branch `split`; fb-split has proven everything except
the budget: law `machine` (MACHINE.bend) says the program finishes within `bound` steps and reads,
and with `-m` the bound gained a `(V+1)^2` term (`split_room`), reviewed and accepted as decisions
29-36 at the end of `reviews/responses-split-law.md`. The fit is argued in `notes/split.md`,
section "Law change: the step bound with -m".

**Your part:** the sequential budget, the holes in `proof_b_budget_*`, `proof_b_bud_*` and
`proof_c_bud*`, on branch `split-budget` from `split` (ff067f4). fb-split does the threads
machine's budget (`proof_e_bud_*`, `proof_e_mach_*`, `proof_e_wrap*`, `proof_e_qif*`, the simdefs,
adv and drive files) at the same time, in the `split` worktree.

**Frozen, shared with fb-split:** `bound` and `split_room` in MACHINE.bend, and the statements in
`proof_b_budget_api.bend`. Do not change them; if you need to, stop and report instead. No law,
plain statement or spec file changes (`LAWS.bend`, `MACHINE.bend`, `types.bend`, `run.bend`,
`tan.bend`, `docs/`), and no program change (`norm*.bend`).

**The plan (decisions 31 and 34):** charge 1 + k allowances per candidate line (`-m`, not
malformed, two or more ALTs, split or not); prove that a split record's text is no longer than its
line's (`Rec.piece` keeps the fields, takes one ALT, keeps a subset of INFO and FORMAT values,
recodes GT with no more digits); use `out_len`'s constants for the output; then `bud_need` and
`start_need` meet the corrected fit. Charge against the current splitter (it was just made faster:
`split-speed`, merged at ff067f4), not the old one. fb-split's progress notes are in
`data/tmp/split/proof_progress.md`; keep your own in `data/tmp/split/budget_progress.md`.

**How to work.** `BEND_NO_TELEMETRY=1`; proof checks only through `test/bcheck.sh` (two at a time
machine-wide, shared with fb-split); scratch in `data/tmp/split/budget/`; `rm` only with literal
paths. Commit on `split-budget` as you go; don't push, don't merge, don't touch `split`. Back up
before large rewrites.

**Report** (final message): the holes closed and left, any statement you had to add (new lemmas
are fine; changed shared statements are not), the files changed, and the commits.
